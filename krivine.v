(* -------------------------------------------------------------------- *)
Require Import ssreflect eqtype ssrbool ssrnat ssrfun seq.
Require Import Relation_Operators.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Lemma pairE (T U : Type) (xy : T * U): (xy.1, xy.2) = xy.
Proof. by case: xy. Qed.

(* -------------------------------------------------------------------- *)
Reserved Notation "# x"         (at level 8, format "# x").
Reserved Notation "^ x"         (at level 8, format "^ x").
Reserved Notation "t · u"       (at level 40, left associativity, format "t  ·  u").
Reserved Notation "'λ' [ t ]"   (at level 30, t at level 15, right associativity, format "'λ'  [ t ]").
Reserved Notation "'ξ' [ c ] t" (at level 30, c, t at level 15, right associativity, format "'ξ'  [ c ]  t").

Reserved Notation "^ x"         (at level 8, format "^ x").
Reserved Notation "⌊ x ⌋"       (at level 7, format "⌊ x ⌋").
Reserved Notation "t ○ u"       (at level 40, left associativity, format "t  ○  u").
Reserved Notation "'λλ' [ t ]"  (at level 30, t at level 15, right associativity, format "'λλ'  [ t ]").
Reserved Notation "'ξ' [ c ] t" (at level 30, c, t at level 15, right associativity, format "'ξ'  [ c ]  t").

Inductive term : Type :=
| Var of nat
| App of term & term
| Lam of term.

Notation "# x"       := (Var x)   : lambda.
Notation "t · u"     := (App t u) : lambda.
Notation "'λ' [ t ]" := (Lam t)   : lambda.

Bind Scope lambda with term.
Delimit Scope lambda with L.

Local Open Scope lambda.

Implicit Types x i     : nat.
Implicit Types n m     : nat.
Implicit Types t u v w : term.

Scheme Equality for term.

Lemma term_eqP t1 t2: reflect (t1 = t2) (term_beq t1 t2).
Proof.
  apply: (iffP idP).
  + by move/internal_term_dec_bl.
  + by move/internal_term_dec_lb.
Qed.

Definition term_eqMixin := EqMixin term_eqP.
Canonical term_eqType := EqType term term_eqMixin.

(* -------------------------------------------------------------------- *)
Reserved Notation "t ·! u" (at level 16, left associativity, format "t  ·!  u").

Definition AppS t := foldl App t.

Notation "t ·! u" := (AppS t u).

Lemma AppS_cons t u us: t ·! (u :: us) = (t · u) ·! us.
Proof. by []. Qed.


Lemma AppS_rcons t u us: t ·! (rcons us u) = (t ·! us) · u.
Proof. by rewrite -cats1 /AppS foldl_cat. Qed.

(* -------------------------------------------------------------------- *)
Fixpoint curry (t : term) :=
  match t with
  | u1 · u2 => let (a, h) := curry u1 in (a, rcons h u2)
  | _       => (t, [::])
  end.

Definition isapp (t : term) := if t is _ · _ then true else false.

Lemma curryE (t : term): (curry t).1 ·! (curry t).2 = t.
Proof.
  elim: t => //= t IH u _; case: (curry t) IH => a h /= IH.
  by rewrite AppS_rcons IH.
Qed.

Lemma crNapp (t : term): ~~(isapp (curry t).1).
Proof.
  by elim: t => [x|t IHt u _|t IH] => //=; case: (curry t) IHt.
Qed.

Lemma crcr t us: ~~(isapp t) -> curry (t ·! us) = (t, us).
Proof.
  elim/last_ind: us => [|us u IH]; first by case: t.
  by move=> Napp_t; rewrite AppS_rcons /= IH.
Qed.

Lemma crK t: curry ((curry t).1 ·! (curry t).2) = curry t.
Proof. by rewrite crcr ?crNapp //; case: (curry t). Qed.

(* -------------------------------------------------------------------- *)
Reserved Notation "↑ t"           (at level 0, format "↑ t").
Reserved Notation "↑ [ k ] t"     (at level 0, format "↑ [ k ] t").
Reserved Notation "↑ [ k , n ] t" (at level 0, format "↑ [ k , n ] t").

Fixpoint lift k n t :=
  match t with
  | #x      => if x >= k then #(x+n) else #x
  | t1 · t2 => ↑[k,n] t1 · ↑[k,n] t2
  | λ [t]   => λ [↑[k.+1,n] t]
  end
    where "↑ [ k , n ] t" := (lift k n t).

Notation "↑ [ k ] t" := (↑[k,1] t).
Notation "↑ t"       := (↑[0] t).

(* -------------------------------------------------------------------- *)
Lemma liftn0 t k: ↑[k,0] t = t.
Proof.
  elim: t k => /= [n|t IHt u IHu|t IH] k.
  + by rewrite addn0; case: leqP.
  + by rewrite !(IHt, IHu).
  + by rewrite IH.
Qed.

(* -------------------------------------------------------------------- *)
Reserved Notation "t [! x ← u ]" (at level 8, x, u at level 15, format "t [! x  ←  u ]").

Delimit Scope I with I.

Fixpoint subst k w t :=
  match t with
  | #x =>
           if x <  k then t
      else if x == k then ↑[0,k] w
      else #x.-1

  | t1 · t2 => t1[!k ← w] · t2[!k ← w]
  | λ [t]   => λ [t[!k.+1 ← w]]
  end
    where "t [! x ← u ]" := (subst x u t).

(* -------------------------------------------------------------------- *)
Inductive closure : Type :=
| CClo  of term & seq closure
| CGrd  of nat
| CLvl  of nat
| CApp  of closure & closure
| CLam  of closure.

Implicit Types c : closure.
Implicit Types cs : seq closure.

Notation "'ξ' [ c ] t" := (CClo t c)   : closure.
Notation "^ x"         := (CLvl x)     : closure.
Notation "⌊ x ⌋"       := (CGrd x)     : closure.
Notation "c1 ○ c2"     := (CApp c1 c2) : closure.
Notation "'λλ' [ c ]"  := (CLam c)     : closure.

Bind Scope closure with closure.
Delimit Scope closure with C.

Local Open Scope closure.

Fixpoint closure_eqb (c1 c2 : closure) {struct c1} :=
  match c1, c2 with
  | ^n     , ^m        => n == m
  | ⌊n⌋    , ⌊m⌋       => n == m
  | c1 ○ c2, c'1 ○ c'2 => [&& closure_eqb c1 c'1 & closure_eqb c2 c'2]
  | λλ [c] , λλ [c']   => closure_eqb c c'
  | ξ [c] t, ξ [c'] t' =>
      let fix cseq cs1 cs2 :=
          match cs1, cs2 with
          | [::]     , [::]      => true
          | c1 :: cs1, c2 :: cs2 => [&& closure_eqb c1 c2 & cseq cs1 cs2]
          | _        , _         => false
          end
      in
        [&& cseq c c' & t == t']
  | _      , _         => false
  end.

Lemma closure_eqP c1 c2: reflect (c1 = c2) (closure_eqb c1 c2).
Proof.
  apply: (iffP idP).
  + move: c1 c2; fix 1; move: closure_eqP => IH.
    case=> [t cs|n|n|c1 c2|c] [t' cs'|n'|n'|c1' c2'|c'] //=;
      try solve [ by move/eqP=> ->
                | by do! (try (try case/andP; move/IH=> ->))].
    * case/andP=> h /eqP->; elim: cs cs' h => [|c cs IHcs] [|c' cs'] //=.
      by case/andP=> /IH-> /IHcs; case=> ->.
  + move: c1 c2; fix 1; move: closure_eqP => IH.
    case=> [t cs|n|n|c1 c2|c] [t' cs'|n'|n'|c1' c2'|c'] //=;
      try by (case; do? (try move/IH)=> ->//).
    * case=> <- eq_cs; apply/andP; split=> //.
      elim: cs cs' eq_cs => [|c cs IHcs] [|c' cs'] //=.
      by case=> /IH-> /IHcs->.
Qed.

Section ClosureInd.
  Definition closure_eqMixin := EqMixin closure_eqP.
  Canonical closure_eqType := EqType closure closure_eqMixin.

  Variable P : closure -> Prop.

  Hypothesis Hclo : forall t cs, (forall c, c \in cs -> P c) -> P (ξ [cs] t).
  Hypothesis Hlvl : forall n, P ^n.
  Hypothesis Hgrd : forall n, P ⌊n⌋.
  Hypothesis Happ : forall c1 c2, P c1 -> P c2 -> P (c1 ○ c2).
  Hypothesis Hlam : forall c, P c -> P (λλ [c]).

  Lemma clind c : P c.
  Proof.
    move: c; fix 1; case => [t cs|n|n|c1 c2|c].
    + apply: Hclo; elim: cs => [|c' cs IH] c.
      * by rewrite in_nil => {clind}.
      * rewrite in_cons; case/orP => [/eqP->|].
        by apply: clind. by move/IH => {clind}.
    + by apply: Hgrd.
    + by apply: Hlvl.
    + by apply: Happ; apply: clind.
    + by apply: Hlam; apply: clind.
  Qed.
End ClosureInd.

Fixpoint is_ephemeral c :=
  match c with
  | ⌊_⌋     => true
  | λλ [c]  => is_ephemeral c
  | c1 ○ c2 => [&& is_ephemeral c1 & is_ephemeral c2]
  | _       => false
  end.

(* -------------------------------------------------------------------- *)
Reserved Notation "c ○! cs" (at level 16, left associativity, format "c  ○!  cs").

Definition CAppS c := foldl CApp c.

Notation "c ○! cs" := (CAppS c cs).

(* -------------------------------------------------------------------- *)
Fixpoint closure_of_term (t : term) : closure :=
  match t with
  | #n      => ⌊n⌋
  | λ [t]   => λλ [closure_of_term t]
  | t1 · t2 => closure_of_term t1 ○ closure_of_term t2
  end.

Fixpoint term_of_closure (w : term) (c : closure) : term :=
  match c with
  | ⌊n⌋     => #n
  | λλ [c]  => λ [term_of_closure w c]
  | c1 ○ c2 => term_of_closure w c1 · term_of_closure w c2
  | _       => w
  end.

(* -------------------------------------------------------------------- *)
Lemma closure_of_termK w: cancel closure_of_term (term_of_closure w).
Proof. by elim=> /= [n|t -> u ->|t ->]. Qed.

Lemma term_of_closureK w:
  {in is_ephemeral, cancel (term_of_closure w) closure_of_term}.
Proof.
  elim=> /= [t cs|n|n|c1 IH1 c2 IH2|c IH] //=; rewrite /in_mem /=.
  + by case/andP=> Ec1 Ec2; rewrite !(IH1, IH2).
  + by move=> Ec; rewrite IH.
Qed.

(* -------------------------------------------------------------------- *)
Inductive ephemeral : Type := Ephemeral c of is_ephemeral c.

Coercion closure_of_ephemeral e := let: Ephemeral c _ := e in c.

Canonical Structure ephemeral_subType :=
  [subType for closure_of_ephemeral by ephemeral_rect].

Definition ephemeral_eqMixin := [eqMixin of ephemeral by <:].
Canonical Structure ephemeral_eqType := Eval hnf in EqType ephemeral ephemeral_eqMixin.

(* -------------------------------------------------------------------- *)
Lemma is_ephemeral_t2c (t : term): is_ephemeral (closure_of_term t).
Proof. by elim: t => /= [n|t -> u ->|t ->]. Qed.

Definition ephemeral_of_term (t : term) :=
  @Ephemeral (closure_of_term t) (is_ephemeral_t2c t).

Definition term_of_ephemeral (e : ephemeral) :=
  term_of_closure #0 e.

Lemma ephemeral_of_termK: cancel ephemeral_of_term term_of_ephemeral.
Proof. by move=> t; rewrite /term_of_ephemeral closure_of_termK. Qed.

Lemma term_of_ephemeralK: cancel term_of_ephemeral ephemeral_of_term.
Proof.
  case=> t Et; rewrite /ephemeral_of_term; apply/eqP.
  by rewrite eqE /= term_of_closureK.
Qed.

(* -------------------------------------------------------------------- *)
Module SCI.
  Fixpoint sc (c : closure) (l : nat) : closure :=
    match c with
    | ⌊_⌋      => c
    | ^n       => ⌊l-n⌋
    | λλ [c]   => λλ [sc c l.+1]
    | c1 ○ c2  => sc c1 l ○ sc c2 l
    | ξ [cs] t =>
        let fix sct t l ls : closure :=
          match t with
          | #n      => if   n < size ls
                       then ⌊l - nth 0 ls n⌋
                       else if   n < size ls + size cs
                            then nth ⌊0⌋ [seq sc c l | c <- cs] (n - size ls)
                            else ⌊n + l - (size ls + size cs)⌋
          | λ [t]   => λλ [sct t l.+1 (l.+1 :: ls)]
          | t1 · t2 => (sct t1 l ls ○ sct t2 l ls)
          end
        in
          sct t l [::]
    end.
End SCI.

(* -------------------------------------------------------------------- *)
Module Type SCSig.
  Parameter sc  : closure -> nat -> closure.
  Parameter scE : sc = SCI.sc.
End SCSig.

Module SC : SCSig.
  Definition sc := SCI.sc.

  Lemma scE : sc = SCI.sc.
  Proof. by []. Qed.
End SC.

Notation  sc := SC.sc.
Canonical sc_unlock := Unlockable SC.scE.

(* -------------------------------------------------------------------- *)
Fixpoint sct cs t l : closure :=
  match t with
  | #n      => if   n < size cs
               then sc (nth ⌊0⌋ cs n) l
               else ⌊n + l - size cs⌋
  | λ [t]   => λλ [sct (^l.+1 :: cs) t l.+1]
  | t1 · t2 => sct cs t1 l ○ sct cs t2 l
  end.

(* -------------------------------------------------------------------- *)
Section SecE.
  Local Open Scope closure.

  Lemma scCE cs t l: sc (ξ [cs] t) l = sct cs t l.
  Proof.
    rewrite unlock /=; apply/esym.
    have {1}->: cs = (map CGrd [::]) ++ cs by [].
    set ls := [::]; set hs := _ ++ _.
    have e: hs = [seq ^x | x <- ls] ++ cs by [].
    elim: t l ls hs e => [n|t1 IH1 t2 IH2|t IH] /= l ls hs e.
    + rewrite e size_cat size_map; case: (ltnP _ (_ + _)); last first.
        move=> h; case: ltnP => //= h'.
        move: (leq_ltn_trans h h'); rewrite /leq.
        by rewrite -addnS addnC -addnBA.
      move=> h; case: ltnP=> h'; rewrite nth_cat !size_map.
      + by rewrite h' (nth_map 0) // unlock.
      + rewrite ltnNge h' /= (nth_map ⌊0⌋) 1?unlock //.
        by rewrite -(ltn_add2l (size ls)) subnKC.
    + by rewrite !(IH1 _ ls, IH2 _ ls).
    + by rewrite (IH l.+1 (l.+1::ls)) //= e.
  Qed.

  Lemma scE: forall c l,
    sc c l = match c return closure with
             | ^n               => ⌊l-n⌋
             | ⌊n⌋              => ⌊n⌋
             | λλ [c]           => λλ [sc c l.+1]
             | c1 ○ c2          => (sc c1 l) ○ (sc c2 l)
             | ξ [cs] #n        => if   n < size cs
                                   then sc (nth ⌊0⌋ cs n) l
                                   else ⌊n + l - size cs⌋
             | ξ [cs] (λ [t])   => sc (λλ [ξ [^(l.+1) :: cs] t]) l
             | ξ [cs] (t1 · t2) => sc (ξ [cs] t1 ○ ξ [cs] t2) l
             end.
  Proof.
    case=> [t c|n|n|c1 c2|c] l; try by rewrite unlock.
    case: t => [n|t1 t2|t]; try by rewrite unlock.
    + by rewrite unlock /= add0n subn0; case:ltnP => h //; apply: nth_map.
    + have ->: sc (λλ [ξ[(^l.+1 :: c)] t]) l = λλ [sc (ξ [(^l.+1 :: c)] t) l.+1].
        by rewrite unlock.
      by rewrite !scCE /=.
  Qed.
End SecE.

(* -------------------------------------------------------------------- *)
Lemma sc_is_ephemeral c l: is_ephemeral (sc c l).
Proof.
  elim/clind: c l => [t cs IH|n|n|c1 c2 IH1 IH2|c IH] l;
    try by rewrite scE //=; do? (apply/andP; split).
  rewrite scCE; elim: t cs IH l => [n|t1 IH1 t2 IH2|t IH] cs IHcs l /=.
  + by case: ltnP => // lt_n_szcs; rewrite IHcs // mem_nth.
  + by rewrite !(IH1, IH2).
  + rewrite IH // => c; rewrite in_cons => /orP [/eqP->|/IHcs //].
    by move=> l'; rewrite scE.
Qed.

(* -------------------------------------------------------------------- *)
Definition σc (c : closure) (l : nat) :=
  @Ephemeral (sc c l) (sc_is_ephemeral c l).

(* -------------------------------------------------------------------- *)
Lemma sc_id_eph: forall c l, is_ephemeral c -> sc c l = c.
Proof.
  elim=> [t cs|n|n|c1 IH1 c2 IH2|c IH] l //=; rewrite scE //.
  + by case/andP=> /IH1-> /IH2->.
  + by move/IH=> ->.
Qed.

(* -------------------------------------------------------------------- *)
Lemma scK l c:  sc (sc c l) l = sc c l.
Proof. by rewrite sc_id_eph // sc_is_ephemeral. Qed.

(* -------------------------------------------------------------------- *)
Coercion term_of_closure_r := locked (term_of_closure #(0)).
Coercion term_of_ephemeral : ephemeral >-> term.

(* -------------------------------------------------------------------- *)
Lemma c2tE:
    (forall n, ⌊n⌋ = #n :> term)
  * (forall c, λλ [c] = λ [c] :> term)
  * (forall c1 c2, c1 ○ c2 = c1 · c2 :> term).
Proof. by do! split; rewrite /term_of_closure_r -lock. Qed.

(* -------------------------------------------------------------------- *)
Inductive wfc : nat -> seq closure -> nat -> Prop :=
| WFCEmpty:
    forall n, wfc 0 [::] n

| WFCTerm:
    forall i t ρt ρ n, i <= n
     -> wfc i ρt i
     -> wfc i ρ  n
     -> wfc i (ξ [ρt] t :: ρ) n

| WFCFormal:
    forall i ρ n, i.+1 <= n
     -> wfc i    ρ n
     -> wfc i.+1 (^i.+1 :: ρ) n
.
Derive Inversion_clear WFCCons with
  (forall i c ρ n, wfc i (c :: ρ) n) Sort Prop.

Definition asformal (c : closure) :=
  if c is ^i then Some i else None.

Definition formals (ρ : seq closure) :=
  pmap asformal ρ.

Lemma formals_cat (ρ1 ρ2 : seq closure):
  formals (ρ1 ++ ρ2) = formals ρ1 ++ formals ρ2.
Proof. by elim: ρ1 => [//|c ρ1 /= ->]; case: (asformal c). Qed.

Lemma wfc_le i ρ n: wfc i ρ n -> i <= n.
Proof. by elim. Qed.

Lemma wfc_lesz i ρ n: wfc i ρ n -> i <= size ρ.
Proof. by elim=> //= {i ρ n} i _ _ ρ _ _ _ _ _ ?; rewrite ltnW. Qed.

Lemma wfc_formals i ρ n:
  wfc i ρ n -> formals ρ = rev (iota 1 i).
Proof.
  elim=> //= {i ρ n} i ρ n _ _ ->; rewrite -rev_rcons -cat1s -cats1.
     have ->: [:: 1   ] = (iota 1    1)%N by []; rewrite -iota_add add1n.
  by have ->: [:: i.+1] = (iota i.+1 1)%N by []; rewrite -iota_add addn1.
Qed.

Lemma wfc_hformal i ρ n: wfc i ρ n -> head 0 (formals ρ) = i.
Proof. by elim. Qed.

Lemma wfc_cat i ρ1 ρ2 n: wfc i (ρ1 ++ ρ2) n -> wfc (head 0 (formals ρ2)) ρ2 n.
Proof.
  elim: ρ1 i => /= [|c ρ ih]; last first.
    move=> i h; inversion h using WFCCons.
    * by move=> _ _ _ _ /ih.
    * by move=> j _ /ih.
  elim: ρ2 => /= [|c ρ ih] i; first by move=> _; constructor.
  move=> h; inversion h using WFCCons => /=.
  + by move=> t ρt le_i_n wfρt wfρ; rewrite (wfc_hformal wfρ); constructor.
  + by move=> j lt_j_n wfρ; constructor.
Qed.

Notation wf ρ l := (wfc l ρ l).

Definition μ l m := [seq ^i | i <- rev (iota l.+1 m)].

Lemma μS l m: μ l m.+1 = ^(l+m).+1 :: μ l m.
Proof.
  rewrite /μ -map_cons -rev_rcons -cats1.
  have ->: [:: (l+m).+1] = iota (l+m).+1 1 by [].
  by rewrite -iota_add addn1.
Qed.

Lemma size_μ l m: size (μ l m) = m.
Proof. by rewrite /μ size_map size_rev size_iota. Qed.

Lemma nth_μ c l m k: k < m -> nth c (μ l m) k = ^(l + m - k).
Proof.
  move=> lt_k_m; rewrite /μ (nth_map 0) ?(size_rev, size_iota) //.
  rewrite nth_rev ?size_iota // nth_iota; last first.
    by rewrite /leq -subSn // subSS -subnDA -/(leq _ _) leq_addl.
  by rewrite subnS addSn -addnS prednK ?subn_gt0 // addnBA 1?ltnW //.
Qed.

(* -------------------------------------------------------------------- *)
Lemma mem_wf l ρ c: wf ρ l -> c \in ρ ->
  [\/ exists2 i, c = ^i & i <= l
    | exists T ρ' l', [/\ c = ξ [ρ'] T, wf ρ' l' & l' <= l]].
Proof.
  elim=> //=.
  + move=> i t pt ρ' n le_in wf_pt IHpt wfρ' IHρ'; rewrite inE.
    case/orP; [move/eqP=> -> | by move/IHρ'].
    by right; exists t, pt, i.
  + move=> i ρ' n lt_in wfρ' IHρ'; rewrite inE.
    case/orP; [move/eqP=> -> | by move/IHρ'].
    by left; exists i.+1.
Qed.

(* -------------------------------------------------------------------- *)
Lemma L1_r:
  forall c,
    forall N ρ l0 l k0 k m, c = ξ [ρ] N -> l >= l0 -> wf ρ l0 ->
          σc (ξ [μ (l+k0+m) k ++ ρ] N) (l+k0+k+m)
        = ↑[k+k0,m] (σc (ξ [μ (l+k0) k ++ ρ] N) (l+k0+k)) :> term.
Proof.
  elim/clind=> // t ρ IH N ρ' l0 l k0 k m [_ <-] {t ρ'}.
  elim: N l0 l k0 k m.
  + move=> n l0 l k0 k m le_l0_l wf_ρ_l0 /=.
    rewrite scE [X in ↑[_,_] (_ X)]scE !size_cat !size_μ; case: ltnP.
    * move=> lt_n_kDρ; case: (ltnP n k) => [lt_nk|le_kn].
      + rewrite !nth_cat !size_μ lt_nk !nth_μ // !scE /=.
        rewrite [_+m]addnAC !subKn; try by rewrite ltnW // ltn_addl.
        by rewrite !c2tE /= leqNgt ltn_addr.
      + rewrite !nth_cat !size_μ ltnNge le_kn /=; set c := nth _ _ _.
        have cρ: c \in ρ by rewrite mem_nth // -subSn // leq_subLR.
        case (mem_wf wf_ρ_l0 cρ).
        - case=> i -> le_i_l0; rewrite !scE !c2tE /=.
          have le_i_lt := leq_trans le_i_l0 le_l0_l.
          apply/esym; rewrite {1}[_+k]addnC {1}[l+_]addnC !addnA.
          rewrite -addnBA 1?leq_addr // addnC addnBA; first by rewrite addnC.
          by rewrite -addnA -[i]addn0 leq_add.
        - case=> T [ρ'] [l'] [cE wf_ρ'_l' le_l'_l0]; rewrite cE.
          have le_l'_l := leq_trans le_l'_l0 le_l0_l.
          have /= := IH _ cρ _ _ _ _ (k0+k) 0 m cE le_l'_l wf_ρ'_l'.
          by rewrite !(addn0, add0n, addnA) [k+k0]addnC.
    * move=> le_kDρ_n; set q := n - (k + size ρ).
      have h: forall h, n + h - (k + size ρ) = q + h.
        by move=> h; rewrite addnC -addnBA // addnC.
      by rewrite !{}h !c2tE /= !addnA [k+k0]addnC leq_add2r leq_addl.
  + move=> t IHt u IHu l0 l k0 k m le_l0_l wf_ρ_l0 /=.
    by rewrite 2!scE !c2tE /= (IHt l0) // (IHu l0) // 2!scE c2tE.
  + move=> t IHt l0 l k0 k m le_l0_l wf_ρ_l0 /=.
    rewrite 2!scE [_+m]addnAC -cat_cons -!μS !c2tE /=.
    rewrite -!addnS [_+k.+1]addnAC (IHt l0) //.
    by rewrite 2!scE c2tE /= -cat_cons -μS -addSn -!addnS.
Qed.

(* -------------------------------------------------------------------- *)
Lemma L1 T ρ l m: wf ρ l ->
  σc (ξ [ρ] T) (l + m) = ↑[0,m] (σc (ξ [ρ] T) l) :> term.
Proof.
  move=> wfρl; move: (@L1_r (ξ [ρ] T) T ρ l l 0 0 m).
  by rewrite !(addn0, add0n) /= => ->.
Qed.

(* -------------------------------------------------------------------- *)
Lemma L2:
  forall c,
    (forall T ρ S l l0 m k, c = ξ [ρ] T -> l >= l0 -> wf ρ l0 ->
         σc (ξ [μ (l+m) k ++ ρ] T) (l+m+k)
       = (σc (ξ [μ (l+m+1) k ++ ρ] T) (l+m+k+1))[! m+k ← S] :> term).
Proof.
  elim/clind=> // t ρ IH T ρ' S l l0 m k [_ <-] {t ρ'}; elim: T l l0 m k.
  + move=> n l l0 m k le_l0_l wf_ρ_l0 /=; rewrite ![sc (ξ [_] _) _]scE.
    rewrite !size_cat !size_μ; case: ltnP=> [lt_n_kDρ|].
    * rewrite !nth_cat !size_μ; case: ltnP => [lt_nk|le_kn].
      - rewrite !nth_μ // !scE !c2tE /= [_+1]addnAC.
        by rewrite !subKn ?ltn_addl // ltnW // ltn_addl.
      - set c := nth _ _ _; have cρ: c \in ρ.
          by rewrite mem_nth // -subSn // leq_subLR.
        case: (mem_wf wf_ρ_l0 cρ).
        + case=> i -> le_i_l0; rewrite !scE !c2tE /=.
          have {-4}->: l+m+k+1 - i = m+k + (l-i).+1.
            have le_i_l := leq_trans le_i_l0 le_l0_l.
            rewrite addn1 -!addSn [_+m]addnC [_+k]addnAC.
            by rewrite -addnBA ?subSn // ltnW.
          rewrite -ltn_subRL subnn /= -[X in _==X]addn0.
          rewrite eqn_add2l /= addn1 subSn //.
          by rewrite (@leq_trans l0) // -[l0]addn0 -addnA leq_add.
        + case=> [T] [ρ'] [l'] [cE wf_ρ'_l' le_l'_l0].
          have le_l'_l := leq_trans le_l'_l0 le_l0_l.
          have /= := (IH _ cρ _ _ S _ _ (m+k) 0 cE le_l'_l wf_ρ'_l').
          by rewrite -cE !(addn0, add0n) !addnA.
    * move=> le_kDρ_n; rewrite !c2tE /=.
      have h z: n + z - (k + size ρ) = (n - (k + size ρ)) + z.
        by rewrite [n+z]addnC -addnBA // [z+_]addnC.
      rewrite !h; have ->: l+m+k+1 = l.+1 + (m+k).
         by rewrite addn1 addSn !addnA.
      rewrite !addnA ltnNge leq_add2r -{2}[m]add0n leq_add2r.
      rewrite {1}addnS /= eqn_add2r -{3}[m]add0n eqn_add2r.
      by rewrite {1}addnS /= !(addnS, addSn).
  + move=> t IHt u IHu l l0 m k le_l0_l wf_ρ_l0.
    rewrite ![_ (σc (ξ [_] _) _)]scE ![sc (_ ○ _) _]scE !c2tE /=.
    by rewrite (IHt _ l0) // (IHu _ l0).
  + move=> t IHt l l0 m k le_l0_l wf_ρ_l0.
    rewrite ![_ (σc (ξ [_] _) _)]scE ![sc (λλ [_]) _]scE !c2tE /=.
    rewrite -cat_cons -μS -addnS (IHt _ l0) // addnS; congr (λ [_ [! _ ← _]]).
    by rewrite {1}[(_+k)+1]addnAC -cat_cons -μS !addn1 addnS.
Qed.

(* -------------------------------------------------------------------- *)
Lemma L3_r:
  forall c,
    (forall B ρ N l0 l m, c = ξ [ρ] B -> l >= l0 -> wf (ξ [ρ] N :: ρ) l0 ->
          σc (ξ [μ l m ++ (ξ [ρ] N) :: ρ] B) (l+m)
        = (σc (ξ [μ l.+1 m ++ ^l.+1 :: ρ] B) (l + m + 1))[! m ← σc (ξ [ρ] N) l] :> term).
Proof.
  elim/clind=> // t ρ IH B ρ' N l0 l m [_ <-] {t ρ'}; elim: B l0 l m.
  + move=> n l0 l m le_l0_l wfρ /=; rewrite scE [X in (_ X)[! _ ← _]]scE.
    rewrite !size_cat !size_μ /=; case: ltnP.
    * move=> lt_n_mDSρ; case: (ltnP n m) => [lt_nm|].
      - rewrite !nth_cat !size_μ lt_nm !nth_μ //.
        have le_n_mDl: n <= l + m by rewrite ltnW // ltn_addl.
        rewrite ![sc ^_ _]scE subKn // addn1 addSn.
        by rewrite subKn 1?ltnW // !c2tE /= lt_nm.
      - rewrite leq_eqVlt; case/orP => [/eqP->|].
        + rewrite !nth_cat !size_μ ltnn subnn /= [sc ^_ _]scE c2tE /=.
          rewrite addn1 -addSn -[X in l.+1 + n - X]addn0 subnDl subn0.
          rewrite ltnn eqxx; move: (@L1_r (ξ [ρ] N) N ρ l0 l 0 0 n).
          by rewrite !(addn0, add0n) /= => -> //; inversion wfρ.
        + case: n lt_n_mDSρ => // n; rewrite addnS ltnS.
          move=> lt_n_mDρ lt_m_Sn; rewrite !nth_cat !size_μ ltnNge ltnW //=.
          rewrite subSn //=; set c := nth _ _ _; have cρ: c \in ρ.
            by rewrite mem_nth // -subSn // leq_subLR.
          have wf'ρ: wf ρ l0 by inversion wfρ. case: (mem_wf wf'ρ cρ).
          - case=> i -> le_i_l0; rewrite ![sc ^_ _]scE !c2tE /=.
            have ->: l + m + 1 - i = m.+1 + (l - i).
              by rewrite addn1 -addnS addnC addnBA // (@leq_trans l0).
            rewrite ltnNge ltnW ?ltn_addr //= addSnnS.
            rewrite -[X in _==X]addn0 eqn_add2l /=.
            by rewrite addnC -addnBA // (@leq_trans l0).
          - case=> [T] [ρ'] [l'] [cE wf_ρ'_l' le_l'_l0]; rewrite cE.
            have le_l'_l := leq_trans le_l'_l0 le_l0_l; set S := sc _ l.
            have /= := (@L2 _ _ _ S _ _ m 0 cE le_l'_l wf_ρ'_l').
            by rewrite !(addn0, add0n).
     * move=> le_mDSρ_n; set q := n - (m + (size ρ).+1).
       have h: forall h, n + h - (m + (size ρ).+1) = q + h.
         by move=> h; rewrite addnC -addnBA // addnC.
       rewrite !{}h !c2tE /= !addnA [_+1]addnAC.
       rewrite [X in X < m]addnC -ltn_subRL subnn /=.
       by rewrite -[X in _==X]add0n eqn_add2r addnS /= addn0.
   + move=> t IHt u IHu l0 l m le_l0_l wf /=.
     rewrite 2!scE !c2tE /= (IHt l0) // (IHu l0) //.
     by rewrite [sc (ξ [_] (_ · _)) _]scE [sc (_ ○ _) _]scE !c2tE /=.
   + move=> t IHt l0 l m le_l0_l wf /=; rewrite 2!scE !c2tE /=.
     rewrite -cat_cons -μS -!addnS (IHt l0) //.
     rewrite [sc (ξ [_] (λ [_])) _]scE [sc (λλ [_]) _]scE !c2tE /=.
     by rewrite μS !addn1 addnS.
Qed.

(* -------------------------------------------------------------------- *)
Lemma L3:
  forall B ρ N l, wf (ξ [ρ] N :: ρ) l ->
      σc (ξ [ξ [ρ] N :: ρ] B) l
    = (σc (ξ [^l.+1 :: ρ] B) l.+1)[! 0 ← σc (ξ [ρ] N) l] :> term.
Proof.
  move=> B ρ N l wf; move: (@L3_r (ξ [ρ] B) B ρ N l l 0).
  by rewrite !(addn0, add0n) /= -addn1 => ->.
Qed.

(* ==================================================================== *)
(*                           Commutation                                *)
(* ==================================================================== *)

(* -------------------------------------------------------------------- *)
Definition IsNeutral (t : term) :=
  if t is λ [_] then false else true.

(* -------------------------------------------------------------------- *)
Inductive IsWhnf : term -> Prop :=
| IsWhnfLam : forall t, IsWhnf (λ [t])
| IsWhnfVar : forall x ts, IsWhnf (#x ·! ts).

(* -------------------------------------------------------------------- *)
Inductive IsNf : term -> Prop :=
| IsNfLam : forall t, IsNf t -> IsNf (λ [t])
| IsNfVar : forall x ts, (forall t, t \in ts -> IsNf t) -> IsNf (#x ·! ts).

(* -------------------------------------------------------------------- *)
Reserved Notation "t1 ⇀ t2"   (at level 60, no associativity, format "t1  ⇀  t2").
Reserved Notation "t1 ⇀_β t2" (at level 60, no associativity, format "t1  ⇀_β  t2").
Reserved Notation "t1 → t2"   (at level 60, no associativity, format "t1  →  t2").

(* -------------------------------------------------------------------- *)
Section NoCtxt.
  Variable R : term -> term -> Prop.

  Inductive NoRed : term -> term -> Prop :=
  | NoBase: forall t1 t2,
      R t1 t2 -> t1 ⇀ t2

  | Noμ1: forall t1 t1' t2,
      ~ IsWhnf t1 -> (t1 ⇀ t1')
    -> (t1 · t2 ⇀ t1' · t2)

  | Noμ2: forall t1 t1' t2,
      IsWhnf t1 -> ~ IsNeutral t1 -> (t1 ⇀ t1')
    -> (t1 · t2 ⇀ t1' · t2)

  | Noν: forall t1 t2 t2',
      IsNf t1 -> (t2 ⇀ t2') -> (t1 · t2 ⇀ t1 · t2')

  | Noξ: forall t t', (t ⇀ t') -> (λ [t] ⇀ λ [t'])

  where "t1 ⇀ t2" := (NoRed t1 t2).  
End NoCtxt.

(* -------------------------------------------------------------------- *)
Inductive BetaRed1 : term -> term -> Prop :=
| Beta: forall t u, (λ [t] · u) ⇀_β t[!0 ← u]

where "t ⇀_β u" := (BetaRed1 t u).

Definition BetaRed := NoRed BetaRed1.

Notation "t → u" := (BetaRed t u).

(* -------------------------------------------------------------------- *)
Definition IsNeutralC (c : closure) :=
  if c is λλ [_] then false else true.

(* -------------------------------------------------------------------- *)
Inductive IsWhnfC : closure -> Prop :=
| IsWhnfCLam : forall t ρ, IsWhnfC (λλ [ξ [ρ] t])
| IsWhnfCVar : forall n cs, IsWhnfC (⌊n⌋ ○! cs).

(* -------------------------------------------------------------------- *)
Inductive IsNfC : closure -> Prop :=
| IsNfCLam : forall c, IsNfC c -> IsNfC (λλ [c])
| IsNfCVar : forall n cs, (forall c, c \in cs -> IsNfC c) -> IsNfC (⌊n⌋ ○! cs).

(* -------------------------------------------------------------------- *)
Reserved Notation "t ⇀_[ l ] u" (at level 60, no associativity, format "t  ⇀_[ l ]  u").
Reserved Notation "t ⇀_[ 'ρ' , l ] u" (at level 60, no associativity, format "t  ⇀_[ 'ρ' , l ]  u").
Reserved Notation "t ⇀_[ 'β' , l ] u" (at level 60, no associativity, format "t  ⇀_[ 'β' , l ]  u").
Reserved Notation "t →_[ 'ρ' , l ] u" (at level 60, no associativity, format "t  →_[ 'ρ' , l ]  u").
Reserved Notation "t →_[ 'β' , l ] u" (at level 60, no associativity, format "t  →_[ 'β' , l ]  u").
Reserved Notation "t →*_[ 'ρ' , l ] u" (at level 60, no associativity, format "t  →*_[ 'ρ' , l ]  u").
Reserved Notation "t →*_[ 'β' , l ] u" (at level 60, no associativity, format "t  →*_[ 'β' , l ]  u").

(* -------------------------------------------------------------------- *)
Section NoCCtxt.
  Variable R : nat -> closure -> closure -> Prop.

  Inductive NoCRed : nat -> closure -> closure -> Prop :=
  | NoCBase: forall l c1 c2, 

                    R l c1 c2
      (* ————————————————————————————————– *)
       ->          c1 ⇀_[l] c2

  | NoCμ1: forall l c1 c1' c2, ~IsWhnfC c1 ->

                  c1 ⇀_[l] c2
      (* ————————————————————————————————– *)
      ->    (c1 ○ c2) ⇀_[l] (c1' ○ c2)

  | NoCμ2: forall l c1 c1' c2, IsWhnfC c1 -> ~ IsNeutralC c1 ->

                  c1 ⇀_[l] c1'
      (* ————————————————————————————————– *)
      ->    (c1 ○ c2) ⇀_[l] (c1' ○ c2)

  | NoCν: forall l c1 c2 c2', IsNfC c1 -> ~ IsNeutralC c1 ->

                   c2 ⇀_[l] c2'
      (* ————————————————————————————————– *)
      ->    (c1 ○ c2) ⇀_[l] (c1 ○ c2')

  | NoCξ: forall l c c',

                   c ⇀_[l.+1] c'
      (* ————————————————————————————————– *)
      ->     (λλ [c]) ⇀_[l] (λλ [c])
  
  where "c1 ⇀_[ l ] c2" := (NoCRed l c1 c2).
End NoCCtxt.

(* -------------------------------------------------------------------- *)
Inductive RhoRed1 : nat -> closure -> closure -> Prop :=
| RhoRedVar: forall l n ρ, n < size ρ ->
    (ξ [ρ] #n) ⇀_[ρ,l] nth ^0 ρ n

| RhoRedFree: forall l n ρ, n >= size ρ ->
    (ξ [ρ] #n) ⇀_[ρ,l] ⌊n - (size ρ - l)⌋

| RhoRedApp: forall l t u ρ,
    (ξ [ρ] (t · u)) ⇀_[ρ,l] (ξ [ρ] t) ○ (ξ [ρ] u)

| RhoRedLam: forall l t ρ,
    (ξ [ρ] (λ [t])) ⇀_[ρ,l] λλ [ξ [^l.+1 :: ρ] t]

where "c1 ⇀_[ 'ρ' , l ] c2" := (RhoRed1 l c1 c2).

Definition RhoRed := NoCRed RhoRed1.

Notation "c1 →_[ 'ρ' , l ] c2" := (RhoRed l c1 c2).
Notation "c1 →*_[ 'ρ' , l ] c2" := (clos_refl_trans _ (RhoRed l) c1 c2).

(* -------------------------------------------------------------------- *)
Inductive TBetaRed1 : nat -> closure -> closure -> Prop :=
| TBeta: forall l t u ρ,
              (λλ [ξ[^l.+1 :: ρ] t]) ○ (ξ [ρ] u)
    ⇀_[β, l] (ξ [ξ [ρ] u :: ρ] t)

where "c1 ⇀_[ 'β' , l ] c2" := (TBetaRed1 l c1 c2).

Definition TBetaRed := NoCRed TBetaRed1.

Notation "c1 →_[ 'β' , l ] c2" := (TBetaRed l c1 c2).
Notation "c1 →*_[ 'β' , l ] c2" := (clos_refl_trans _ (TBetaRed l) c1 c2).

(* -------------------------------------------------------------------- *)
Reserved Notation "t →_[ 'σ' , l ] u" (at level 60, no associativity, format "t  →_[ 'σ' , l ]  u").
Reserved Notation "t →*_[ 'σ' , l ] u" (at level 60, no associativity, format "t  →*_[ 'σ' , l ]  u").

Definition SigmaRed (l : nat) (c1 c2 : closure) := c2 = sc c1 l.

Notation "c1 →_[ 'σ' , l ] c2" := (SigmaRed l c1 c2).
Notation "c1 →*_[ 'σ' , l ] c2" := (clos_refl_trans _ (SigmaRed l) c1 c2).

(* -------------------------------------------------------------------- *)
Theorem commute (M : closure) (E E' : ephemeral) (l n : nat):
     M →*_[σ, l] E
  -> E → E'
  -> exists X M', M →*_[ρ, l] X /\ X  →_[β, l] M'.
Proof. Admitted.

(*
*** Local Variables: ***
*** coq-load-path: ("ssreflect" ".") ***
*** End: ***
 *)
