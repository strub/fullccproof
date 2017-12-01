(* -------------------------------------------------------------------- *)
From mathcomp Require Import all_ssreflect.
Require Import Relation_Operators.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* -------------------------------------------------------------------- *)
Tactic Notation "rev" "/" constr(x) ":" hyp(h) :=
  inversion h using x.

Tactic Notation "rev" "/" constr(x) :=
  let h := fresh "h" in move=> h; rev/x: h => {h}.

Ltac ctor := constructor.

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
Reserved Notation "t ·! u" (at level 40, left associativity, format "t  ·!  u").

Definition AppS t := foldl App t.

Notation "t ·! u" := (AppS t u).

Lemma AppS_cons t u us: t ·! (u :: us) = (t · u) ·! us.
Proof. by []. Qed.

Lemma AppS_rcons t u us: t ·! (rcons us u) = (t ·! us) · u.
Proof. by rewrite -cats1 /AppS foldl_cat. Qed.

Lemma AppS_cat t ts us : t ·! (ts ++ us) = t ·! ts ·! us.
Proof. by elim: ts t us => /=. Qed.

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

(* -------------------------------------------------------------------- *)
Fixpoint h (c : closure) := nosimpl(
  match c with
  | ^n      => 0%N
  | ⌊n⌋     => 0%N
  | c1 ○ c2 => (maxn (h c1) (h c2)).+1
  | λλ [c]  => (h c).+1
  | ξ [ρ] t =>
      let fix ht (t : term) := nosimpl (
        match t with
        | λ [t']  => (ht t').+2
        | t1 · t2 => (maxn (ht t1) (ht t2)).+2
        | #n      => 
          let hs := [seq h c | c <- ρ] in
          if n < size hs then (nth 0 hs n).+1 else 0
        end)
      in ht t
  end).

(* -------------------------------------------------------------------- *)
Section HInd.
Variable (P : closure -> Prop).

Hypothesis (ih : forall c, (forall c', h c' < h c -> P c') -> P c).

Lemma hind c : P c.
Proof. Admitted.
End HInd.

(* -------------------------------------------------------------------- *)
Fixpoint is_ephemeral c :=
  match c with
  | ⌊_⌋     => true
  | λλ [c]  => is_ephemeral c
  | c1 ○ c2 => [&& is_ephemeral c1 & is_ephemeral c2]
  | _       => false
  end.

(* -------------------------------------------------------------------- *)
Reserved Notation "c ○! cs"
  (at level 40, left associativity, format "c  ○!  cs").

Definition CAppS c := foldl CApp c.

Notation "c ○! cs" := (CAppS c cs).

Lemma CAppS_cons c c' cs: c ○! (c' :: cs) = (c ○ c') ○! cs.
Proof. by []. Qed.

Lemma CAppS_rcons c c' cs: c ○! (rcons cs c') = (c ○! cs) ○ c'.
Proof. by rewrite -cats1 /CAppS foldl_cat. Qed.

Lemma CAppS_cat c cs cs' : c ○! (cs ++ cs') = c ○! cs ○! cs'.
Proof. by elim: cs c cs' => /=. Qed.

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

Lemma sc_appS l c cs :
  sc (c ○! cs) l = (sc c l) ○! [seq sc c l | c <- cs].
Proof. by elim: cs c => //= c' cs ih c; rewrite ih scE. Qed.

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

Lemma c2t_appS c cs :
  c ○! cs = (c ·! [seq term_of_closure_r c | c <- cs]) :> term.
Proof. by elim: cs c => // c' cs ih c; rewrite ih c2tE. Qed.

(* -------------------------------------------------------------------- *)
Inductive wfr : nat -> seq closure -> nat -> Prop :=
| WFREmpty:
    forall n, wfr 0 [::] n

| WFRTerm:
    forall i t ρt ρ n, i <= n
     -> wfr i ρt i
     -> wfr i ρ n
     -> wfr i (ξ [ρt] t :: ρ) n

| WFRFormal:
    forall i ρ n, i.+1 <= n
     -> wfr i ρ n
     -> wfr i.+1 (^i.+1 :: ρ) n

| WFRWeak:
    forall i j ρ n, i <= j -> j <= n
     -> wfr i ρ n
     -> wfr j ρ n.

Notation wf ρ l := (wfr l ρ l).

(* -------------------------------------------------------------------- *)
Lemma wfr_strg i ρ l l' : l <= l' -> wfr i ρ l -> wfr i ρ l'.
Proof.
move=> le_ll' wf1; elim: wf1 l' le_ll' => {i ρ l}; try by ctor.
+ move=> i t ρt ρ n lt_in wft iht wf ih l' le_nl'; ctor.
    by apply/(leq_trans lt_in). by apply/iht. by apply/ih.
+ move=> i ρ n lt_in wfr ih l' le_nl'; ctor.
    by apply/(leq_trans lt_in). by apply/ih.
+ move=> i j ρ n le_ij le_jn wf ih l' le_nl'.
  apply/(@WFRWeak i) => //; last by apply/ih.
  by apply/(leq_trans le_jn).
Qed.

(* -------------------------------------------------------------------- *)
Lemma wfr_term i ρt t ρ n:
  wfr i (ξ [ρt] t :: ρ) n ->
    exists2 j, j <= i & wfr j ρ n.
Proof.
set cs := _ :: _; move: {-2}cs (erefl cs); rewrite {}/cs.
move=> cs csE wf1; elim: wf1 csE => // {i cs n}.
+ by move=> i t' ρt' ρ' n lt_in h1 _ h2 _ [_ _ <-]; exists i.
+ move=> i j ρ' n le_ij _ wf' ih eq; case: (ih eq).
  by move=> k le_ki wf1; exists k => //; apply/(leq_trans le_ki).
Qed.

(* -------------------------------------------------------------------- *)
Lemma wfr_term_sub i ρt t ρ n:
  wfr i (ξ [ρt] t :: ρ) n ->
    exists2 j, j <= i & wfr j ρt n.
Proof.
set cs := _ :: _; move: {-2}cs (erefl cs); rewrite {}/cs.
move=> cs csE wf1; elim: wf1 csE => // {i cs n}.
+ move=> i t' ρt' ρ' n lt_in h1 _ h2 _ [_ <- _].
  by exists i => //; apply/(wfr_strg lt_in).
+ move=> i j ρ' n le_ij _ wf' ih eq; case: (ih eq).
  by move=> k le_ki wf1; exists k => //; apply/(leq_trans le_ki).
Qed.

(* -------------------------------------------------------------------- *)
Inductive wfc : nat -> closure -> Prop :=
| WFCLvl l n :
    n <= l -> wfc l ^n

| WFCGrd l n :
    wfc l ⌊n⌋

| WFCApp l c1 c2 :
    wfc l c1 -> wfc l c2 -> wfc l (c1 ○ c2)

| WFCLam l c :
    wfc l.+1 c -> wfc l (λλ [c])

| WFCClos l t ρ: wf ρ l -> wfc l (ξ [ρ] t).

(* -------------------------------------------------------------------- *)
Derive Inversion_clear wfc_lam
  with (forall l c, wfc l (λλ [c]))
  Sort Prop.

Derive Inversion_clear wfc_app
  with (forall l c1 c2, wfc l (c1 ○ c2))
  Sort Prop.

Derive Inversion_clear wfc_lvl
  with (forall l n, wfc l ^n)
  Sort Prop.

Derive Inversion_clear wfc_clos
  with (forall l ρ t, wfc l (ξ [ρ] t))
  Sort Prop.

Lemma wfc_appsl l c cs : wfc l (c ○! cs) -> wfc l c.
Proof. by elim: cs c => //= c1 cs ih c /ih; rev/wfc_app. Qed.

(* -------------------------------------------------------------------- *)
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
  [\/ exists2 i, c = ^i.+1 & i.+1 <= l
    | exists T ρ' l', [/\ c = ξ [ρ'] T, wf ρ' l' & l' <= l]].
Proof.
elim=> //=.
+ move=> i t pt ρ' n le_in wf_pt IHpt wfρ' IHρ'; rewrite inE.
  case/orP; [move/eqP=> -> | by move/IHρ'].
  by right; exists t, pt, i.
+ move=> i ρ' n lt_in wfρ' IHρ'; rewrite inE.
  by case/orP; [move/eqP=> ->; left; exists i | by move/IHρ'].
Qed.

(* -------------------------------------------------------------------- *)
Lemma L_5_4:                  (* Lemma 5.4 [in paper] *)
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
      - case=> i -> lt_i_l0; rewrite !scE !c2tE /=.
        have lt_i_l := leq_trans lt_i_l0 le_l0_l.
        apply/esym; rewrite {1}[_+k]addnC {1}[l+_]addnC !addnA.
        rewrite -addnBA 1?leq_addr // addnC addnBA 1?addnC //.
        by rewrite addnCA; apply/(leq_trans lt_i_l)/leq_addr.
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
Lemma L_5_3 T ρ l m: wf ρ l ->   (* Lemma 5.3 [in paper] *)
  σc (ξ [ρ] T) (l + m) = ↑[0,m] (σc (ξ [ρ] T) l) :> term.
Proof.
  move=> wfρl; move: (@L_5_4 (ξ [ρ] T) T ρ l l 0 0 m).
  by rewrite !(addn0, add0n) /= => ->.
Qed.

(* -------------------------------------------------------------------- *)
Lemma L_5_6:                    (* Lemma 5.6 [in paper] *)
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
      + case=> i -> lt_i_l0; rewrite !scE !c2tE /=.
        have {-4}->: l+m+k+1 - i.+1 = m+k + (l-i).
          have lt_i_l := leq_trans lt_i_l0 le_l0_l.
          rewrite addn1 -!addSn [_+m]addnC [_+k]addnAC.
          by rewrite -addnBA ?subSS // ltnW.
        rewrite -ltn_subRL subnn /= -[X in _==X]addn0.
        have lt_il := leq_trans lt_i_l0 le_l0_l.
        rewrite eqn_add2l /= addn1 subn_eq0 leqNgt lt_il /=.
        by rewrite subSn // -addnA (leq_trans lt_il) ?leq_addr.
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
Lemma L_5_5:                    (* Lemma 5.5 [in paper] *)
  forall T ρ S l l0 m, l >= l0 -> wf ρ l0 ->
    σc (ξ [ρ] T) (l+m) = (σc (ξ [ρ] T) (l+m+1))[! m ← S] :> term.
Proof.
  move=> T ρ S l l0 m; move: (@L_5_6 (ξ [ρ] T) T ρ S l l0 m 0).
  by rewrite !(addn0, add0n) /=; apply.
Qed.

(* -------------------------------------------------------------------- *)
Lemma L_5_8:                    (* Lemma 5.8 [in paper] *)
  forall c,
    (forall B ρ1 ρ2 N l0 l m, c = ξ [ρ1] B -> l >= l0 -> wf (ξ [ρ2] N :: ρ1) l0 ->
          σc (ξ [μ l m ++ (ξ [ρ2] N) :: ρ1] B) (l+m)
        = (σc (ξ [μ l.+1 m ++ ^l.+1 :: ρ1] B) (l + m + 1))
            [! m ← σc (ξ [ρ2] N) l] :> term).
Proof.
elim/clind=> // t ρ IH B ρ1 ρ2 N l0 l m [_ <-] {t ρ1}; elim: B l0 l m.
+ move=> n l0 l m le_l0_l wfρ /=; rewrite scE [X in (_ X)[! _ ← _]]scE.
  rewrite !size_cat !size_μ /=; case: ltnP.
  * move=> lt_n_mDSρ; case: (ltnP n m) => [lt_nm|].
    - rewrite !nth_cat !size_μ lt_nm !nth_μ //.
      have le_n_mDl: n <= l + m by rewrite ltnW // ltn_addl.
      rewrite ![sc (^ _) _]scE subKn // addn1 addSn.
      by rewrite subKn 1?ltnW // !c2tE /= lt_nm.
    - rewrite leq_eqVlt; case/orP => [/eqP->|].
      + rewrite !nth_cat !size_μ ltnn subnn /= [sc (^ _) _]scE c2tE /=.
        rewrite addn1 -addSn -[X in l.+1 + n - X]addn0 subnDl subn0.
        rewrite ltnn eqxx; move: (@L_5_4 (ξ [ρ2] N) N ρ2 l0 l 0 0 n).
        rewrite !(addn0, add0n) /= => -> //; case/wfr_term_sub: wfρ.
        by move=> k le_kl0 wfρ; apply (@WFRWeak k) => //; apply/ltnW.
      + case: n lt_n_mDSρ => // n; rewrite addnS ltnS.
        move=> lt_n_mDρ lt_m_Sn; rewrite !nth_cat !size_μ ltnNge ltnW //=.
        rewrite subSn //=; set c := nth _ _ _; have cρ: c \in ρ.
          by rewrite mem_nth // -subSn // leq_subLR.
        have wf'ρ: wf ρ l0; first case/wfr_term: wfρ.
          by move=> k le_kl0; apply (@WFRWeak k).
        case: (mem_wf wf'ρ cρ).
        - case=> i -> le_i_l0; rewrite ![sc (^ _) _]scE !c2tE /=.
          have ->: l + m + 1 - i.+1 = m + (l - i).
            rewrite addn1 subSS addnC addnBA //.
            by apply/ltnW/(@leq_trans l0).
          rewrite -ltn_subRL subnn ltn0 -{3}[m]addn0 eqn_add2l.
          rewrite subn_eq0 leqNgt (@leq_trans l0) //=.
          by rewrite subnS addnC -addnBA // ltnW 1?(@leq_trans l0).
        - case=> [T] [ρ'] [l'] [cE wf_ρ'_l' le_l'_l0]; rewrite cE.
          have le_l'_l := leq_trans le_l'_l0 le_l0_l; set S := sc _ l.
          have /= := (@L_5_6 _ _ _ S _ _ m 0 cE le_l'_l wf_ρ'_l').
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
Lemma L_5_7:                    (* Lemma 5.7 [in paper] *)
  forall B ρ1 ρ2 N l, wf (ξ [ρ2] N :: ρ1) l ->
      σc (ξ [ξ [ρ2] N :: ρ1] B) l
    = (σc (ξ [^l.+1 :: ρ1] B) l.+1)[! 0 ← σc (ξ [ρ2] N) l] :> term.
Proof.
move=> B ρ1 ρ2 N l wf; move: (@L_5_8 (ξ [ρ1] B) B ρ1 ρ2 N l l 0).
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

  | Noμ1: forall t1 t1' t2, ~ IsWhnf t1
    -> (t1 ⇀ t1')
    -> (t1 · t2 ⇀ t1' · t2)

  | Noμ2: forall t1 t1' t2, IsWhnf t1 -> IsNeutral t1
    -> (t1 ⇀ t1')
    -> (t1 · t2 ⇀ t1' · t2)

  | Noν: forall t1 t2 t2', IsNf t1 -> IsNeutral t1
    -> (t2 ⇀ t2')
    -> (t1 · t2 ⇀ t1 · t2')

  | Noξ: forall t t', (t ⇀ t') -> (λ [t] ⇀ λ [t'])

  where "t1 ⇀ t2" := (NoRed t1 t2).  
End NoCtxt.

(* -------------------------------------------------------------------- *)
Inductive BetaRed1 : term -> term -> Prop :=
| Beta: forall t u, (λ [t] · u) ⇀_β t[!0 ← u]

where "t ⇀_β u" := (BetaRed1 t u).

Notation BetaRed := (NoRed BetaRed1).

Notation "t → u" := (BetaRed t u).

(* -------------------------------------------------------------------- *)
Lemma Noμ1S R t1 t1' ts :
  ~ IsWhnf t1 -> NoRed R t1 t1' -> NoRed R (t1 ·! ts) (t1' ·! ts).
Proof.
move=> Nwh1 r; elim: ts t1 t1' Nwh1 r => // t ts ih /= t1 t1' Nwh1 r.
apply/ih => [h|]; [apply/Nwh1 | by apply/Noμ1].
inversion h; elim/last_ind: ts0 H0 => //= us u _.
by rewrite AppS_rcons => -[<- _]; ctor.
Qed.

(* -------------------------------------------------------------------- *)
Lemma Noμ2Var x ts t t' us :
    (forall z, z \in ts -> IsNf z) -> t → t'
  -> (#x ·! ts · t ·! us) → (#x ·! ts · t' ·! us).
Proof.
move=> nf r; elim/last_ind: us => [|us u ih]//=.
  apply/Noν => //; first by apply/IsNfVar.
  by elim/last_ind: {nf} ts => // zs z _; rewrite AppS_rcons.
rewrite !AppS_rcons; apply/Noμ2 => //.
  by rewrite -AppS_rcons -AppS_cat; ctor.
rewrite -AppS_rcons -AppS_cat; elim/last_ind: (_ ++ _) => //.
by move=> zs z ihz; rewrite AppS_rcons .
Qed.

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
Inductive IsRhoS : seq closure -> Prop :=
| RhoS1 ρ1 ρ2 t :
    IsRhoS ρ1 -> IsRhoS ρ2 -> IsRhoS (ξ [ρ1] t :: ρ2)

| RhoS2 n ρ :
    IsRhoS ρ -> IsRhoS (^n :: ρ)

| RhoS3 :
    IsRhoS [::].

(* -------------------------------------------------------------------- *)
Inductive IsStc : closure -> Prop :=
| Stc1 ρ t ρts :
       IsRhoS ρ
    -> (forall ρt, ρt \in ρts -> IsRhoS ρt.1)
    -> IsStc (ξ [ρ] t ○! [seq ξ[ρt.1] ρt.2 | ρt <- ρts])

| Stc2 c :
    IsStc c -> IsStc (λλ [c])

| Stc3 n nfc c ρts :
    let cs := [seq ξ [ρt.1] ρt.2 | ρt <- ρts] in
       IsStc c
    -> (forall nf, nf \in nfc -> IsNfC nf)
    -> (forall ρt, ρt \in ρts -> IsRhoS ρt.1)
    -> IsStc (⌊n⌋ ○! nfc ○ c ○! cs).

(* -------------------------------------------------------------------- *)
Inductive IsExc : closure -> Prop :=
| Exc1 n ρ t1 t2 ρts :
    let cs := [seq ξ [ρt.1] ρt.2 | ρt <- ρts] in
       IsRhoS ρ -> size ρts != 0
    -> (forall ρt, ρt \in ρts -> IsRhoS ρt.1)
    -> IsExc ((λλ [ξ [^n :: ρ] t1]) ○! cs)

| Exc2 c :
    IsExc c -> IsExc (λλ [c])

| Exc3 n nfc c ρts :
    let cs := [seq ξ [ρt.1] ρt.2 | ρt <- ρts] in
       IsExc c
    -> (forall nf, nf \in nfc -> IsNfC nf)
    -> (forall ρt, ρt \in ρts -> IsRhoS ρt.1)
    -> IsExc (⌊n⌋ ○! nfc ○ c ○! cs).

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

                  c1 ⇀_[l] c1'
      (* ————————————————————————————————– *)
      ->    (c1 ○ c2) ⇀_[l] (c1' ○ c2)

  | NoCμ2: forall l c1 c1' c2, IsWhnfC c1 -> IsNeutralC c1 ->

                  c1 ⇀_[l] c1'
      (* ————————————————————————————————– *)
      ->    (c1 ○ c2) ⇀_[l] (c1' ○ c2)

  | NoCν: forall l c1 c2 c2', IsNfC c1 -> IsNeutralC c1 ->

                   c2 ⇀_[l] c2'
      (* ————————————————————————————————– *)
      ->    (c1 ○ c2) ⇀_[l] (c1 ○ c2')

  | NoCξ: forall l c c',

                   c ⇀_[l.+1] c'
      (* ————————————————————————————————– *)
      ->     (λλ [c]) ⇀_[l] (λλ [c'])
  
  where "c1 ⇀_[ l ] c2" := (NoCRed l c1 c2).
End NoCCtxt.

(* -------------------------------------------------------------------- *)
Inductive RhoRed1 : nat -> closure -> closure -> Prop :=
| RhoRedVar: forall l n ρ, n < size ρ ->
    (ξ [ρ] #n) ⇀_[ρ,l] nth ^0 ρ n

| RhoRedFree: forall l n ρ, n >= size ρ ->
    (ξ [ρ] #n) ⇀_[ρ,l] ⌊n + l - size ρ⌋

| RhoRedApp: forall l t u ρ,
    (ξ [ρ] (t · u)) ⇀_[ρ,l] (ξ [ρ] t) ○ (ξ [ρ] u)

| RhoRedLam: forall l t ρ,
    (ξ [ρ] (λ [t])) ⇀_[ρ,l] λλ [ξ [^l.+1 :: ρ] t]

| RhoRedPar: forall l n,
    ^n ⇀_[ρ,l] ⌊l-n⌋

where "c1 ⇀_[ 'ρ' , l ] c2" := (RhoRed1 l c1 c2).

Notation RhoRed := (NoCRed RhoRed1).

Notation "c1 →_[ 'ρ' , l ] c2" := (RhoRed l c1 c2).
Notation "c1 →*_[ 'ρ' , l ] c2" := (clos_refl_trans _ (RhoRed l) c1 c2).

(* -------------------------------------------------------------------- *)
Inductive TBetaRed1 : nat -> closure -> closure -> Prop :=
| TBeta: forall l t u ρ,
    (λλ [ξ[^l.+1 :: ρ] t]) ○ (ξ [ρ] u)
      ⇀_[β, l] (ξ [ξ [ρ] u :: ρ] t)

where "c1 ⇀_[ 'β' , l ] c2" := (TBetaRed1 l c1 c2).

Notation TBetaRed := (NoCRed TBetaRed1).

Notation "c1 →_[ 'β' , l ] c2" := (TBetaRed l c1 c2).
Notation "c1 →*_[ 'β' , l ] c2" := (clos_refl_trans _ (TBetaRed l) c1 c2).

(* -------------------------------------------------------------------- *)
Reserved Notation "t →_[ 'σ' , l ] u" (at level 60, no associativity, format "t  →_[ 'σ' , l ]  u").
Reserved Notation "t →*_[ 'σ' , l ] u" (at level 60, no associativity, format "t  →*_[ 'σ' , l ]  u").

Definition SigmaRed (l : nat) (c1 c2 : closure) := c2 = sc c1 l.

Notation "c1 →_[ 'σ' , l ] c2" := (SigmaRed l c1 c2).
Notation "c1 →*_[ 'σ' , l ] c2" := (clos_refl_trans _ (SigmaRed l) c1 c2).

(* -------------------------------------------------------------------- *)
Derive Inversion_clear rwbb
  with (forall c1 c2 c l, (λλ [c1] ○ c2) →_[β,l] c)
  Sort Prop.

Derive Inversion_clear rwb1
  with (forall c c' l, c ⇀_[β,l] c')
  Sort Prop.

(* -------------------------------------------------------------------- *)
Derive Inversion_clear rwb_app
  with (forall l c1 c2 c, c1 ○ c2 →_[β,l] c)
  Sort Prop.

Derive Inversion rwb1_app
  with (forall l c1 c2 c, c1 ○ c2 ⇀_[β,l] c)
  Sort Prop.

(* -------------------------------------------------------------------- *)
Derive Inversion_clear rwbl_r
  with (forall c c' l, λλ [c] →_[β,l] c')
  Sort Prop.

Lemma rwbl (c c' : closure) (l : nat) (P : closure -> closure -> nat -> Prop) :
  (forall c'0 : closure, c →_[β,l.+1] c'0 -> P c (λλ [c'0]) l) ->
  λλ [c] →_[β,l] c' -> P c c' l.
Proof. by move=> h rw; inversion rw using rwbl_r; first inversion 1. Qed.

(* -------------------------------------------------------------------- *)
Derive Inversion_clear rwb_grd
  with (forall n c l, ⌊n⌋ →_[β,l] c).

Derive Inversion rwb1_grd
  with (forall n c l, ⌊n⌋ ⇀_[β,l] c).

(* -------------------------------------------------------------------- *)
Derive Inversion_clear rwb_clos_r
  with (forall l ρ t c, ξ [ρ] t →_[β,l] c)
  Sort Prop.

Derive Inversion_clear rwb1_clos_r
  with (forall l ρ t c, ξ [ρ] t ⇀_[β,l] c)
  Sort Prop.

Lemma rwb_clos l ρ t c : ~ (ξ [ρ] t →_[β,l] c).
Proof. by rev/rwb_clos_r; rev/rwb1_clos_r. Qed.

(* -------------------------------------------------------------------- *)
Lemma sc_rho1 c1 c2 l : c1 →_[ρ,l] c2 -> sc c1 l = sc c2 l.
Proof. elim => {l c1 c2} l; first last.
+ by move=> c c' _ ih; rewrite [LHS] scE [RHS]scE -ih.
+ by move=> c1 c2 c2' _ _ _ ih; rewrite [LHS] scE [RHS]scE -ih.
+ by move=> c1 c1' c2 _ _ _ ih; rewrite [LHS] scE [RHS]scE -ih.
+ by move=> c1 c1' c2 _ _ ih; rewrite [LHS] scE [RHS]scE -ih.
move=> c1 c2 [] {l} l => [n ρ|n ρ|t u ρ|t ρ|n]; try by rewrite !scE.
+ by move=> ltn; rewrite scE ltn; congr (sc _ _); apply/set_nth_default.
+ by move=> geq; rewrite !scE ltnNge geq.
Qed.

(* -------------------------------------------------------------------- *)
Lemma sc_rho c1 c2 l : c1 →*_[ρ,l] c2 -> sc c1 l = sc c2 l.
Proof. by elim=> {c1 c2} [c1 c2 /sc_rho1||c1 c2 c3 _ -> _ ->]. Qed.

Lemma wfc_rho1 c1 c2 l : wfc l c1 -> c1 →_[ρ,l] c2 -> wfc l c2.
Proof.
move=> wfc1 r; elim: r wfc1 => {l c1 c2} l; first last.
+ by move=> c c' _ ih; rev/wfc_lam => /ih w; ctor.
+ by move=> c1 c2 c2' _ _ _ ih; rev/wfc_app => w1 /ih w2; ctor.
+ by move=> c1 c1' c2 _ _ _ ih; rev/wfc_app => /ih w1 w2; ctor.
+ by move=> c1 c1' c2 _ _ ih; rev/wfc_app=> /ih w1 w2; ctor.
move=> c1 c2 [] {c1 c2 l} l =>[n|t u|t u|t|n]; try by ctor.
+ move=> ρ ltn; rev/wfc_clos => wf1; elim: wf1 n ltn => {ρ} //=.
  * move=> i t ρt ρ n lt_in wfρt iht wfρ ih [_|k] /=; last first.
      by rewrite ltnS => /ih.
    by ctor; apply/(@WFRWeak i)/(@wfr_strg _ _ i).
  * move=> i ρ n lt_in wf ih [_|k] /=.
      by ctor. by rewrite ltnS=> /ih.
+ by move=> ρ; rev/wfc_clos=> wf1; do 2! ctor.
+ move=> ρ; rev/wfc_clos=> wf1; do 2! ctor.
  apply/WFRFormal; rewrite ?leqnn //.
  by apply/(@wfr_strg _ _ l); rewrite ?leqnSn.
Qed.

(* -------------------------------------------------------------------- *)
Lemma wfc_rho c1 c2 l : wfc l c1 -> c1 →*_[ρ,l] c2 -> wfc l c2.
Proof.
move=> h r; elim: r h => {c1 c2} [c1 c2|c //|c1 c2 c3 _ ih1 _ ih2].
  by move/wfc_rho1. by move/ih1/ih2.
Qed.

(* -------------------------------------------------------------------- *)
Derive Inversion_clear inv_nored_beta_lam_r
  with (forall t u, λ [t] → u)
  Sort Prop.

Lemma inv_noredbeta_lam t u :
  λ [t] → u -> exists t', [/\ t → t' & u = λ [t']].
Proof.
inversion 1 using inv_nored_beta_lam_r.
+ by inversion 1. + by eauto.
Qed.

(* -------------------------------------------------------------------- *)
Lemma inv_redX3_rhd l n (nfc : seq closure) M :
    (forall nf, nf \in nfc -> IsNfC nf)
  -> ~ (⌊n⌋ ○! nfc →_[β,l] M).
Proof.
elim/last_ind: nfc M => /= [|nfc nf ih] M h.
  by rev/rwb_grd; rev/rwb1_grd.
rewrite CAppS_rcons; rev/rwb_app; first rev/rwb1_app.
+ move=> _ _ t u ρ _ eq; absurd False => //; move: eq.
  by elim/last_ind: nfc {ih h} => //= zs z _; rewrite CAppS_rcons.
+ by move=> c1' h'; absurd False => //; apply/h'; ctor.
+ move=> c1' _ _; apply/ih => nf' mem; apply/h.
  by rewrite mem_rcons inE mem orbT.
+ move=> c2' _ _; have nf': (IsNfC nf); first apply/h.
    by rewrite mem_rcons inE eqxx.
  elim: nf' c2' l {ih} => [c _ ihc|k cs _ ihcs] c2' l.
    by rev/rwbl => ?; apply/ihc.
  elim/last_ind: cs ihcs c2' => /= [|cs c ihcs] ih c2'.
    by rev/rwb_grd; rev/rwb1_grd.
  rewrite CAppS_rcons; rev/rwb_app; first rev/rwb1_app.
  + move=> _ _ t u ρ _; elim/last_ind: cs {ihcs ih} => //.
    by move=> zs z _; rewrite CAppS_rcons.
  + by move=> c1' h' _; apply/h'; ctor.
  + move=> c1' _ _; apply/ihcs => c' c'_in_cs c3 l'.
    by apply/ih; rewrite mem_rcons inE c'_in_cs orbT.
  + by move=> c3 _ _; apply/ih; rewrite mem_rcons inE eqxx.
Qed.

(* -------------------------------------------------------------------- *)
Lemma inv_redX3_r l n (nfc : seq closure) c M :
    (forall nf, nf \in nfc -> IsNfC nf)
  -> ⌊n⌋ ○! nfc ○ c →_[β,l] M
  -> exists2 M', M = ⌊n⌋ ○! nfc ○ M' & c →_[β,l] M'.
Proof.
move=> h; rev/rwb_app; first rev/rwb1_app.
+ move=> _ _ t u ρ _ eq; absurd False => //; move: eq.
  by elim/last_ind: nfc {h} => // zs z; rewrite CAppS_rcons.
+ by move=> c1' h'; absurd False => //; apply/h'; ctor.
+ by move=> c1'_ _ _ /inv_redX3_rhd -/(_ h).
+ by move=> c2' _ _ r; exists c2'.
Qed.

(* -------------------------------------------------------------------- *)
Lemma inv_redX3 l n (nfc : seq closure) c ρ ts M :
  let cs := [seq ξ [ρ] t | t <- ts] in
    (forall nf, nf \in nfc -> IsNfC nf)
  -> ⌊n⌋ ○! nfc ○ c ○! cs →_[β,l] M
  -> exists2 M', M = ⌊n⌋ ○! nfc ○ M' ○! cs & c →_[β,l] M'.
Proof.
move=> cs h; rewrite {}/cs; elim/last_ind: ts M => [|ts t ih] M.
  by move/inv_redX3_r => /(_ h).
rewrite map_rcons CAppS_rcons; rev/rwb_app.
+ rev/rwb1_app=> _ _ t' u' ρ' _ eq; absurd False => //.
  move: eq; rewrite -CAppS_rcons -CAppS_cat; move: (_ ++ _).
  by elim/last_ind=> //= z zs _; rewrite CAppS_rcons.
+ move=> c1'; rewrite -CAppS_rcons -CAppS_cat; move: (_ ++ _) => cs.
  by move=> whnf; absurd False => //; apply/whnf; ctor.
+ by move=> c1' => h1 h2 /ih [M' ->] r; exists M' => //; rewrite CAppS_rcons.
+ by move=> c2' _ _ /rwb_clos.
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsStcGrd n : ~ IsStc ⌊n⌋.
Proof.
suff: forall c, IsStc c -> forall n, c <> ⌊n⌋.
+ by move=> h /h {h}h; apply/(h n).
move=> c; elim=> //= {n} [ρ t ρts _ _|k nfc c' ρts _ _ _ _] n.
+ by elim/last_ind: (map _ _) => // ?? _; rewrite CAppS_rcons.
+ by elim/last_ind: (map _ _) => // ?? _; rewrite CAppS_rcons.
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsStcLvl n : ~ IsStc ^n.
Proof.
suff: forall c, IsStc c -> forall n, c <> ^n.
+ by move=> h /h {h}h; apply/(h n).
move=> c; elim=> //= {n} [ρ t ρts _ _|k nfc c' ρts _ _ _ _] n.
+ by elim/last_ind: (map _ _) => // ?? _; rewrite CAppS_rcons.
+ by elim/last_ind: (map _ _) => // ?? _; rewrite CAppS_rcons.
Qed.

(* -------------------------------------------------------------------- *)
Lemma c2tE_lamI (c : closure) (t : term) :
  c = λ [t] :> term -> exists ct, c = λλ [ct] /\ ct = t :> term.
Proof.
case: c => [u c|n|n|c1 c2|c]; try by rewrite /term_of_closure_r -lock.
by rewrite c2tE=> -[cE]; exists c; rewrite cE.
Qed.

(* -------------------------------------------------------------------- *)
Lemma rhored_trans_lam (t t' : closure) l :
  t →*_[ρ,l.+1] t' -> λλ [t] →*_[ρ,l] λλ [t'].
Proof.
elim => [X1 X2 h|X|X1 X2 X3 _ ih1 _ ih2].
- by apply/rt_step/NoCξ.
- by apply/rt_refl.
- by apply/(rt_trans _ _ _ _ _ ih1 ih2).
Qed.

(* -------------------------------------------------------------------- *)
Lemma L_5_11 l (S M M' : closure) :
  wfc l S -> IsStc S -> M → M' -> S →_[σ, l] M ->
    exists X, [/\ wfc l X, IsExc X & S →*_[ρ, l] X].
Proof.
rewrite /SigmaRed => wfS stc rd ME; subst M.
elim/hind: S M' l stc rd wfS => S ih M' l h; case: h ih => /=.
+ move=> ρ t ρts rho_ρ rho_ρs ih /=; case: t ih => [n|t1 t2|t] ih.
  * admit.
  * case (ρts =P [::]) => [{rho_ρs}->/=|].
    - move=> sct wft. admit.
    - admit.
Abort.

(*
(* -------------------------------------------------------------------- *)
Lemma commute_r l (M1 : closure) (X : closure) (E : ephemeral) :
    wfc l X 
  -> IsExc X
  -> X →_[β, l] M1
  -> X →_[σ, l]  E
  -> exists E', M1 →_[σ, l] E' /\ E → E'.
Proof.
rewrite /SigmaRed => wfX ecX rb ->; elim: {E} ecX M1 l wfX rb.
+ move=> n ρ t1 t2 M1 l wfX h; rev/rwbb: h => // {h}; last first.
    by move=> c []; constructor.
  move=> h; move: wfX; rev/rwb1: h => t u ρ'; set c := (X in sc X).
  exists (sc c l); split=> //; rewrite 2!scE L_5_7.
    by rewrite !c2tE; do! ctor.
  rev/wfc_app: wfX; rev/wfc_lam; rev/wfc_clos => wf1.
  by rev/wfc_clos => w2; ctor.
+ move=> c exc ihc M1 l; rev/wfc_lam => wfX h; rev/rwbl: h.
  move=> c' /ihc [] // E' [eq scE']; exists (λλ [E']); rewrite scE {1}eq.
  by split=> //; rewrite scE !c2tE; apply/Noξ.
+ move=> n ρ nfc c ts cs exc ihc nf M1 l wfX.
  have wflc: wfc l c by move/wfc_appsl: wfX; rev/wfc_app.
  case/inv_redX3 => // cr -> /ihc -/(_ wflc); rewrite -/cs.
  case=> [E' [eqE' rE']]; exists (sc (⌊n⌋ ○! nfc ○ cr ○! cs) l); split=> //.
  rewrite !sc_appS !c2t_appS ![sc (_ ○ _) _]scE !sc_appS ![sc ⌊_⌋ _]scE.
  rewrite !(c2tE, c2t_appS); apply/Noμ2Var; last by rewrite -eqE'.
  move=> z; rewrite -map_comp => /mapP[c' /nf nfc'] -> /=.
  elim: nfc' l {n ihc c cs exc rE' eqE' wflc wfX} => {c'}.
    by move=> c _ ih l; rewrite scE c2tE; ctor; apply/ih.
  move=> n cs _ ih l; rewrite sc_appS scE !(c2tE, c2t_appS).
  by ctor=> t; rewrite -map_comp => /mapP[] c /ih /(_ l) nf' -> /=.
Qed.

(* -------------------------------------------------------------------- *)
Theorem commute                 (* Theorem 5.11 [in paper] *)
    l (M0 M1 : closure) (X : closure) (E : ephemeral)
:
    wfc l M0 -> IsExc X
  -> M0 →*_[ρ, l] X
  -> X →_[β, l] M1
  -> X →_[σ, l]  E
  -> exists E', M1 →_[σ, l] E' /\ E → E'.
Proof.
by move=> wfX exc r1 r2 rs; apply/(commute_r (wfc_rho wfX r1) exc r2 rs).
Qed.
*)