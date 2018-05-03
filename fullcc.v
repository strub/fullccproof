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
Axiom EM : forall P : Prop, {P}+{~P}.

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
Module Height.
Fixpoint h (c : closure) :=
  match c with
  | ^n      => 0%N
  | ⌊n⌋     => 0%N
  | c1 ○ c2 => (h c1 + h c2).+1
  | λλ [c]  => (h c).+1
  | ξ [ρ] t =>
      let ρ := [seq h c | c <- ρ] in

      let fix ht ρ t :=
        match t with
        | #n =>
            if n < size ρ then (nth 0 ρ n).+1 else 0
      
        | λ [t'] =>
            (ht (0 :: ρ) t').+2
      
        | t1 · t2 =>
            (ht ρ t1 + ht ρ t2).+2
        end
      in ht ρ t
  end.
End Height.

(* -------------------------------------------------------------------- *)
Module Type HSig.
  Parameter h  : closure -> nat.
  Parameter hE : h = Height.h.
End HSig.

Module H : HSig.
  Definition h := Height.h.

  Lemma hE : h = Height.h.
  Proof. by []. Qed.
End H.

Notation  h := H.h.
Canonical h_unlock := Unlockable H.hE.

(* -------------------------------------------------------------------- *)
Lemma hE c : h c =
  match c with
  | ^n              => 0%N
  | ⌊n⌋             => 0%N
  | c1 ○ c2         => (h c1 + h c2).+1
  | λλ [c]          => (h c).+1
  | ξ [ρ] #n        => if n < size ρ then (h (nth ⌊0⌋ ρ n)).+1 else 0
  | ξ [ρ] (t1 · t2) => (h (ξ [ρ] t1 ○ ξ [ρ] t2)).+1
  | ξ [ρ] (λ [u])   => (h (λλ [ξ [^(size ρ) :: ρ] u])).+1
  end.
Proof.
rewrite unlock; elim/clind: c => // t ρ _ /=.
elim: t ρ => /= [n|t1 ih1 t2 ih2|t iht] ρ.
+ rewrite size_map; case: ltnP => // lt.
  by rewrite (nth_map ⌊0⌋) // unlock.
+ by rewrite !(ih1, ih2).
+ by rewrite {1}[X in X :: _](_ : 0 = h (^(size ρ))) ?unlock.
Qed.

Fixpoint ht hs t :=
  match t with
  | #n =>
    if n < size hs then (nth 0 hs n).+1 else 0
      
  | λ [t'] =>
    (ht (0 :: hs) t').+2
      
  | t1 · t2 =>
    (ht hs t1 + ht hs t2).+2
  end.

Lemma hcE c : h c =
  match c with
  | ^n      => 0%N
  | ⌊n⌋     => 0%N
  | c1 ○ c2 => (h c1 + h c2).+1
  | λλ [c]  => (h c).+1
  | ξ [ρ] t => ht [seq h c | c <- ρ] t
  end.
Proof. by rewrite unlock; elim/clind: c. Qed.

(* -------------------------------------------------------------------- *)
Section HInd.
Variable (P : closure -> Prop).

Hypothesis (ih : forall c, (forall c', h c' < h c -> P c') -> P c).

Lemma hind c : P c.
Proof.
suff H: forall n, forall c, h c <= n -> P c by apply (H (h c)).
elim=> {c} [|n ihn] c hcE; apply/ih.
+ by move=> c'; rewrite leqn0 in hcE; rewrite (eqP hcE).
by move=> c' lt; apply/ihn; rewrite -ltnS (@leq_trans (h c)).
Qed.
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

Lemma eq_capps_grdI n1 n2 cs1 cs2 : ⌊n1⌋ ○! cs1 = ⌊n2⌋ ○! cs2 ->
  n1 = n2 /\ cs1 = cs2.
Proof.
elim/last_ind: cs1 cs2 => [|cs1 c1 ih] cs2.
+ by elim/last_ind: cs2 => /= [[//]|cs2 c2 _]; rewrite CAppS_rcons.
elim/last_ind: cs2 => /= [|cs2 c2 _]; first by rewrite CAppS_rcons.
by rewrite !CAppS_rcons => -[/ih[-> ->] ->].
Qed.

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

Lemma closure_of_term_appS t ts :
  closure_of_term (t ·! ts) =
  closure_of_term t ○! [seq closure_of_term u | u <- ts].
Proof.
elim/last_ind: ts => // us u ih; rewrite !(AppS_rcons, CAppS_rcons).
by rewrite /= ih !map_rcons CAppS_rcons.
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
Inductive wf : seq closure -> nat -> Prop :=
| WFEmpty:
    forall l, wf [::] l

| WFTerm:
    forall i j t ρt l ρ, i <= j
     -> j <= l
     -> wf ρt i
     -> wf ρ j
     -> wf (ξ [ρt] t :: ρ) l

| WFFormal:
    forall i l ρ, wf ρ i
     -> i.+1 <= l
     -> wf (^i.+1 :: ρ) l.

(* -------------------------------------------------------------------- *)
Lemma wf_strg ρ l l' : l <= l' -> wf ρ l -> wf ρ l'.
Proof.
move=> le_ll' wf1. elim: wf1 l' le_ll' => {ρ l}. try by ctor.
+ move=> i j t ρt l ρ le_ij le_jl wft iht wf ih l' le_ll'.
  have le_jl': j <= l'. by apply/(leq_trans le_jl).
  have leᵢ_il': i <= l'. by apply/(leq_trans le_ij).
  apply/(@WFTerm i j _ _ l' _). apply/le_ij. apply/le_jl'. apply/wft. by apply/wf.
+ move=> i l ρ wf ih lt_il l' le_ll'.
  apply/(@WFFormal i l' _). apply/wf.
  apply/(@leq_trans l). apply/lt_il. by apply le_ll'.
Qed.

(* -------------------------------------------------------------------- *)
Lemma wf_term ρt t ρ l:
  wf (ξ [ρt] t :: ρ) l ->
    exists2 i, i <= l & wf ρ i.
Proof.
set cs := _ :: _; move: {-2}cs (erefl cs); rewrite {}/cs.
move=> cs csE wf1; elim: wf1 csE => // {cs l}.
+ move=> i j t' ρt' l ρ' lt_ij lt_jl h1 _ h2 _ [_ _ <-]; exists l. trivial.
  apply/(@wf_strg _ j _). trivial. by apply/h2.
Qed.

(* -------------------------------------------------------------------- *)
Lemma wf_term_sub ρt t ρ l:
  wf (ξ [ρt] t :: ρ) l ->
    exists2 i, i <= l & wf ρt i.
Proof.
set cs := _ :: _; move: {-2}cs (erefl cs); rewrite {}/cs.
move=> cs csE wf1; elim: wf1 csE => // {cs l}.
+ move=> i j t' ρt' l ρ' lt_ij lt_jl h1 _ h2 _ [_ <- _].
  have lt_il: i <= l. by apply/(leq_trans lt_ij).
  by exists i => //.
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
+ move=> i j t pt l' ρ' le_ij le_jl' wf_pt IHpt wfρ' IHρ'; rewrite inE.
  have wf_pt_l': wf pt l'. apply/(@wf_strg _ i).
  by apply/(leq_trans le_ij). apply/wf_pt.
  case/orP. move/eqP=> ->. right. by exists t, pt, l'.
  move=> c_ρ. case (@IHρ' c_ρ).
  * left. case H=> i0 [ci lt_i0j]. exists i0. apply ci.
    apply/(leq_trans lt_i0j). apply/le_jl'.
  * right. case H=> T [ρ0] [l0] [cE wf_ρ0 le_l'j]. exists T, ρ0, l0.
    split. apply/cE. apply/wf_ρ0. apply/(leq_trans le_l'j). apply/le_jl'.
+ move=> i l' ρ' wfρ' IHρ' lt_il'; rewrite inE.
  case/orP. move/eqP=> ->. left. exists i. trivial. by apply/lt_il'.
  move=> c_ρ. case (@IHρ' c_ρ).
  * left. case H=> i0 [ci lt_i0i]. exists i0. apply ci.
    apply/(leq_trans lt_i0i). apply/ltnW. apply/lt_il'.
  * right. case H=> T [ρ0] [l0] [cE wf_ρ0 le_l0i]. exists T, ρ0, l0.
    split. apply/cE. apply/wf_ρ0. apply/(leq_trans le_l0i). apply ltnW. apply/lt_il'.
Qed.

(* -------------------------------------------------------------------- *)
Lemma wfc_strg_clos ρ l i n:
  wf ρ l -> i <= l -> n < size ρ -> wfc i (nth ^0 ρ n) -> wfc l (nth ^0 ρ n).
Proof.
+ move=> wf1 le_il n_size_ρ wf2; set c := (nth ^0 ρ n).
  have cρ: c \in ρ by rewrite mem_nth // -subSn // leq_subLR.
  case (mem_wf wf1 cρ).
  * by case=> i' -> lt_i'l; apply/WFCLvl/lt_i'l.
  * case=> T [ρ'] [l'] [cE wf_ρ'_l' le_l'_l0]; rewrite cE.
    apply/WFCClos/(@wf_strg _ l'). apply/le_l'_l0. apply/wf_ρ'_l'.
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
        rewrite !(addn0, add0n) /= => -> //; case/wf_term_sub: wfρ.
        by move=> k le_kl0 wfρ; apply/(@wf_strg _ k).
      + case: n lt_n_mDSρ => // n; rewrite addnS ltnS.
        move=> lt_n_mDρ lt_m_Sn; rewrite !nth_cat !size_μ ltnNge ltnW //=.
        rewrite subSn //=; set c := nth _ _ _; have cρ: c \in ρ.
          by rewrite mem_nth // -subSn // leq_subLR.
        have wf'ρ: wf ρ l0; first case/wf_term: wfρ.
          by move=> k le_kl0; apply/(@wf_strg _ k).
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
Fixpoint IsNeutral (t : term) :=
  match t with
  | #_ => true
  | t · _ => IsNeutral t
  | _ => false
  end.

(* -------------------------------------------------------------------- *)
Lemma IsNeutralVar x ts : IsNeutral (#x ·! ts).
Proof.
elim/last_ind: ts => // ts t ih.
by rewrite AppS_rcons /= ih.
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsNeutralP t :
  reflect (exists n ts, t = #n ·! ts) (IsNeutral t).
Proof.
apply: (iffP idP) => [|[x] [ts] ->]; last by apply/IsNeutralVar.
elim: t => // [n _|t1 ih1 t2 ih2]; first by exists n, [::].
move/ih1 => [x] [ts] ->; exists x, (rcons ts t2).
by rewrite AppS_rcons.
Qed.

(* -------------------------------------------------------------------- *)
Inductive IsWhnf : term -> Prop :=
| IsWhnfLam : forall t, IsWhnf (λ [t])
| IsWhnfVar : forall x ts, IsWhnf (#x ·! ts).

Fixpoint is_varapp t :=
  match t with #x => true | t · _ => is_varapp t | _ => false end.

Definition iswhnf t :=
  if t is λ [_] then true else is_varapp t.

Lemma is_varappP t :
  is_varapp t -> exists x ts, t = #x ·! ts.
Proof.
elim: t => [n|t1 ih1 t2 ih2|t ih] //=.
+ by move=> _; exists n, [::].
+ move/ih1=> [x] [ts] => ->; exists x, (rcons ts t2).
  by rewrite AppS_rcons.
Qed.

Lemma IsWhnfP t : reflect (IsWhnf t) (iswhnf t).
Proof.
apply: (iffP idP).
+ case: t => //= [n _|t1 t2 hap|t]; try by constructor.
  - by apply: (IsWhnfVar _ [::]).
  move/is_varappP: hap => [x] [ts] ->.
  by rewrite -AppS_rcons; constructor.
+ case=> {t} [t|x ts] //; elim/last_ind: ts => // us u ih.
  rewrite AppS_rcons /=; move: ih; rewrite /iswhnf.
  by elim/last_ind: us => // s y _; rewrite AppS_rcons.
Qed.

Lemma whnf_dec t : IsWhnf t \/ ~ IsWhnf t.
Proof. by case/boolP: (iswhnf t) => /IsWhnfP; tauto. Qed.

(* -------------------------------------------------------------------- *)
Inductive IsNf : term -> Prop :=
| IsNfLam : forall t, IsNf t -> IsNf (λ [t])
| IsNfVar : forall x ts, (forall t, t \in ts -> IsNf t) -> IsNf (#x ·! ts).

(* -------------------------------------------------------------------- *)
Inductive IsWhnfC : closure -> Prop :=
| IsWhnfCLam : forall c, IsWhnfC (λλ [c])
| IsWhnfCVar : forall n cs, IsWhnfC (⌊n⌋ ○! cs).

(* -------------------------------------------------------------------- *)
Inductive IsNfC : closure -> Prop :=
| IsNfCLam : forall c, IsNfC c -> IsNfC (λλ [c])
| IsNfCVar : forall n cs, (forall c, c \in cs -> IsNfC c) -> IsNfC (⌊n⌋ ○! cs).

(* -------------------------------------------------------------------- *)
Inductive IsStc : closure -> Prop :=
| Stc1 n : IsStc ⌊n⌋

| Stc2 n (ρts : seq (seq closure * term)) :
    IsStc (^n ○! [seq ξ[ρt.1] ρt.2 | ρt <- ρts])

| Stc3 ρ t (ρts : seq (seq closure * term)) :
    IsStc (ξ [ρ] t ○! [seq ξ[ρt.1] ρt.2 | ρt <- ρts])

| Stc4 c :
    IsStc c -> IsStc (λλ [c])

| Stc5 n nfc c ρts :
    let cs := [seq ξ [ρt.1] ρt.2 | ρt <- ρts] in
       IsStc c
    -> (forall nf, nf \in nfc -> IsNfC nf)
    -> IsStc (⌊n⌋ ○! nfc ○ c ○! cs).

(* -------------------------------------------------------------------- *)
Inductive IsExc : nat -> closure -> Prop :=
| Exc1 n ρ t1 ρts :
    let cs := [seq ξ [ρt.1] ρt.2 | ρt <- ρts] in
    size ρts != 0 -> IsExc n ((λλ [ξ [^n.+1 :: ρ] t1]) ○! cs)

| Exc2 n c :
    IsExc n.+1 c -> IsExc n (λλ [c])

| Exc3 n p nfc c ρts :
    let cs := [seq ξ [ρt.1] ρt.2 | ρt <- ρts] in
       IsExc p c
    -> (forall nf, nf \in nfc -> IsNfC nf)
    -> IsExc p (⌊n⌋ ○! nfc ○ c ○! cs).

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
move=> nf r; elim/last_ind: us => [|us u ih] //=.
  apply/Noν => //; first by apply/IsNfVar.
  by elim/last_ind: {nf} ts => // zs z ih; rewrite AppS_rcons.
rewrite !AppS_rcons; apply/Noμ2 => //.
+ by rewrite -!(AppS_rcons, AppS_cat); apply/IsWhnfVar.
+ by rewrite -!(AppS_rcons, AppS_cat); apply/IsNeutralVar.
Qed.

(* -------------------------------------------------------------------- *)
Derive Inversion_clear beta_var
  with (forall x t, #x ⇀_β t)
  Sort Prop.

Derive Inversion_clear nobeta_var
  with (forall x t, #x → t)
  Sort Prop.

Lemma NoVar x t: ~ (#x → t).
Proof.
by inversion 1 using nobeta_var; inversion 1 using beta_var.
Qed.

(* -------------------------------------------------------------------- *)
Derive Inversion_clear nobeta_lam
  with (forall t u, λ [t] → u)
  Sort Prop.

Lemma NoLam t u : λ [t] → u ->
  exists t', t → t' /\ u = λ [t'].
Proof.
by inversion 1 using nobeta_lam; [inversion 1 | eauto].
Qed.

(* -------------------------------------------------------------------- *)
Fixpoint IsNeutralC (c : closure) :=
  match c with
  | ⌊_⌋ => true
  | c ○ _ => IsNeutralC c
  | _ => false
  end.

(* -------------------------------------------------------------------- *)
Lemma IsNeutralCP (c : closure) :
  reflect
    (exists n, exists cs, c = ⌊n⌋ ○! cs)
    (IsNeutralC c).
Proof.
apply: (iffP idP); last first.
+ case=> [n] [cs] ->; elim/last_ind: cs => // cs c' ih.
  by rewrite CAppS_rcons /= ih.
elim: c => // [n _|c1 ih1 c2 ih2]; first by exists n, [::].
move/ih1 => [n] [cs] ->; exists n, (rcons cs c2).
by rewrite CAppS_rcons.
Qed.

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
| TBeta: forall l t u ρ1 ρ2,
    (λλ [ξ[^l.+1 :: ρ1] t]) ○ (ξ [ρ2] u)
      ⇀_[β, l] (ξ [ξ [ρ2] u :: ρ1] t)

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

(* -------------------------------------------------------------------- *)
Lemma wfc_rho1 c1 c2 l : wfc l c1 -> c1 →_[ρ,l] c2 -> wfc l c2.
Proof.
move=> wfc1 r; elim: r wfc1 => {l c1 c2} l; first last.
+ by move=> c c' _ ih; rev/wfc_lam => /ih w; ctor.
+ by move=> c1 c2 c2' _ _ _ ih; rev/wfc_app => w1 /ih w2; ctor.
+ by move=> c1 c1' c2 _ _ _ ih; rev/wfc_app => /ih w1 w2; ctor.
+ by move=> c1 c1' c2 _ _ ih; rev/wfc_app=> /ih w1 w2; ctor.
move=> c1 c2 [] {c1 c2 l} l =>[n|t u|t u|t|n]; try by ctor.
+ move=> ρ ltn; rev/wfc_clos => wf1; elim: wf1 n ltn => {ρ} //=.
  * move=> i j t ρt l' ρ lt_ij lt_jl' wfρt iht wfρ ih [_|k] /=; last first.
    rewrite ltnS. move=> k_ρ'. move:(@ih k k_ρ'). apply/wfc_strg_clos.
    apply/(@wf_strg _ j). apply/lt_jl'. apply/wfρ. apply/lt_jl'. apply/k_ρ'.
    ctor. apply/(@wf_strg _ i). apply/(leq_trans lt_ij). apply lt_jl'. apply/wfρt.
  * move=> i l' ρ wf1 ih lt_il' [_|k] /=.
    by ctor. rewrite ltnS. move=> k_ρ'. move:(@ih k k_ρ'). apply/wfc_strg_clos.
      apply/(@wf_strg _ i). apply/ltnW/lt_il'. apply/wf1.
      apply/ltnW/lt_il'. apply/k_ρ'.
+ by move=> ρ; rev/wfc_clos=> wf1; do 2! ctor.
+ move=> ρ; rev/wfc_clos=> wf1; do 2! ctor.
  apply/WFFormal. apply/wf1. apply ltnSn.
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

Derive Inversion_clear inv_nored_beta_var_r
  with (forall n t, #n → t)
  Sort Prop.

Lemma inv_noredbeta_lam t u :
  λ [t] → u -> exists t', [/\ t → t' & u = λ [t']].
Proof.
inversion 1 using inv_nored_beta_lam_r.
+ by inversion 1. + by eauto.
Qed.

Lemma inv_noredbeta_var n t : ~ (#n → t).
Proof.
by inversion 1 using inv_nored_beta_var_r; inversion 1.
Qed.

(* -------------------------------------------------------------------- *)
Lemma inv_redX3_rhd l n (nfc : seq closure) M :
    (forall nf, nf \in nfc -> IsNfC nf)
  -> ~ (⌊n⌋ ○! nfc →_[β,l] M).
Proof.
elim/last_ind: nfc M => /= [|nfc nf ih] M h.
  by rev/rwb_grd; rev/rwb1_grd.
rewrite CAppS_rcons; rev/rwb_app; first rev/rwb1_app.
+ move=> _ _ t u ρ1 ρ2 _ eq; absurd False => //; move: eq.
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
  + move=> _ _ t u ρ1 ρ2 _; elim/last_ind: cs {ihcs ih} => //.
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
+ move=> _ _ t u ρ1 ρ2 _ eq; absurd False => //; move: eq.
  by elim/last_ind: nfc {h} => // zs z; rewrite CAppS_rcons.
+ by move=> c1' h'; absurd False => //; apply/h'; ctor.
+ by move=> c1'_ _ _ /inv_redX3_rhd -/(_ h).
+ by move=> c2' _ _ r; exists c2'.
Qed.

(* -------------------------------------------------------------------- *)
Lemma inv_redX3 l n (nfc : seq closure) c ρts M :
  let cs := [seq ξ [ρt.1] ρt.2 | ρt <- ρts] in
    (forall nf, nf \in nfc -> IsNfC nf)
  -> ⌊n⌋ ○! nfc ○ c ○! cs →_[β,l] M
  -> exists2 M', M = ⌊n⌋ ○! nfc ○ M' ○! cs & c →_[β,l] M'.
Proof.
move=> cs h; rewrite {}/cs; elim/last_ind: ρts M => [|ts t ih] M.
  by move/inv_redX3_r => /(_ h).
rewrite map_rcons CAppS_rcons; rev/rwb_app.
+ rev/rwb1_app=> _ _ t' u' ρ1' ρ2' _ eq; absurd False => //.
  move: eq; rewrite -CAppS_rcons -CAppS_cat; move: (_ ++ _).
  by elim/last_ind=> //= z zs _; rewrite CAppS_rcons.
+ move=> c1'; rewrite -CAppS_rcons -CAppS_cat; move: (_ ++ _) => cs.
  by move=> whnf; absurd False => //; apply/whnf; ctor.
+ by move=> c1' => h1 h2 /ih [M' ->] r; exists M' => //; rewrite CAppS_rcons.
+ by move=> c2' _ _ /rwb_clos.
Qed.

(* -------------------------------------------------------------------- *)
Derive Inversion_clear ρ_closI
  with (forall ρ t l c, ξ [ρ] t →_[ρ,l] c)
  Sort Prop.

Derive Inversion_clear ρ_appI
  with (forall c1 c2 l c, c1 ○ c2 →_[ρ,l] c)
  Sort Prop.

Derive Inversion_clear ρ_idxI
  with (forall i c l, ^i →_[ρ,l] c).

Derive Inversion_clear ρ1_closfreevarI
  with (forall ρ x l c, ξ [ρ] #x ⇀_[ρ,l] c)
  Sort Prop.

Derive Inversion_clear ρ1_closappI
  with (forall ρ t1 t2 l c, ξ [ρ] (t1 · t2) ⇀_[ρ,l] c)
  Sort Prop.

Derive Inversion_clear ρ1_closlamI
  with (forall ρ t l c, ξ [ρ] (λ [t]) ⇀_[ρ,l] c)
  Sort Prop.

Derive Inversion_clear ρ1_closI
  with (forall ρ t l c, ξ [ρ] t ⇀_[ρ,l] c)
  Sort Prop.

Derive Inversion_clear ρ1_idxI
  with (forall i c l, ^i ⇀_[ρ,l] c).

(* -------------------------------------------------------------------- *)
Derive Inversion_clear IsNfCI with (forall c, IsNfC c) Sort Prop.
Derive Inversion_clear IsWhnfCI with (forall c, IsWhnfC c) Sort Prop.

(* -------------------------------------------------------------------- *)
Derive Inversion IsNfC_lblI
  with (forall i, IsNfC ^i)
  Sort Prop.

Lemma NIsNfC_lbl i : ~ IsNfC ^i.
Proof.
elim/IsNfC_lblI => _ n cs _; elim/last_ind: cs => //.
by move=> cs c _; rewrite CAppS_rcons.
Qed.

(* -------------------------------------------------------------------- *)
Derive Inversion IsNfC_appI
  with (forall c1 c2, IsNfC (c1 ○ c2))
  Sort Prop.

Lemma NIsNfC_closappI ρ t c : ~ (IsNfC ((ξ [ρ] t) ○ c)).
Proof.
elim/IsNfC_appI=> _ n cs _; elim/last_ind: cs c => //.
move=> cs c' _ c; rewrite CAppS_rcons => -[].
by elim/last_ind: cs => // cs c'' _; rewrite CAppS_rcons.
Qed.

(* -------------------------------------------------------------------- *)
Derive Inversion IsNfC_lamI
  with (forall c, IsNfC (λλ [c]))
  Sort Prop.

(* -------------------------------------------------------------------- *)
Derive Inversion IsNfC_closI
  with (forall ρ t, IsNfC (ξ [ρ] t))
  Sort Prop.

Lemma NIsNfC_clos ρ t : ~ IsNfC (ξ [ρ] t).
Proof.
elim/IsNfC_closI => _ n cs _; elim/last_ind: cs => //.
by move=> cs c _; rewrite CAppS_rcons.
Qed.

(* -------------------------------------------------------------------- *)
Lemma ρ_clos ρ t l : exists c, ξ [ρ] t →_[ρ,l] c.
Proof.
case: t => [n|t1 t2|t]; first case: (ltnP n (size ρ)) => h.
+ by eexists; apply/NoCBase/RhoRedVar.
+ by eexists; apply/NoCBase/RhoRedFree.
+ by eexists; apply/NoCBase; econstructor.
+ by eexists; apply/NoCBase; econstructor.
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsNfC_IsEph c : IsNfC c -> is_ephemeral c.
Proof.
elim=> // n; elim/last_ind=> // cs c' ih h1 h2.
rewrite CAppS_rcons /=; rewrite ih ?h2 //.
* by rewrite mem_rcons mem_head.
* by move=> c'' c''in; apply/h1; rewrite mem_rcons mem_behead.
* by move=> c'' c''in; apply/h2; rewrite mem_rcons mem_behead.
Qed.

(* -------------------------------------------------------------------- *)
Lemma L_5_11 l (S S' : closure) (t : term) :
     IsStc S -> ~ IsWhnfC S -> IsWhnf t
  -> wfc l S -> σc S l = t :> term -> S →_[ρ,l] S'
  -> (IsStc S' /\ (IsNfC S' -> S' = t :> term)).
Proof.
elim/hind: S S' t => S ih S' t h; elim: h ih=> [n|n|||].
+ by move=> _ []; apply/(IsWhnfCVar _ [::]).

+ move=> ρts _ _ wft hwf /=; set a := map _ _.
  have: ^n ○! a →_[ρ,l] S' ->
    exists2 c', ^n →_[ρ,l] c' & S' = c' ○! a.
  + rewrite {}/a; elim/last_ind: {+}ρts S' => //=.
    * move=> S'; elim/ρ_idxI; elim/ρ1_idxI.
      by eexists; try reflexivity; do 2! constructor.
    move=> ρts' ρt' ih' S1'; rewrite map_rcons CAppS_rcons.
    (elim/ρ_appI; first by inversion 1); first last.
    * move=> x h; absurd False => // {x}; move: h.
      set Z := (_ ○! _) => h; move: (erefl Z).
      rewrite {2}/Z; elim/IsNfCI: h => //.
      - move=> c' _; elim/last_ind: {+}ρts => //.
        elim/last_ind: {+}ρts' => // ρts'' ρt'' _.
        by rewrite map_rcons CAppS_rcons.
      - move=> n' cs _; elim/last_ind: {+}ρts' cs => /=.
        + by elim/last_ind => // cs' c' _; rewrite CAppS_rcons.
        + move=> ρts'' ρt'' ih''; elim/last_ind => //=.
          - by rewrite map_rcons CAppS_rcons.
          - move=> cs' c' _; rewrite map_rcons !CAppS_rcons.
            by case=> /ih''.
    * move=> x h; absurd False => // {x}; move: h.
      set Z := (_ ○! _) => h; move: (erefl Z).
      rewrite {2}/Z; elim/IsWhnfCI: h => //.
      - move=> c; elim/last_ind: {+}ρts => //.
        elim/last_ind: {+}ρts' => // ρts'' ρt'' _.
        by rewrite map_rcons CAppS_rcons.
      - move=> n' cs; elim/last_ind: {+}ρts' cs => /=.
        + by elim/last_ind => // cs' c' _; rewrite CAppS_rcons.
        + move=> ρts'' ρt'' ih''; elim/last_ind => //=.
          - by rewrite map_rcons CAppS_rcons.
          - move=> cs' c' _; rewrite map_rcons !CAppS_rcons.
            by case=> /ih''.
    * move=> c1' _ /ih' [c' h6 h7]; exists c' => //.
      by rewrite CAppS_rcons h7.
  move=> h6 h7 h8; have := h6 h8 => -[c' rd ->].
  elim/ρ_idxI: rd; elim/ρ1_idxI; split.
  * rewrite /a; case: {+}ρts => /=; first constructor.
    move=> c'' cs'; apply/(@Stc5  _ [::]) => //.
    by apply/(Stc3 _ _ [::]).
  * subst a; rewrite -h7; elim/last_ind: {+}ρts => /=.
    - by move=> _; rewrite scE.
    move=> ρts'' ρt'' _; set Z := (_ ○! _) => h; move: (erefl Z).
    rewrite {2}/Z; elim/IsNfCI: h => //.
    - by move=> c'' _; rewrite map_rcons CAppS_rcons.
    - move=> n' cs h; elim/last_ind: cs h => /=.
      + by rewrite map_rcons CAppS_rcons.
      move=> cs'' c'' _ h; rewrite map_rcons !CAppS_rcons.
      case=> _ ?; subst c''; absurd False => //.
      move/(_ (ξ [ρt''.1] ρt''.2)): h.
      rewrite mem_rcons mem_head => -/(_ (erefl true)).
      by move/IsNfC_IsEph.
+ move=> ρ u; elim/last_ind =>  [|ρts ρt _] ih h1 h2 /= hwf tE; rewrite -tE.
  * case: {ih tE h1 h2} u hwf => [n|u1 u2|u].
    - move=> hwf; elim/ρ_closI; elim/ρ1_closfreevarI => h.
      + rewrite scE h; elim/wfc_clos: hwf.
        move/mem_wf => /(_ _ (mem_nth _ h)) -/(_ ^0).
        case=> [[i] -> _|[v] [ρ'] [l'] [-> _ _]].
        * by split; [apply/(@Stc2 _ [::]) | case/NIsNfC_lbl].
        * split; first by apply/(@Stc3 _ _ [::]).
          by case/NIsNfC_clos.
      + split; first by constructor.
          by rewrite scE ltnNge h.
    - move=> _; elim/ρ_closI; elim/ρ1_closappI; split.
      + by apply/(@Stc3 _ _ [:: (ρ, u2)]).
      + by case/NIsNfC_closappI.
    - move=> _; elim/ρ_closI; elim/ρ1_closlamI; split.
      + by constructor; apply/(@Stc3 _ _ [::]).
      + elim/IsNfC_lamI.
        * by move=> _ ?; case/NIsNfC_clos.
        * move=> _ n cs _; elim/last_ind: cs => // cs c' _.
          by rewrite CAppS_rcons.
  * move: hwf h1 h2; rewrite map_rcons CAppS_rcons.
    set S1 := _ ○! _ => hwf h1 h2 h; rewrite scE.
    (elim/ρ_appI: h; first by inversion 1); first last.
    + move=> x nfc1 _ _; absurd False => // {x}.
      - move: (erefl S1); rewrite {2}/S1; elim/IsNfCI: nfc1.
        + move=> c' _; elim/last_ind: {+}ρts => // ρts' ρt' _.
          by rewrite map_rcons CAppS_rcons.
        + move=> n cs _; elim/last_ind: cs {ih tE S1 hwf h1 h2} ρts => /=.
          * move=> ρts /=; elim/last_ind: ρts => // ρts ρt' _.
            by rewrite map_rcons CAppS_rcons.
          * move=> cs c' ih' ρts; rewrite CAppS_rcons.
            elim/last_ind: ρts => [|ρts ρt' _] //.
            by rewrite map_rcons CAppS_rcons => -[/ih'].
      - move=> x nfc1 _ _; absurd False => // {x}.
        move: (erefl S1); rewrite {2}/S1; elim/IsWhnfCI: nfc1.
        + move=> c'; elim/last_ind: {ih tE S1 hwf h1 h2} ρts => //.
          by move=> ρts ρt' _; rewrite map_rcons CAppS_rcons.
        + move=> n cs; elim/last_ind: cs {ih tE S1 hwf h1 h2} ρts.
          * move=> ρts /=; elim/last_ind: ρts => // ρts ρt' _.
            by rewrite map_rcons CAppS_rcons.
          * move=> cs c' ih' ρts; rewrite CAppS_rcons.
            elim/last_ind: ρts => [|ρts ρt' _] //.
            by rewrite map_rcons CAppS_rcons => -[/ih'].
      - move=> S1' h3 rd; move: tE; rewrite sc_appS.
        rewrite !map_rcons /= CAppS_rcons /= !c2tE.
        case: t h2 => // t1 t2 h2 [t1E t2E].
        elim: (ih S1 _ S1' t1) => //; first last.
        + by rewrite /S1 /= sc_appS.
        + by inversion hwf.
        + apply/IsWhnfP; move/IsWhnfP: h2 => /=.
          by case: {t1E} t1 => //.
        + by constructor.
        + rewrite /S1 map_rcons CAppS_rcons [X in _ < X]hE.
          by rewrite ltnS leq_addr.
        + move=> h4 h5; split.
          - move: rd; rewrite /S1; set a := map _ _.
            have: ξ [ρ] u ○! a →_[ρ,l] S1' ->
              exists2 c', ξ [ρ] u →_[ρ,l] c' & S1' = c' ○! a.
            + rewrite {}/a; elim/last_ind: {+}ρts {h4 h5} S1' => //=.
              * by case: (ρ_clos ρ u l) => c' h; eexists; try eassumption.
              move=> ρts' ρt' ih' S1'; rewrite map_rcons CAppS_rcons.
              (elim/ρ_appI; first by inversion 1); first last.
              * move=> x h; absurd False => // {x}; move: h.
                set Z := (_ ○! _) => h; move: (erefl Z).
                rewrite {2}/Z; elim/IsNfCI: h => //.
                - move=> c' _; elim/last_ind: {+}ρts => //.
                  elim/last_ind: {+}ρts' => // ρts'' ρt'' _.
                  by rewrite map_rcons CAppS_rcons.
                - move=> n cs _; elim/last_ind: {+}ρts' cs => /=.
                  + by elim/last_ind => // cs' c' _; rewrite CAppS_rcons.
                  + move=> ρts'' ρt'' ih''; elim/last_ind => //=.
                    - by rewrite map_rcons CAppS_rcons.
                    - move=> cs' c' _; rewrite map_rcons !CAppS_rcons.
                      by case=> /ih''.
              * move=> x h; absurd False => // {x}; move: h.
                set Z := (_ ○! _) => h; move: (erefl Z).
                rewrite {2}/Z; elim/IsWhnfCI: h => //.
                - move=> c; elim/last_ind: {+}ρts => //.
                  elim/last_ind: {+}ρts' => // ρts'' ρt'' _.
                  by rewrite map_rcons CAppS_rcons.
                - move=> n cs; elim/last_ind: {+}ρts' cs => /=.
                  + by elim/last_ind => // cs' c' _; rewrite CAppS_rcons.
                  + move=> ρts'' ρt'' ih''; elim/last_ind => //=.
                    - by rewrite map_rcons CAppS_rcons.
                    - move=> cs' c' _; rewrite map_rcons !CAppS_rcons.
                      by case=> /ih''.
              * move=> c1' _ /ih' [c' h6 h7]; exists c' => //.
                by rewrite CAppS_rcons h7.
            move=> h6 h7; have := h6 h7 => -[c' rdc' E]; rewrite E.
            elim/ρ_closI: rdc' {h6} h7 E t1E; elim/ρ1_closI.
            + move=> n lt _ _ _; elim/wfc_app: hwf => hwf _.
              move/wfc_appsl: hwf; elim/wfc_clos => /mem_wf.
              move=> /(_ _ (mem_nth _ lt)) -/(_ ^0) -[].
              - case=> i -> _; have := Stc2 i.+1 (rcons ρts (ρt.1, ρt.2)).
                by rewrite map_rcons /= -/a -CAppS_rcons.
              - case=> [t] [ρ'] [_] [-> _ _].
                have := Stc3 ρ' t (rcons ρts (ρt.1, ρt.2)).
                by rewrite map_rcons /= -/a -CAppS_rcons.
            + move=> n _ _ _ _; rewrite -CAppS_rcons /a -map_rcons.
              rewrite headI map_cons CAppS_cons; apply/(@Stc5 _ [::]) => //.
              by apply/(@Stc3 _ _ [::]).
            + move=> t' u' _ _ _; rewrite -CAppS_cons -CAppS_rcons.
              rewrite /a -(map_cons _ (ρ, u')) -map_rcons.
              by apply/Stc3.
            + move=> t' h7 S1'E t1E; absurd False => //.
              move: h2; rewrite -t1E 2!scE c2t_appS.
              inversion 1 => //; move: H0; elim/last_ind: ts => //.
              move=> ts t _; rewrite AppS_rcons; case.
              move=> h; absurd False => //; move: h.
              elim/last_ind: {+}ρts ts => [|ρts' ρt' ih'] ts.
              - elim/last_ind: ts => //=; first by rewrite c2tE.
                by move=> ts t'' _; rewrite AppS_rcons c2tE.
              - elim/last_ind: ts => [|ts t'' _] /=.
                + by rewrite !map_rcons !c2tE AppS_rcons.
                + rewrite AppS_rcons !map_rcons !c2tE AppS_rcons.
                  by case=> h; case/(_ ts): ih'; rewrite !c2tE.
            + by move/IsNfC_IsEph => /=; rewrite andbF.
+ by move=> c _ _ _ h; absurd False => //; apply/h; constructor.
+ move=> n cs c ρts csE _ _ _ _ [].
  by rewrite -CAppS_rcons -CAppS_cat; constructor.
Qed.

(* -------------------------------------------------------------------- *)
Lemma h_closure_eq ρ1 ρ2 t :
  [seq h x | x <- ρ1] = [seq h x | x <- ρ2]
  -> h (ξ [ρ1] t) = h (ξ [ρ2] t).
Proof.
elim: t ρ1 ρ2 => [n|t1 ih1 t2 ih2|t iht] ρ1 ρ2 eq /=.
+ have eqsz: size ρ1 = size ρ2.
  - by move/(congr1 size): eq; rewrite !size_map => ->.
  rewrite ![h (ξ [_] #_)]hE; rewrite eqsz; case: ifPn => //.
  move=> ltn2; have ltn1: n < size ρ1 by rewrite eqsz.
  by move/(congr1 ((nth 0)^~ n)): eq; rewrite !(nth_map ⌊0⌋) // => ->.
+ by rewrite 2!hE (ih1 _ _ eq) (ih2 _ _ eq) // !hE.
+ rewrite [LHS]hE [RHS]hE ![h (λλ [_])]hE; congr _.+2.
  by apply/iht => /=; rewrite !hE eq.
Qed.

(* -------------------------------------------------------------------- *)
Derive Inversion_clear NoRed_app_r
  with (forall t u v, t · u → v)
  Sort Prop.

Derive Inversion inv_beta
  with (forall t u v, t · u ⇀_β v)
  Sort Prop.

Lemma IsNf_nf t : IsNf t -> forall u, ~ t → u.
Proof.
elim=> {t} [t _ ih|n ts _ ih].
+ by move=> u /inv_noredbeta_lam[t' [/ih]].
+ move=> u rd; elim/last_ind: ts u ih rd => /= [|ts t ihts] u ih.
  - by move=> /inv_noredbeta_var.
  rewrite AppS_rcons; inversion 1 using NoRed_app_r.
  - move=> {rd} rd; inversion rd using inv_beta.
    move=> {rd} _ t' u'; elim/last_ind: ts {ihts ih} => //.
    by move=> s x _; rewrite AppS_rcons.
  - by move=> t' /(_ (IsWhnfVar _ _)).
  - move=> t' _ _ /ihts; apply => v ints; apply/ih.
    by rewrite mem_rcons in_cons ints orbT.
  - by move=> v _ _; apply/ih; rewrite mem_rcons in_cons eqxx.
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsNfC_IsNf (c : closure) : IsNfC c -> IsNf c.
Proof.
elim=> {c} [c _ h|c cs _ ih]; first by rewrite c2tE; constructor.
rewrite c2t_appS c2tE; constructor.
by move=> t /mapP[c' /ih h ->].
Qed.

(* -------------------------------------------------------------------- *)
Derive Inversion IsWhnfCN_clos_r
  with (forall ρ t, IsWhnfC (ξ [ρ] t))
  Sort Prop.

Lemma IsWhnfCN_clos ρ t : ~ IsWhnfC (ξ [ρ] t).
Proof.
elim/IsWhnfCN_clos_r => _ n; elim/last_ind => //.
by move=> ρs ρ' _; rewrite CAppS_rcons.
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsNfC_grd n : IsNfC ⌊n⌋.
Proof. by apply/(@IsNfCVar _ [::]). Qed.

(* -------------------------------------------------------------------- *)
Derive Inversion IsWhnfC_lvl_r with
  (forall l, IsWhnfC ^l) Sort Prop.

Lemma IsWhnfCN_lvl l : ~ IsWhnfC ^l.
Proof.
inversion 1 using IsWhnfC_lvl_r => _ n.
by elim/last_ind => // cs c _; rewrite CAppS_rcons.
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsNf_AppL t u : IsNf (t · u) -> IsNf t.
Proof.
suff: forall w, IsNf w -> w = t · u -> IsNf t.
+ by move=> h1 h2; apply/(h1 (t · u)).
move=> w h; elim: h t u => //= x ts nf _ t u.
elim/last_ind: ts nf => // ts t' _ nf.
rewrite AppS_rcons => -[<- _]; constructor.
by move=> z h; apply/nf; rewrite mem_rcons mem_behead.
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsNf_AppR t u : IsNf (t · u) -> IsNf u.
Proof.
suff: forall w, IsNf w -> w = t · u -> IsNf u.
+ by move=> h1 h2; apply/(h1 (t · u)).
move=> w h; elim: h t u => //= x ts nf _ t u.
elim/last_ind: ts nf => // ts t' _ nf.
rewrite AppS_rcons => -[_ <-]; apply/nf.
by rewrite mem_rcons mem_head.
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsNf_Lam t : IsNf (λ [t]) -> IsNf t.
Proof.
suff: forall w, IsNf w -> w = λ [t] -> IsNf t.
+ by move=> h1 h2; apply/(h1 (λ [t])).
move=> w h; move: h t; elim.
+ by move=> t nf _ _ -[<-].
+ move=> /= x ts _ _ t; elim/last_ind: ts => //.
  by move=> ts t' _; rewrite AppS_rcons.
Qed.

(* -------------------------------------------------------------------- *)
Derive Inversion IsNfC_grd_apps_r with
  (forall n cs, IsNfC (⌊n⌋ ○! cs)) Sort Prop.

Lemma IsNfC_grd_apps n cs c :
  IsNfC (⌊n⌋ ○! cs) -> c \in cs -> IsNfC c.
Proof.
move=> h; inversion h using IsNfC_grd_apps_r => {h} _.
+ move=> c' _; elim/last_ind: cs => // cs c'' _.
  by rewrite CAppS_rcons => //.
+ by move=> p cs' h /eq_capps_grdI [_ <- /h].
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsStc_AppL c1 c2 : ~ IsNfC c1 -> IsStc (c1 ○ c2) -> IsStc c1.
Proof. move=> h; inversion 1.
+ elim/last_ind: ρts H1 => // cs c _.
  rewrite map_rcons CAppS_rcons => -[<- _].
  by constructor.
+ elim/last_ind: ρts H1 => // cs c _.
  rewrite map_rcons CAppS_rcons => -[<- _].
  by constructor.
+ move: H0; rewrite {}/cs; elim/last_ind: ρts => /=.
  - by case=> ? _; subst c1; case: h; constructor.
  - move=> cs c' _; rewrite map_rcons CAppS_rcons.
    by case=> <- _; apply/@Stc5.
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsStc_AppR c1 c2 : IsStc (c1 ○ c2) -> IsStc c2.
Proof. inversion 1.
+ elim/last_ind: ρts H1 => // c cs _.
  rewrite map_rcons CAppS_rcons => -[_ <-].
  by apply/(@Stc3 _ _ [::]).
+ elim/last_ind: ρts H1 => // c cs _.
  rewrite map_rcons CAppS_rcons => -[_ <-].
  by apply/(@Stc3 _ _ [::]).
+ subst cs; elim/last_ind: ρts H0 => /= [|c' cs _].
  * by case=> _ <-.
  rewrite map_rcons CAppS_rcons => -[_ <-].
  by apply/(@Stc3 _ _ [::]).
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsNfC_AppR c1 c2 : IsNfC (c1 ○ c2) -> IsNfC c2.
Proof.
elim/IsNfC_appI => _ n; elim/last_ind=> // cs c _ ih.
rewrite CAppS_rcons => -[_ <-]; apply/ih.
by rewrite mem_rcons mem_head.
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsNf_IsWhnf t : IsNf t -> IsWhnf t.
Proof. by case=> {t} *; constructor. Qed.

(* -------------------------------------------------------------------- *)
Lemma sc_IsNfC c l : IsNfC c -> sc c l = c.
Proof. move=> h; elim: h l => {c} [c _ cE|n cs _ ih] l.
+ by rewrite scE cE.
+ rewrite sc_appS scE; congr (_ ○! _).
  by rewrite -[RHS]map_id; apply/eq_in_map => c ccs; apply/ih.
Qed.

(* -------------------------------------------------------------------- *)
Lemma NIsNfC_red c l :
 wfc l c -> IsStc c -> ~ IsNfC c -> exists c', c →_[ρ,l] c'.
Proof. elim: c l => [t ρ|n|n|c ih c' ih'|c ih] l.
+ move=> _ _ _; case: t => [p|t1 t2|t].
  * case: (ltnP p (size ρ)) => [lt|ge].
    - by exists (nth ^0 ρ p); do! constructor.
    - by exists ⌊p + l - size ρ⌋; constructor; apply/RhoRedFree/ge.
  * by exists ((ξ [ρ] t1) ○ (ξ [ρ] t2)); do! constructor.
  * by exists (λλ [ξ [^l.+1 :: ρ] t]); do! constructor.
+ by move=> _ _; case; apply/(@IsNfCVar _ [::]).
+ by move=> _ _ _; exists (⌊l-n⌋); do! constructor.
+ move=> h1 h2; move: h1; inversion h2 => h' h''.
  * exists (⌊l - n⌋ ○! [seq ξ [ρt.1] ρt.2 | ρt <- ρts]) => {H0}.
    move=> {h' h''}; elim/last_ind: ρts => /= [|ρts ρt ihr].
    + by do! constructor.
    + rewrite !map_rcons !CAppS_rcons; apply/NoCμ1 => //.
      inversion 1.
      + elim/last_ind: {H ihr} ρts H1 => // ρts ρt' _.
        by rewrite map_rcons CAppS_rcons.
      + elim/last_ind: {H ihr} ρts cs H1 => /= [|ρts ρt' ih''] cs H2.
        * by elim/last_ind: cs H2 => // cs c'' _; rewrite CAppS_rcons.
        * move: H2; rewrite map_rcons CAppS_rcons.
          elim/last_ind: cs => // cs c'' _; rewrite CAppS_rcons.
          by case=> /ih''.
  * case: {H0 h''} t h' => [p|t1 t2|t] h'.
    - elim/last_ind: {h'} ρts => /= [|ρts ρt ih''].
      + case: (ltnP p (size ρ)) => [lt|gt].
        - by exists (nth ^0 ρ p); do! constructor.
        - by exists ⌊p + l - size ρ⌋; constructor; apply/RhoRedFree/gt.
      + case: ih''=> c'' rd; exists (c'' ○ ξ [ρt.1] ρt.2).
        rewrite map_rcons CAppS_rcons; apply/NoCμ1 => //.
Admitted.

Lemma red_NIsNfC c c' l :
 wfc l c -> c →_[ρ,l] c' -> ~ IsNfC c.
Proof. Admitted.

(* -------------------------------------------------------------------- *)
Lemma CAppS_injR n1 n2 cs1 cs2 : ⌊n1⌋ ○! cs1 = ⌊n2⌋ ○! cs2 -> cs1 = cs2.
Proof.
elim/last_ind: cs1 cs2 => /= [|cs1 c1 ih].
+ by elim/last_ind => // cs2 c2 _; rewrite CAppS_rcons.
+ elim/last_ind => //=; first by rewrite CAppS_rcons.
  move=> cs2 c2 _; rewrite !CAppS_rcons.
  by case=> /ih -> ->.
Qed.

(* -------------------------------------------------------------------- *)
Lemma L_5_12 l (S : closure) (t : term) :
     IsStc S -> IsWhnfC S -> ~ IsNfC S -> IsNf t
  -> wfc l S -> σc S l = t :> term ->
     exists S', [/\ S →_[ρ,l] S', IsStc S' &
        (~ IsNfC S' /\ IsWhnfC S')
     \/ (IsNfC S' /\ S' = t :> term)].
Proof. elim: S l t.
+ by move=> t l l' t' _ /IsWhnfCN_clos.
+ by move=> n l t _ _ []; apply/IsNfC_grd.
+ by move=> n l t _ /IsWhnfCN_lvl.
+ move=> c1 ih1 c2 ih2 l t h1 h2 h3 h4 h5 /esym tE; case: (EM (IsNfC c1)) => nfc1.
  move: tE => /=; rewrite scE c2tE; case: t h4 => // t1 t2 h4 tE.
  - have: exists n cs, c1 = ⌊n⌋ ○! cs.
    * inversion h2; elim/last_ind: cs H0 => // cs c _.
      by rewrite CAppS_rcons => -[<- _]; exists n, cs.
    case=> [n] [cs] c1E; subst c1; case: (EM (IsWhnfC c2)) => whnfc2.
    *  have nfc2: ~ IsNfC c2.
      - move=> h6; apply/h3; rewrite -CAppS_rcons; constructor.
        move=> c; rewrite mem_rcons in_cons => /orP[/eqP->//|c_cs].
        inversion nfc1.
        - by elim/last_ind: {+}cs H => // cs' c' _; rewrite CAppS_rcons.
        by apply/H0; move/CAppS_injR: H => ->.
      case: (ih2 l t2) => // {ih1 ih2}.
      - by move/IsStc_AppR: h1.
      - by move/IsNf_AppR: h4.
      - by elim/wfc_app: h5. 
      - by case: tE => _ ->.
      move=> S'' [hS''1 hS''2 hS''3]; case: hS''3.
      - case=> hS''3 hS''4; exists (⌊n⌋ ○! cs ○ S''); split=> //.
        + by apply/NoCν => //=; apply/IsNeutralCP; do! eexists.
        + apply/(@Stc5 _ _ _ [::]) => // nf nfcs.
          by move/IsNfC_grd_apps: nfc1; apply.
        left; split.
        + by move/IsNfC_AppR. 
        + by rewrite -CAppS_rcons; constructor.
      - case=> hS''3 ?; subst t2; exists (⌊n⌋ ○! cs ○ S''); split => //.
        + by apply/NoCν => //; apply/IsNeutralCP; do! eexists.
        + apply/(@Stc5 _ _ _ [::]) => // nf nfcs.
          by move/IsNfC_grd_apps: nfc1; apply.
        right; split.
        + rewrite -CAppS_rcons; constructor => c.
          rewrite mem_rcons in_cons => /orP[/eqP->//|].
          inversion nfc1.
          - elim/last_ind: {+}cs H => // cs' c' _.
            by rewrite CAppS_rcons.
          - by move/CAppS_injR: H => <-; apply/H0.
        + case: tE => -> _; rewrite c2tE; congr (_ · _).
          by rewrite sc_IsNfC.
  - (* from nfc1, h3, and the fact that the operator is neutral *)
    have: exists c2', c2 →_[ρ,l] c2' by admit.
    case=> c2' rd; case: (@L_5_11 l c2 c2' t2) => // {ih1 ih2}.
    * by move/IsStc_AppR: h1.
    * by apply/IsNf_IsWhnf; move/IsNf_AppR: h4.
    * by elim/wfc_app: h5.
    * by case: tE => _ ->.
    move=> h6 h7; exists (⌊n⌋ ○! cs ○ c2'); split=> //.
    * by apply/NoCν => //; apply/IsNeutralCP; do! eexists.
    * apply/(@Stc5 _ _ _ [::]) => // nf h.
      by move/IsNfC_grd_apps: nfc1; apply.
    case: (EM (IsNfC c2')) => h8.
    * right; split.
      - rewrite -CAppS_rcons; constructor => c.
        rewrite mem_rcons in_cons => /orP[/eqP->//|c_in_cs].
        by move/IsNfC_grd_apps: nfc1; apply.
      - by rewrite c2tE h7 //; case: tE => -> _; rewrite sc_IsNfC.
    * left; split.
      - by move/IsNfC_AppR/h8.
      - by rewrite -CAppS_rcons; constructor.
  - have: exists c1', c1 →_[ρ,l] c1'.
    * admit. (* because of nfc1 *)
    case=> c1' rd; move: tE; rewrite /= scE c2tE; case: t h4 => //.
    move=> t1 t2 h4 [t1E t2E]; case: (ih1 l t1) => {ih1 ih2} //.
    * by move/IsStc_AppL: h1; apply.
    * inversion h2; elim/last_ind: cs H0 => // cs c _.
      by rewrite CAppS_rcons => -[<- _]; constructor.
    * by move/IsNf_AppL: h4.
    * by elim/wfc_app: h5.
    move=> S'' [hS''1 hS''2 hS''3]; exists (S'' ○ c2); split.
    * apply/NoCμ2 => //.
      - inversion h2; elim/last_ind: cs H0 => // cs c _.
        by rewrite CAppS_rcons => -[<- _]; constructor.
      - inversion h2; elim/last_ind: cs H0 => // cs c _.
        rewrite CAppS_rcons => -[<- _]; apply/IsNeutralCP.
        by exists n, cs.
    * have: exists ρ b, c2 = ξ [ρ] b.
      - inversion h1.
        - elim/last_ind: ρts H0 => // ρts ρt _.
          rewrite map_rcons CAppS_rcons => -[_ <-].
          by do! eexists.
        - elim/last_ind: ρts H0 => // ρts ρt _.
          rewrite map_rcons CAppS_rcons => -[_ <-].
          by do! eexists.
        - subst cs; elim/last_ind: ρts H => /=; last first.
          * move=> ρts ρt _; rewrite map_rcons CAppS_rcons.
            by case=> _ <-; do! eexists.
          * case=> c1E _; have: IsNfC c1.
            - by rewrite -c1E; constructor.
            by case/(red_NIsNfC _ hS''1); elim/wfc_app: h5.
      case=> [ρ] [b] ?; subst c2.
      have h6: IsNeutralC S''.
      - (* by inversion of h2 *) admit.
      admit. (* by inversion of hS1'', retrieving the form of S''*)
    * left; split.
      - admit. (* c2 is a proper closure *)
      - admit. (* by inversion of hS''1, retriving the for of S'' *)
+ move=> c ih l t h1 h2 h3 h4 h5 /esym tE.
  have h6: ~ IsNfC c by admit. (* by h3 *)
  have: exists c', c →_[ρ,l.+1] c' by admit. (* by h6 *)
  case=> c' rd; case: (EM (IsWhnfC c)).
  * move=> h7; move: tE; rewrite /= scE c2tE.
    case: t h4 => // t h8 [?]; subst t.
    case: (ih l.+1 (sc c l.+1)) => //.
    - admit. (* by h1 *)
    - admit. (* by h8 *)
    - admit. (* by h5 *)
    - move=> S'' [hS''1 hS''2 hS''3]; case: hS''3.
      + case=> h9 h10; exists (λλ [S'']); split => //.
        - by apply/NoCξ.
        - by constructor.
        left; split.
        - admit. (* by h9 *)
        - by constructor.
      + case=> h9 h10; exists (λλ [S'']); split => //.
        - by apply/NoCξ.
        - by constructor.
        right; split.
        - by constructor.
        - by rewrite -h10 c2tE.
  * move: tE; rewrite /= scE c2tE.
    case: t h4 => // t h8 [?]; subst t.
    move=> h7; case: (@L_5_11 l.+1 c c' (sc c l.+1)) => //.
    - admit. (* by h1 *)
    - admit. (* by h8 *)
    - admit. (* by h5 *)
    move=> h9 h10; exists (λλ [c']); split=> //.
    - by apply/NoCξ.
    - by constructor.
    case: (EM (IsNfC (c'))).
    + move=> h11; right; split=> //.
      - by constructor.
      - by rewrite -h10 // c2tE.
    + move=> h11; left; split=> //.
      - admit. (* by h11 *)
      - by constructor.
Admitted.

(* -------------------------------------------------------------------- *)
Lemma sc_rho_inv c l t : IsNf t -> IsStc c -> wfc l c -> sc c l = t :> term ->
  exists2 e : ephemeral, c →*_[ρ,l] e & t = e.
Proof.
elim/hind: c l t => c ih l t; case: (EM (IsWhnfC c)).
+ case: (EM (IsNfC c)).
  - admit. (* e = c *)
  - move=> h1 h2 h3 h4 h5 h6; case: (@L_5_12 l c t) => //.
    move=> c' [h7 h8 h9]; case: h9.
    + case=> h9 h10; case: (ih c' _ l t) => //.
      * admit. (* FIXME: to be proved *)
      * admit. (* FIXME: proved somewhere *)
      * admit. (* easy *)
      move=> e h11 h12; exists e => //.
      * by apply/(rt_trans _ _ _ _ _ _ h11)/rt_step.
    + case=> h9 h10. admit. (* e = c' *)
+ move=> h1 h2 h3 h4 h5; have: exists c', c →_[ρ,l] c' by admit. (* h1 *)
  case=> c' rd; case: (@L_5_11 l c c' t) => //.
  + admit. (* h12 *)
  + move=> h6 h7; case: (EM (IsNfC c')).
    - admit. (* e = c' *)
    - move=> h8; case: (ih c' _ l t) => //.
      * admit. (* FIXME: to be proved *)
      * admit. (* FIXME: proved somewhere *)
      * admit. (* easy from h5 *)
    move=> e h9 h10; exists e => //.
    by apply/(rt_trans _ _ _ _ _ _ h9)/rt_step.
Admitted.

(* -------------------------------------------------------------------- *)
Lemma ephemeral_lamI (e : ephemeral) t :
  e = λ [t] :> term -> exists2 e' : ephemeral,
    e = λλ [e'] :> closure & e' = t :> term.
Proof.
case: e; case=> //=.
- by move=> ? _; rewrite c2tE.
- by move=> ?? _; rewrite c2tE.
move=> c ce; rewrite c2tE => -[<-].
by exists (Ephemeral ce).
Qed.

(* -------------------------------------------------------------------- *)
Lemma ephemeral_varappI (e : ephemeral) x ts :
  e = #x ·! ts :> term -> exists2 es : seq ephemeral,
      e = ⌊x⌋ ○! [seq closure_of_ephemeral c | c <- es] :> closure
    & [seq term_of_closure_r (closure_of_ephemeral c) | c <- es] = ts.
Proof.
move=> eE; pose us := [seq ephemeral_of_term t | t <- ts].
exists us; first rewrite {}/us.
+ elim/last_ind: ts e eE => /= [|ts t ih] e eE.
  * case: e eE => //; case=> //=.
    - by move=> ? _; rewrite c2tE => -[->].
    - by move=> ?? _; rewrite c2tE.
    - by move=> ? _; rewrite c2tE.
  * rewrite !map_rcons CAppS_rcons; case: e eE => //=; case=> //=.
    - by move=> ? _; rewrite c2tE AppS_rcons.
    - move=> e1 e2 /andP[h1 h2]; rewrite c2tE AppS_rcons.
      case=> he1 he2; rewrite -(ih (Ephemeral h1)) //=.
      by rewrite -he2 /term_of_closure_r -eq_lock term_of_closureK.
    - by move=> ? _; rewrite c2tE AppS_rcons.
+ rewrite {}/us; elim: ts {eE} => //= t ts ->.
  by rewrite /term_of_closure_r -lock closure_of_termK.
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsNf_IsNfC (e : ephemeral) : IsNf e -> IsNfC e.
Proof.
suff: forall t, IsNf t ->
  forall (e : ephemeral), t = e :> term -> IsNfC e.
+ by move=> h hc; apply/(h _ hc).
move=> {e} t; elim=> {t} /= [t _ ih|x ts _ ih] e /esym eE.
+ case/ephemeral_lamI: eE => e' -> tE.
  by constructor; apply/ih.
+ case/ephemeral_varappI: eE => es -> tsE.
  constructor => c /mapP[/= e'].
  move/(map_f (term_of_closure_r \o closure_of_ephemeral)) => /=.
  by rewrite tsE => /ih h1 ->; apply/h1.
Qed.

(* -------------------------------------------------------------------- *)
Lemma inj_varappsr x y ts us :
  #x ·! ts = #y ·! us -> ts = us.
Proof.
elim/last_ind: ts us => [|ts t ih] /= us.
+ by elim/last_ind: us => [|us u _] //=; rewrite AppS_rcons.
elim/last_ind: us => [|us u _] /=.
+ by rewrite AppS_rcons.
+ by rewrite !AppS_rcons => -[/ih -> ->].
Qed.

Lemma inj_cvarappsr x y cs cs' :
  ⌊x⌋ ○! cs = ⌊y⌋ ○! cs' -> cs = cs'.
Proof.
elim/last_ind: cs cs' => [|cs c ih] /= cs'.
+ by elim/last_ind: cs' => [|cs' c' _] //=; rewrite CAppS_rcons.
elim/last_ind: cs' => [|cs' c' _] /=.
+ by rewrite CAppS_rcons.
+ by rewrite !CAppS_rcons => -[/ih -> ->].
Qed.

Derive Inversion_clear red_appI
  with (forall t u v, t · u → v)
  Sort Prop.

(* -------------------------------------------------------------------- *)
Derive Inversion_clear rhored_app
  with (forall c1 c2 c l, c1 ○ c2 →_[ρ,l] c)
  Sort Prop.
  
Derive Inversion_clear rhored_var
  with (forall n c l, ⌊n⌋ →_[ρ,l] c)
  Sort Prop.

Derive Inversion_clear rhored_base_var
  with (forall n c l, ⌊n⌋ ⇀_[ρ,l] c)
  Sort Prop.

Lemma iswhnfc_appI c :
  IsWhnfC c -> IsNeutralC c ->
    exists n, exists cs, c = ⌊n⌋ ○! cs.
Proof. by case=> // n cs _; eauto. Qed.

(* -------------------------------------------------------------------- *)
Lemma NoRed_varappsnf_app x ts u v :
     (forall t, t \in ts -> IsNf t)
  -> #x ·! ts · u → v
  -> exists u', u → u' /\ v = #x ·! ts · u'.
Proof.
elim/last_ind: ts u v => //= [|ts t ih] u v.
+ move=> _ rd; inversion rd using NoRed_app_r.
  * by inversion 1.
  * by move=> t /(_ (IsWhnfVar _ [::])).
  * by move=> t _ _ /inv_noredbeta_var.
  * by move=> t _ _ {rd} rd; exists t.
move=> nfs; rewrite AppS_rcons => rd.
inversion rd using NoRed_app_r.
+ by inversion 1.
+ by rewrite -AppS_rcons; move=> t' /(_ (IsWhnfVar _ _)).
+ move=> t' _ _ /ih[].
  * by move=> t'' ints; apply/nfs; rewrite mem_rcons in_cons ints orbT.
  move=> rdt [{rd} rd] _; have nf_t: IsNf t.
  * by apply: nfs; rewrite mem_rcons in_cons eqxx.
  by case: (IsNf_nf nf_t rd).
+ by move=> u' _ _ {rd} rd; exists u'.
Qed.


(* -------------------------------------------------------------------- *)
Lemma IsNfC_sc c l : IsNfC c -> IsNfC (sc c l).
Proof.
move=> h; elim: h l => {c} [c _ ih|n cs _ ih] l.
+ by rewrite scE; constructor.
+ rewrite sc_appS scE; constructor.
  by move=> c /mapP[c' incs ->]; apply/ih.
Qed.

(* -------------------------------------------------------------------- *)
Lemma rhored_trans_appR (t u u' : closure) l :
  IsNfC t -> IsNeutralC t ->
  u →*_[ρ,l] u' -> t ○ u →*_[ρ,l] t ○ u'.
Proof.
move=> h1 h2; elim=> [X1 X2 h|X|X1 X2 X3 _ ih1 _ ih2].
- by apply/rt_step/NoCν.
- by apply/rt_refl.
- by apply/(rt_trans _ _ _ _ _ ih1 ih2).
Qed.

(* -------------------------------------------------------------------- *)
Lemma L_5_13 l (S : closure) (M M' : term) :
     IsStc S -> wfc l S -> M → M' -> σc S l = M :> term
  -> exists X, [/\ IsExc l X, wfc l X & S →*_[ρ,l] X].
Proof.
elim/hind: S M M' => S ih M M'; case: (EM (IsWhnfC S)).
+ case: S ih.
 * admit. (* a proper closure is not a whnf *)
 * move=> n ih h1 h2 h3 rd /esym ME; rewrite /= scE in ME.
   case/IsNf_nf: rd; rewrite ME; apply/IsNfC_IsNf.
   by apply/(@IsNfCVar _ [::]).
 * move=> n ih h1 h2 h3 rd /esym ME; rewrite /= scE in ME.
   case/IsNf_nf: rd; rewrite ME; apply/IsNfC_IsNf.
   by apply/(@IsNfCVar _ [::]).
   
 * move=> c1 c2 ih h1 h2 h3 rd /esym ME; rewrite /= scE in ME.
   move: h1; inversion 1; move: H0.
   elim/last_ind: cs => //= cs c' _; rewrite CAppS_rcons.
   case=> /esym c1E /esym c2E; subst c'; case: (EM (IsNfC c1)) => h.
   - elim/IsNfCI: h (c1E).
     + move=> c' _; elim/last_ind: {+}cs => //=.
       by move=> cs' c'' _; rewrite CAppS_rcons.
     + move=> k cs' allnf; move/inj_cvarappsr => ?; subst cs'.
       move: rd; rewrite ME c2tE c1E sc_appS scE c2t_appS c2tE.
       case/NoRed_varappsnf_app.
       - move=> t /mapP[ct] /mapP[c' /allnf nfc' -> ->].
         by apply/IsNfC_IsNf/IsNfC_sc.
     move=> M2' [rd ?]; subst M'; case: (ih c2 _ _ _ _ _ rd) => //.
     + by rewrite [X in _ < X]hE ltnS leq_addl.
     + move: h2; rewrite c1E; inversion 1.
       * move: H0; elim/last_ind: ρts => // ρts ρt _.
         rewrite map_rcons CAppS_rcons => -[_ <-].
         by apply/(@Stc3 _ _ [::]).
       * move: H0; elim/last_ind: ρts => // ρts ρt _.
         rewrite map_rcons CAppS_rcons => -[_ <-].
         by apply/(@Stc3 _ _ [::]).
       * move: H; rewrite {}/cs0; elim/last_ind: ρts => /= [|ρts ρt _].
         - by case=> _ <-.
         - rewrite map_rcons CAppS_rcons => -[_ <-].
           by apply/(@Stc3 _ _ [::]).
     + by elim/wfc_app: h3.
     move=> X [exX wfX rdX]; exists (c1 ○ X); split.
     + by rewrite c1E; apply/(@Exc3 _ l _ _ [::]).     
     + by constructor=> //; elim/wfc_app: h3.
     + rewrite c1E; apply/rhored_trans_appR => //.
       - by constructor.
       - by apply/IsNeutralCP; do 2! eexists.
   - case: (EM (IsNf (sc c1 l))) => h'.
     + case: (@L_5_12 l c1 (sc c1 l)) => //.
       * admit. (* -> h2 *)
       * admit. (* -> h1 *)
       * admit. (* -> h3 *)
       move=> X [hX1 hX2 hX3]; case: (ih (X ○ c2) _ M M') => //.
       * admit.
       * admit. (* -> if c2 is the 'c' of Stc5, then c1 is normal -> contradiction *)
       * admit. (* red preserves wf, so X is wf, and ok *)
       * admit. (* From ME and hX1 *)
       move=> X' [hX'1 hX'2 hX'3]; exists X'; split=> //.
       rewrite -c1E; apply/(rt_trans _ _ _ _ _ _ hX'3).
       apply/rt_step/NoCμ2 => //.
       * admit. (* -> h1 *)
       * admit. (* By computation *)
     + move: rd; rewrite ME; rewrite !c2tE.
       have: exists M1' M2, M' = M1' · M2 /\ sc c1 l → M1'.
       * admit.
       case=> [M1'] [M2] [M'E rd1 rd2]; case: (ih c1 _ (sc c1 l) M1') => //.
       * admit.
       * admit. (* -> if c2 is the 'c' of Stc5, then c1 is normal -> contradiction *)
       * admit. (* From h3 *)
       move=> X [hX1 hX2 hX3]; exists (X ○ c2); split=> //.
       * admit. (* c2 is a proper closure because the 'c of Stc5 cannot be c3 *)
       * admit.
       * admit. (* by hX3, using Rhoμ2 several times *)
 * move=> c ih h1 h2 h3 rd /esym /= ME.
   (* By IH on the body, inverting first the reduction to get M *)
   admit.

+ case: S ih.
  * case=> [n|t1 t2|t].
    - move=> ρ ih; case: (ltnP n (size ρ)) => [lt|le]; last first.
      + rewrite /= scE ltnNge le /= => _ _ _ h ?; subst M.
        by move: h; rewrite c2tE; case/inv_noredbeta_var.
      + rewrite /= scE lt => _ _ hwf rd ?; subst M.
        elim/wfc_clos: (hwf) => /mem_wf /(_ (mem_nth _ lt)) -/(_ ^0) [].
        + case=> i iE _; move: rd; rewrite (set_nth_default ^0) //.
          by rewrite iE scE c2tE; case/inv_noredbeta_var.
        + case=> [t] [ρ'] [_] [ρE _ _].
          case/(_ (ξ [ρ'] t) _ (sc (nth ⌊0⌋ ρ n) l) M'): ih => //.
          - rewrite -ρE [X in _ < X]hE lt (set_nth_default ^0) //.
          - by apply/(Stc3 _ _ [::]).
          - elim/wfc_clos: hwf => /mem_wf /(_ (mem_nth _ lt)).
            move/(_ ^0) => -[[x]|]; first by rewrite ρE.
            case=> [t'] [ρ''] [l'] []; rewrite ρE.
            case=> ??; subst t' ρ'' => hwf le_l.
            by constructor; apply/(wf_strg le_l).
          - by rewrite /= -ρE (set_nth_default ^0).
          move=> X [exX wfX rdX]; exists X; split=> //.
          apply/(rt_trans _ _ _ (ξ [ρ'] t)) => //.
          by apply/rt_step/NoCBase; rewrite -ρE; constructor.
    - move=> ρ ih h1 h2 h3 rd /esym ME.
      case: (ih (ξ [ρ] t1 ○ ξ [ρ] t2) _ M M') => //.
      - by rewrite hE 2![in X in _ < X]hE !ltnS.
      - by apply/(@Stc3 _ _ [:: (ρ, t2)]).
      - by elim/wfc_clos: h3 => h3; do 2! constructor.
      - by rewrite ME /= [in RHS]scE.
      move=> X [exX wfX rdX]; exists X; split=> //.
      by apply/(rt_trans _ _ _ _ _ _ rdX)/rt_step; do 2! constructor.
    - move=> ρ ih h1 h2 h3 rd /esym ME.
      case: (ih (λλ [ξ [^l.+1 :: ρ] t]) _ M M') => //.
      - rewrite hE 2![in X in _ < X]hE !ltnS.
        rewrite leq_eqVlt -(rwP orP); left.
        by apply/eqP/h_closure_eq => /=; rewrite !hE.
      - by constructor; apply/(@Stc3 _ _ [::]).
      - by do 3! constructor => //; elim/wfc_clos: h3.
      - by rewrite ME /= [in RHS]scE.
      move=> X [exX wfX rdX]; exists X; split=> //.
      by apply/(rt_trans _ _ _ _ _ _ rdX)/rt_step; do 2! constructor.
  * admit. (* A variable is a whnf *)
  * admit. (* Resolve the index and apply the IH *)
  * case => //.
    - case=> [n|t1 t2|t].
      + admit. (* Apply ih on the reduce of #x *)
      + admit. (* ibid *)
      + move=> cs c ih h1 h2 h3 rd /esym /= ME.
        exists (λλ [ξ [^l.+1 :: cs] t] ○ c); split=> //.
        * admit. (* By h2, c is a proper closure *)
        * admit. (* ok, from h3 *)
        * admit. (* By rule μ1 *)
    - admit. (* Is it a whnf *)
    - admit. (* Reduce ^n, apply ih *)
    - admit. (* ibid *)
    - admit. (* We're contradicting IsStc (...) *)
  * admit. (* iit is a whnf *)
Admitted.

Lemma IsExcBeta X l : IsExc l X -> wfc l X -> exists2 S, IsStc S & X →_[β,l] S.
Proof. elim.
+ move=> n ρ t1 [|] // ρt ρts cs _ h.
  rewrite /cs map_cons CAppS_cons; set cs' := map _ _.
  exists ((ξ [(ξ [ρt.1] ρt.2 :: ρ)] t1) ○! cs').
  * by apply/Stc3.
  elim/last_ind: cs' => [|cs' c ih] /=; first by do! constructor.
  rewrite !CAppS_rcons; apply/NoCμ1 => //. admit.
+ move=> n c _ ih; elim/wfc_lam => /ih [S h1 h2].
  exists (λλ [S]); first by do! constructor.
  by apply/NoCξ.
+ move=> n p nfc c ρts cs h1 h2 h3 h4.
  move/wfc_appsl: h4; elim/wfc_app => _ /h2 [S h'1 h'2].
  exists (⌊n⌋ ○! nfc ○ S ○! cs); first by apply/Stc5.
  admit.
Admitted.

(*
Lemma commute_r l (M1 : closure) (X : closure) (E : ephemeral) :
    wfc l X 
  -> IsExc X
  -> X →_[β, l] M1
  -> X →_[σ, l]  E
  -> exists E', M1 →_[σ, l] E' /\ E → E'.
Proof.
rewrite /SigmaRed => wfX ecX rb ->; elim: {E} ecX M1 l wfX rb.



+ move=> n ρ t1 [|] //. admit.
*)
(*



t2 M1 l wfX h; rev/rwbb: h => // {h}; last first.
    by move=> c []; constructor.
  move=> h; move: wfX; rev/rwb1: h => t u ρ'; set c := (X in sc X).
  exists (sc c l); split=> //; rewrite 2!scE L_5_7.
    by rewrite !c2tE; do! ctor.
  rev/wfc_app: wfX; rev/wfc_lam; rev/wfc_clos => wf1.
  by rev/wfc_clos => w2; ctor.


| Exc1 n ρ t1 t2 :
    IsExc ((λλ [ξ [^n :: ρ] t1]) ○ (ξ [ρ] t2))
*)

(*
+ move=> c exc ihc M1 l; rev/wfc_lam => wfX h; rev/rwbl: h.
  move=> c' /ihc [] // E' [eq scE']; exists (λλ [E']); rewrite scE {1}eq.
  by split=> //; rewrite scE !c2tE; apply/Noξ.
+ move=> n nfc c ρts cs exc ihc nf M1 l wfX.
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
Admitted.
*)

Lemma BetaSigma l X S (m m' : term) : IsExc l X ->
  sc X l = m :> term -> X →_[β,l] S -> m → m' -> sc S l = m' :> term.
Proof. elim.
+ move=> n ρ t1 [|] // ρt ρts cs _ <-.
  rewrite sc_appS c2t_appS scE !c2tE {}/cs !map_cons AppS_cons.
  set cs := map _ _; set u1 := sc _ _; set u2 := sc _ _.
  move=> h. admit.
admit.
Admitted.

(* -------------------------------------------------------------------- *)
Theorem commute l (S0 : closure) (m0 : term) :
  IsStc S0 -> wfc l S0 -> σc S0 l = m0 :> term ->
  (IsNf m0 -> exists2 N, S0 →*_[ρ,l] N & N = m0 :> term)
  /\ (~IsNf m0 -> exists S1 (m1 : term) X,
           IsExc l X
        /\ S0 →*_[ρ,l] X
        /\ X →_[β,l] S1
        /\ IsStc S1
        /\ m0 → m1
        /\ σc S1 l = m1 :> term).
Proof.
move=> h1 h2 h3; split => h4.
+ by case: (@sc_rho_inv S0 l m0) => // e rd m0E; subst; exists e.
have: exists m0', m0 → m0' by admit. (* h4 *)
case=> m0' rd; case: (@L_5_13 l S0 m0 m0') => // X [h5 h6 h7].
case: (IsExcBeta h5 h6) => S h8 h9; exists S, m0', X.
do! split=> //. move: h3 h9 rd => /=; rewrite (sc_rho h7).
by apply/BetaSigma.
Admitted.

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
Derive Inversion iswhnfI
  with (forall c, IsWhnfC c)
  Sort Prop.

(* -------------------------------------------------------------------- *)
Lemma iswhnfCN_pclos ρ t : ~ IsWhnfC (ξ [ρ] t).
Proof.
elim/iswhnfI => // _ n; elim/last_ind => [|cs c _] //.
by rewrite CAppS_rcons.
Qed.

(* -------------------------------------------------------------------- *)
Lemma iswhnfCN_lvl l : ~ IsWhnfC (^l).
Proof.
elim/iswhnfI => // _ n; elim/last_ind => [|cs c _] //.
by rewrite CAppS_rcons.
Qed.

(* -------------------------------------------------------------------- *)
Derive Inversion isnfI
  with (forall t, IsNf t)
  Sort Prop.

Lemma NIsNf_LamApp t u : ~ IsNf (λ [t] · u).
Proof.
elim/isnfI => //= _ x ts _; elim/last_ind: ts u => //.
move=> ws w _ u; rewrite AppS_rcons => -[h _] {w u}.
by elim/last_ind: ws h => // ws w _; rewrite AppS_rcons.
Qed.


(* -------------------------------------------------------------------- *)
Lemma IsNeutral_IsNeutralC (e : ephemeral) : IsNeutral e -> IsNeutralC e.
Proof.
case: e => c ee /IsNeutralP [n] [ts] /= cE.
apply/IsNeutralCP; exists n, [seq closure_of_term t | t <- ts].
move/(congr1 closure_of_term): cE; rewrite closure_of_term_appS /=.
by move=> <-; rewrite /term_of_closure_r -lock term_of_closureK.
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsNfApp_IsNeutral t u : IsNf (t · u) -> IsNeutral (t · u).
Proof.
suff: forall w, IsNf w -> forall t u, w = t · u -> IsNeutral w.
+ by move=> h1 h2; apply/h1.
move=> w; case => //= x ts _ _ _ _.
elim/last_ind: ts => // ts t' _; rewrite AppS_rcons.
by rewrite -AppS_rcons; apply/IsNeutralVar.
Qed.

(* -------------------------------------------------------------------- *)
Lemma isneutralc_rhored c1 c2 l :
  IsNeutralC c1 -> c1 →_[ρ,l] c2 -> IsNeutralC c2.
Proof.
case/IsNeutralCP => [x] [cs] ->; elim/last_ind: cs c2 => /= [|cs c ih] c2.
+ by elim/rhored_var; elim/rhored_base_var.
rewrite CAppS_rcons; elim/rhored_app.
+ by inversion 1.
+ by move=> c1' []; constructor.
+ by move=> c1' _ _ /ih.
+ move=> c2' _ _ _; rewrite -CAppS_rcons; apply/IsNeutralCP.
  by exists x, (rcons cs c2').
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsWhnfC_appI c1 c2 : IsWhnfC (c1 ○ c2) -> IsWhnfC c1.
Proof.
elim/iswhnfI => // _ n; elim/last_ind => // cs c _.
by rewrite CAppS_rcons => -[<- _]; constructor.
Qed.  

(* -------------------------------------------------------------------- *)
Derive Inversion IsNfCI
  with (forall c, IsNfC c)
  Sort Prop.

Lemma IsNfC_appI c1 c2 : IsNfC (c1 ○ c2) ->
  exists n cs, c1 ○ c2 = ⌊n⌋ ○! cs.
Proof.
elim/IsNfCI => // _ n cs _.
by elim/last_ind: cs => // cs c _ _; eauto.
Qed.

(*
(* -------------------------------------------------------------------- *)
Lemma iswhnfc_rhored c1 c1_1 c1_2 c2 l :
  IsWhnfC c1 -> c1 →_[ρ,l] c2 -> c1 = (c1_1 ○ c1_2) -> IsWhnfC c2.
Proof.
move=> he h; case: h he c1_1 c1_2 => {l c1 c2} //.
+ by move=> l c1 c2 rd _ ???; subst c1; inversion rd.
Is+ by move=> ???? ? _ /IsWhnfC_appI.
+ move=> l c1 c1' c2 wh nt rd h; elim/iswhnfI: h nt => //.
  move=> _ n cs; elim/last_ind: cs rd => // cs c _ rd.
  rewrite CAppS_rcons => -[c1E _]; subst c1 => _ _ _ _ {wh}.
  have: exists cs', c1' = ⌊n⌋ ○! cs'.
  * elim/last_ind: cs c1' rd => /= [|cs c' ih] c1'.
    - by elim/rhored_var; elim/rhored_base_var.
    rewrite CAppS_rcons; elim/rhored_app.
    - by inversion 1.    
    - move=> c3 _ /ih [cs' ->]; exists (rcons cs' c').
      by rewrite CAppS_rcons.      
    - move=> c3 _ _ /ih [cs' ->]; exists (rcons cs' c').
      by rewrite CAppS_rcons.      
    - move=> c2' _ _ _; exists (rcons cs c2').
      by rewrite CAppS_rcons.      
    by case=> cs' ->; rewrite -CAppS_rcons; constructor.
+ move=> l c1 c1' c2 nf nt rd h; elim/iswhnfI: h nt => //.
  move=> _ n cs; elim/last_ind: cs rd => // cs c _ rd.
  rewrite CAppS_rcons => -[c1E _]; subst c1 => _ _ _ _ {nf}.
  by rewrite -CAppS_rcons; constructor.
Qed.
 *)

(* -------------------------------------------------------------------- *)
Lemma sc_rho_inv c l t : IsNf t -> sc c l = t :> term ->
  exists2 e : ephemeral, c →*_[ρ,l] e & t = e.
Proof. elim/hind: c l t; case.
+ move=> t cs ih l u nf eq; rewrite -eq; case: t l eq ih => [n|t1 t2|t] l eq ih.
  * rewrite scE; case: ifPn => [ltn|gen]; last first.
    - exists (@Ephemeral ⌊n + l - size cs⌋ (erefl true)) => //=.
      by apply/rt_step; constructor; apply/RhoRedFree; rewrite leqNgt.
    set c := nth _ _ _; have ccs: c \in cs by rewrite mem_nth.
    case/(_ c _ l (sc c l) _ (erefl _)): ih.
    - by rewrite [X in _ < X]hE ltn.
    - by move: eq; rewrite scE ltn => ->.
    move=> e rd /esym eE; exists e => //.
    apply/(rt_trans _ _ _ c) => //; apply/rt_step.
    constructor; rewrite /c (set_nth_default ^0) //.
    by apply/(RhoRedVar l ltn).
  * rewrite scE; pose c := ξ [cs] t1 ○ ξ [cs] t2.
    case: (ih c _ l _ _ (erefl _)).
    - by rewrite [X in _ < X]hE.
    - by move: nf; rewrite -eq /c scE.
    move=> e rd eE; exists e => //; apply/(rt_trans _ _ _ c) => //.
    by apply/rt_step/NoCBase/RhoRedApp.
  * rewrite scE. set c := λλ [_]; case: (ih c _ l _ _ (erefl _)).
    - rewrite [X in _ < X]hE /c ![h (λλ [_])]hE !ltnS.
      rewrite leq_eqVlt; apply/orP; left; apply/eqP.
      by apply/h_closure_eq => /=; rewrite !hE.
    - by move: nf; rewrite -eq /c scE.
    move=> e rd eE; exists e => //; apply/(rt_trans _ _ _ c) => //.
    by apply/rt_step/NoCBase/RhoRedLam.
+ move=> n _ l t _ <-; exists (@Ephemeral ⌊n⌋ (erefl true)) => /=.
  - by apply/rt_refl. - by rewrite scE.
+ move=> n _ l t _ <-; exists (@Ephemeral ⌊l-n⌋ (erefl true)) => /=.
  - by apply/rt_step/NoCBase/RhoRedPar.
  - by rewrite scE.
+ move=> c1 c2 ih l t nf eq; rewrite -eq; case: c1 eq ih.
  - case => [n|u1 u2|u] ρ eq ih.
    * rewrite 2!scE; case: ifPn => [ltn|gen]; last first.
      + case: (ih c2 _ l _ _ (erefl _)).
        - by rewrite [X in _ < X]hE ltnS leq_addl.
        - by move: nf; rewrite -eq scE c2tE => /IsNf_AppR.
        move=> e2 rd2 eE2; have: is_ephemeral (⌊n + l - size ρ⌋ ○ e2).
        - by rewrite /= valP.
        move=> h; exists (Ephemeral h) => /=; last first.
        - by rewrite !c2tE; rewrite eE2.
        apply/(rt_trans _ _ _ (⌊n + l - size ρ⌋ ○ c2)).
        - apply/rt_step/NoCμ1 => /=.
          * by apply/iswhnfCN_pclos.
          * by apply/NoCBase/RhoRedFree; rewrite leqNgt.
        - by apply/rhored_trans_appR => //; apply/(@IsNfCVar _ [::]).
      + set c := nth _ _ _; case: (ih (c ○ c2) _ l _ _ (erefl _)).
        - rewrite [X in _ < X]hE ltnS hE ltn_add2r.
          by rewrite [X in _ < X]hE ltn.
        - move: nf; rewrite -eq ![sc (_ ○ _) _]scE.
          by rewrite [sc (ξ [_] #_) _]scE ltn.
        move=> e rd eE; exists e; last first.
        - by rewrite -eE [in RHS]scE !c2tE.
        apply/(rt_trans _ _ _ (c ○ c2)) => //.
        apply/rt_step/NoCμ1 => [/iswhnfCN_pclos//|].
        apply/NoCBase; rewrite /c (set_nth_default ^0) //.
        by apply/RhoRedVar.
    * rewrite scE; set c := ξ [ρ] u1 ○ ξ [ρ] u2 ○ c2.
      case: (ih c _ l _ _ (erefl _)).
      - rewrite /c hE [X in _ < X]hE ltnS ltn_add2r.
        by rewrite hE 2![in X in _ < X]hE !ltnS.
      - move: nf; rewrite -eq /c ![sc (_ ○ _) _]scE.
        by rewrite [sc (ξ [_] _) _]scE scE.
      move=> e rd eE; exists e; last first.
      - by rewrite -eE /c [in RHS]scE [in LHS]scE.
      apply/(rt_trans _ _ _ c) => //; apply/rt_step.
      apply/NoCμ1 => [/iswhnfCN_pclos//|].
      by apply/NoCBase/RhoRedApp.
    * by move: nf; rewrite -eq scE !c2tE 2!scE !c2tE => /NIsNf_LamApp.
  - move=> n tE /(_ c2 _ l _ _ (erefl _)) [].
    * by rewrite [X in _ < X]hE ltnS leq_addl.
    * by move: nf; rewrite -tE scE c2tE => /IsNf_AppR.
    move=> e rd eE; have h: is_ephemeral (⌊n⌋ ○ e).
    * by rewrite /= valP.
    exists (Ephemeral h) => /=; last first.
    * by rewrite 2!scE !c2tE eE.
    by apply/rhored_trans_appR => //; apply/(@IsNfCVar _ [::]).
  - move=> n tE /(_ c2 _ l _ _ (erefl _)) [].
    * by rewrite [X in _ < X]hE ltnS leq_addl.
    * by move: nf; rewrite -tE scE c2tE => /IsNf_AppR.
    move=> e rd eE; have h: is_ephemeral (⌊l - n⌋ ○ e).
    * by rewrite /= valP.
    exists (Ephemeral h) => /=; last first.
    * by rewrite 2!scE !c2tE eE.
    apply/(rt_trans _ _ _ (⌊l - n⌋ ○ c2)).
    * apply/rt_step/NoCμ1 => [/iswhnfCN_lvl//|].
      by apply/NoCBase/RhoRedPar.
    * by apply/rhored_trans_appR => //; apply/(@IsNfCVar _ [::]).

  - move=> c c1 tE ih; case: (EM (IsWhnf (c ○ c1))); last first.
    * 

    move=> c c1 tE ih; case: (ih (c ○ c1) _ l _ _ (erefl _)).
    * by rewrite [X in _ < X]hE ltnS leq_addr.
    * by move: nf; rewrite -tE scE c2tE => /IsNf_AppL.
    move=> e1 rd1 eE1; case: (ih c2 _ l _ _ (erefl _)).
    * by rewrite [X in _ < X]hE ltnS leq_addl.
    * by move: nf; rewrite -tE scE c2tE => /IsNf_AppR.
    move=> e2 rd2 eE2; have h: is_ephemeral (e1 ○ e2).
    * by rewrite /= !valP.



    exists (Ephemeral h) => /=; last first.
    * by rewrite scE !c2tE eE1 eE2.
    have nfe1: IsNfC e1.
    * move: nf; rewrite -tE scE c2tE => /IsNf_AppL.
      by rewrite eE1; apply/IsNf_IsNfC.
    apply/(rt_trans _ _ _ (e1 ○ c2)); last first.
    * apply/rhored_trans_appR => //.
      - move: {+}nfe1 => /IsNfC_IsNf; rewrite -eE1.
        rewrite scE c2tE => /IsNfApp_IsNeutral.
        rewrite -c2tE (_ : sc c l ○ sc c1 l = e1); last first.
        + move/(congr1 closure_of_term): (eE1).
          rewrite /term_of_closure_r -lock.
          rewrite !term_of_closureK // 1?scE //.
          * by apply/valP.
          by apply/andP; split; apply/sc_is_ephemeral.
        by move/IsNeutral_IsNeutralC.
      - rewrite /= in h; case/andP: h => he1 he2 {rd2 eE2 he2}.
        
        
        move: rd1.

          * have is_neu1: IsNeutralC e1.
      - case: {rd1 h} e1 nfe1 eE1 => /= e; case: e => //.
        + move=> c1' c2' h1 h2 h3.
          case/IsNfC_appI: h2 => [n] [cs] ->.
          by apply/IsNeutralCP; exists n, cs.
        + by move=> ? _ _; rewrite scE !c2tE.
      have: IsNeutralC (c ○ c1).
      * move: is_neu1; move: eE1; rewrite scE !c2tE.
        case: e1 rd1 h nfe1 => e1 /= ee1 rd1 /andP[hee1 hee2] [].
        - by move=> ? _; rewrite c2tE.
          move=> n cs _; elim/last_ind: cs => /=.
          + by rewrite c2tE.
          move=> cs c' _; rewrite CAppS_rcons !c2tE => -[].
          case: is
          

+ by move=> c tE _; move: nf; rewrite -tE 2!scE !c2tE => /NIsNf_LamApp.
+ move=> c ih l t nf tE; case: (ih c _ l.+1 _ _ (erefl _)).
  * by rewrite [X in _ < X]hE ltnS.
  * by move: nf; rewrite -tE scE c2tE => /IsNf_Lam.
  move=> e rd E; have h: is_ephemeral (λλ [e]).
  * by rewrite /= valP.
  exists (Ephemeral h) => /=; last first.
  * by rewrite -tE scE !c2tE E.
  by apply/rhored_trans_lam.
Admitted.

(* -------------------------------------------------------------------- *)
Derive Inversion_clear wfc_closI
  with (forall l ρ n, wfc l (ξ [ρ] #n))
  Sort Prop.

(* -------------------------------------------------------------------- *)
Lemma lth_appSL c1 c2 cs : h c1 < h c2 -> h c1 < h (c2 ○! cs).
Proof.
move=> lt; elim/last_ind: cs => // cs c3 ih.
rewrite CAppS_rcons [X in _ < X]hE ltnS.
by apply/ltnW/(leq_trans ih); rewrite leq_addr.
Qed.

(* -------------------------------------------------------------------- *)
Lemma lth_clos_lam l ρs t :
  h (λλ [ξ [^l :: ρs] t]) < h (ξ [ρs] (λ [t])).
Proof. by rewrite !hcE /= !ltnS [h ^l]hE. Qed.

(* -------------------------------------------------------------------- *)
Lemma lth_clos (ρ : seq closure) n (x0 : closure) :
  n < size ρ -> h (nth x0 ρ n) < h (ξ [ρ] #n).
Proof.
move=> lt; rewrite [X in _ < X]hE /= lt ltnS.
by rewrite -(set_nth_default _ x0).
Qed.

(* -------------------------------------------------------------------- *)
Lemma mem_IsRhoS (ρ : seq closure) (c : closure) :
  IsRhoS ρ -> c \in ρ ->
    (exists n, c = ^n) \/ (exists ρ' t, c = ξ [ρ'] t /\ IsRhoS ρ').
Proof. elim=> //.
+ move=> ρ1 ρ2 t h1 ih1 h2 ih2; rewrite in_cons; case/orP.
  - by move/eqP=> ->; right; eauto.
  - by move/ih2.
+ move=> n ρ' _ ih'; rewrite in_cons; case/orP.
  - by move/eqP=> ->; left; eauto.
  - by move/ih'.
Qed.

(* -------------------------------------------------------------------- *)
Derive Inversion isnfc_lam_r
  with (forall c, IsNfC (λλ [c]))
  Sort Prop.

Lemma isnfc_lam c : IsNfC (λλ [c]) -> IsNfC c.
Proof.
inversion 1 using isnfc_lam_r => //.
move=> _ n cs _; elim/last_ind: cs => // cs c' _.
by rewrite CAppS_rcons.
Qed.

Derive Inversion isnfc_varapps_r
  with (forall n cs, IsNfC (⌊n⌋ ○! cs))
  Sort Prop.

Lemma isnfc_varapps n cs : IsNfC (⌊n⌋ ○! cs) ->
  (forall c, c \in cs -> IsNfC c).
Proof.
move=> h; inversion h using isnfc_varapps_r.
+ move=> {h} _ c _; elim/last_ind: cs => // cs c' _.
  by rewrite CAppS_rcons.
by move=> {h} _ n' cs' hc /eq_capps_grdI [_ <-].
Qed.

Derive Inversion isnfc_closapps_r
  with (forall ρ t cs, IsNfC (ξ [ρ] t ○! cs))
  Sort Prop.

Lemma isnfc_closapps ρ t cs : ~ IsNfC (ξ [ρ] t ○! cs).
Proof.
move=> h; inversion h using isnfc_closapps_r.
+ move=> {h} _ c _; elim/last_ind: cs => // cs c' _.
  by rewrite CAppS_rcons.
move=> {h} _ n' cs' _; elim/last_ind: cs' cs => /= [|c' cs' ih] cs.
+ by elim/last_ind: cs => //= s x _; rewrite CAppS_rcons.
+ rewrite CAppS_rcons; elim/last_ind: cs => //= s x _.
  by rewrite CAppS_rcons; case => /ih.
Qed.

(* -------------------------------------------------------------------- *)
Lemma NoRed_varappsnf_app x ts u v :
     (forall t, t \in ts -> IsNf t)
  -> #x ·! ts · u → v
  -> exists u', u → u' /\ v = #x ·! ts · u'.
Proof.
elim/last_ind: ts u v => //= [|ts t ih] u v.
+ move=> _ rd; inversion rd using NoRed_app_r.
  * by inversion 1.
  * by move=> t /(_ (IsWhnfVar _ [::])).
  * by move=> t _ _ /inv_noredbeta_var.
  * by move=> t _ _ {rd} rd; exists t.
move=> nfs; rewrite AppS_rcons => rd.
inversion rd using NoRed_app_r.
+ by inversion 1.
+ by rewrite -AppS_rcons; move=> t' /(_ (IsWhnfVar _ _)).
+ move=> t' _ _ /ih[].
  * by move=> t'' ints; apply/nfs; rewrite mem_rcons in_cons ints orbT.
  move=> rdt [{rd} rd] _; have nf_t: IsNf t.
  * by apply: nfs; rewrite mem_rcons in_cons eqxx.
  by case: (IsNf_nf nf_t rd).
+ by move=> u' _ _ {rd} rd; exists u'.
Qed.

(* -------------------------------------------------------------------- *)
Lemma IsStc_NIsNfC c : IsStc c -> ~ IsNfC c.
Proof. elim=> {c}.
+ by move=> *; apply: isnfc_closapps.
+ by move=> c h1 h2 /isnfc_lam.
+ move=> n nfc c ρts csE _ hc _ _; rewrite -CAppS_cons -CAppS_cat.
  move=> hF; have /(_ n _ hF) := hc (isnfc_varapps _ _).
  by apply; rewrite mem_cat in_cons eqxx /= orbT.
Qed.

(* -------------------------------------------------------------------- *)
Section StcCase.
Variable (P : closure -> Prop).

Variable
  (HVar  : forall n ρ, IsRhoS ρ -> P (ξ [ρ] #n))
  (HApp  : forall t1 t2 ρ, IsRhoS ρ -> P (ξ [ρ] (t1 · t2)))
  (HLam  : forall t ρ, IsRhoS ρ -> P (ξ [ρ] (λ [t])))
  (HCLam : forall c, IsStc c -> P (λλ [c]))
  (HClo  : forall n nfc c cs,
                IsStc c
             -> (forall nf, nf \in nfc -> IsNfC nf)
             -> P (⌊n⌋ ○! nfc ○ c ○! cs))
  (HCApp : forall ρ t ρts ρ' t',
             let cs := [seq ξ [ρt.1] ρt.2 | ρt <- ρts] in
                IsRhoS ρ
             -> (forall ρt, ρt \in ρts -> IsRhoS ρt.1)
             -> IsRhoS ρ'
             -> P (ξ[ρ] t ○! cs ○ ξ[ρ'] t')).

Lemma stccase c : IsStc c -> P c.
Proof. elim=> {c} /=.
+ move=> ρ t ρts rho_ρ rho_ρs; elim/last_ind: ρts rho_ρs.
  - by move=> _ /=; case: t => [n|t1 t2|t]; auto.
  - move=> ρts ρt _ rho_ρs; rewrite map_rcons CAppS_rcons.
    apply/HCApp=> //=.
    * by move=> ρt' ρt'in; apply/rho_ρs; rewrite mem_rcons mem_behead.
    * by apply/rho_ρs; rewrite mem_rcons mem_head.
+ by move=> c stc Pc; apply/HCLam.
+ by move=> n nfc c ρts stc Pc nf_nfc rho_ρs; apply/HClo.
Qed.

End StcCase.

(* -------------------------------------------------------------------- *)
Lemma L_5_11 l (S M M' : closure) :
  wfc l S -> IsStc S -> M → M' -> S →_[σ, l] M ->
    exists X, [/\ wfc l X, IsExc X & S →*_[ρ, l] X].
Proof.
rewrite /SigmaRed => wfS stc rd ME; subst M.
elim/hind: S M' l stc rd wfS => S ih M' l h; elim/stccase: h ih => /=.
* move=> n ρ rho_ρ ih; rewrite scE /=; case: ltnP; last first.
  + by rewrite ?c2tE => _ /NoVar[].
  move=> lt_nρ rdn wfn; set c' := nth _ _ _ in rdn.
  move/mem_nth: (lt_nρ) => /(_ ⌊0⌋) /mem_wf -/(_ l).
  inversion wfn using wfc_closI => wfρ /(_ wfρ) [].
  + case=> x c'E; move: rdn; rewrite /c' c'E scE c2tE.
    by case/inv_noredbeta_var.
  rewrite -/c'; case=> [T] [ρ'] [l'] [c'E wf' lel].
  case/(_ c' _ M' l): ih => //.
  + by apply/lth_clos.
  + rewrite c'E; apply (@Stc1 _ _ [::]) => //.
    move/mem_nth: (lt_nρ) => /(_ ⌊0⌋) /mem_IsRhoS.
    case/(_ rho_ρ) => [[k]|]; first by rewrite -/c' c'E.
    by case=> [ρ''] [T']; rewrite -/c' c'E => -[] [_ ->].
  + rewrite c'E; constructor; apply(@wf_strg _ l').
    - by apply lel. by apply wf'.
  move=> X [wfX exX rdX]; exists X; split=> //.
  apply/(@rt_trans _ _ _ c') => //; apply/rt_step.
  constructor; rewrite /c' (set_nth_default ^0) //.
  by constructor.
* move=> t1 t2 ρ rho_ρ ih; rewrite /= scE; set c := (X in sc X).
  move=> scd wfd; case/(_ c _ M' l): ih => //.
  + by rewrite /c [X in _ < X]hE.
  + apply: (@Stc1 _ _ [:: (ρ, t2) ]) => //=.
    by move=> ρt; rewrite mem_seq1 => /eqP ->.
  + by do 2! constructor; elim/wfc_clos: wfd.
  move=> X [wfX exX rdX]; exists X; split=> //.
  apply/(rt_trans _ _ _ c) => //; apply/rt_step.
  by apply/NoCBase; constructor.
* move=> t ρ rho_ρ ih; rewrite /= scE; set c := (X in sc X).
  move=> scd wfd; case/(_ c _ M' l): ih => //.
  + by apply/lth_clos_lam.
  + constructor; apply/(@Stc1 _ _ [::]) => //.
    by apply/RhoS2.
  + by elim/wfc_clos: wfd => wfd; do 3! constructor.
  move=> X [wfX exX rdX]; exists X; split=> //.
  apply/(rt_trans _ _ _ c) => //; apply/rt_step.
  by apply/NoCBase; constructor.
* move=> c st ih rd wfd; move: rd; rewrite scE c2tE.
  case/NoLam => sM' [rM' M'E].
  case/(_ c _ (closure_of_term sM') l.+1 st): ih => //.
  - by rewrite [X in _ < X]hE.
  - by rewrite {2}/term_of_closure_r -lock closure_of_termK.
  - by elim/wfc_lam: wfd.
  move=> X [wfX exX rdX]; exists (λλ [X]); split.
  - by constructor.
  - by constructor.
  by apply rhored_trans_lam.
* move=> t u ρt ρu rho_ρt rho_ρu ih _ wfd.
  exists (λλ [ξ [^l.+1 :: ρt] t] ○ ξ [ρu] u); split.
  + elim/wfc_app: wfd => wf1 wf2; constructor => //.
    do 3! constructor => //; elim/wfc_clos: wf1 => wf1.
    by apply/(wfr_strg _ wf1).
  + apply/(@Exc1 _ _ _ [:: (ρu, u)]) => //.
    by move=> ?; rewrite mem_seq1 => /eqP->.
  apply/rt_step; apply/NoCμ1; last by do 2! constructor.
  set c := (X in IsWhnfC X) => hX; move: {-2}c hX (erefl c).
  rewrite {}/c => c; case=> // n; elim/last_ind=> // s x _.
  by rewrite CAppS_rcons.
* move=> n nfc c stc nf_nfc ih rd wfd; move: rd.
  rewrite scE sc_appS scE !(c2tE,c2t_appS) -map_comp /=.
  move=> rd; case/NoRed_varappsnf_app: (rd).
  + move=> t /mapP[ct /= hct ->]; apply/IsNfC_IsNf.
    by apply/IsNfC_sc/nf_nfc.
  move=> u [rdu M'E]; case: (ih c _ (closure_of_term u) l) => //.
  + by rewrite [X in _ < X]hE ltnS leq_addl.
  + by rewrite {2}/term_of_closure_r -lock closure_of_termK.
  + by elim/wfc_app: wfd.
  move=> X [wfX exX rdX]; exists (⌊n⌋ ○! nfc ○ X); split.
  + by constructor=> //; elim/wfc_app: wfd.
  + by apply/(@Exc3 _ _ _ [::]).
  apply/rhored_trans_appR=> //.
  + by constructor=> c'; apply/nf_nfc.
  + by elim/last_ind: {+}nfc => [|? ? _]; last rewrite CAppS_rcons.
* move=> c u ρ stc rho_ρ ne1 ne2 ne3 ih; rewrite scE c2tE => rd.
  have ntc: IsNeutral (sc c l); first case: stc ne1 ne2 ne3.
  - move=> ρ' t ρts rho_ρ' _ ne1 _ _; elim/last_ind: ρts ne1; last first.
    + move=> s x _ _; rewrite sc_appS c2t_appS -!map_comp.
      by rewrite map_rcons AppS_rcons.
    move=> /=; elim: t => {ih} [n|t1 _ t2 _|t _] // ne1.
    + rewrite scE; case: ltnP => [lt|]; last by rewrite c2tE.
      by apply/IsNeutral_rho.
    + by rewrite 2!scE c2tE.
    + by move/(_ t ρ'): ne1.
  - by move=> c' _ _ /(_ c').
  - move=> n nfc c' ρts cs _ _ _ _ _ _; rewrite sc_appS scE sc_appS.
    rewrite !(c2tE, c2t_appS) -!(AppS_cat, AppS_cons).
    set X := (X in _ ·! X); elim/last_ind: X => //=.
    + by rewrite scE c2tE.
    + by move=> s x _; rewrite AppS_rcons.
  have: exists t, sc c l → t.
  - by admit.
  case=> t {rd} rd wfd; have []// := ih c _ (closure_of_term t) l.
  - by rewrite [X in _ < X]hE ltnS leq_addr.
  - by rewrite {2}/term_of_closure_r -lock closure_of_termK.
  - by elim/wfc_app: wfd.
  have nt: IsNeutral c by admit.
  move=> X [wfX exX rdX]; exists (X ○ ξ [ρ] u); split.
  - by constructor=> //; elim/wfc_app: wfd.
  - case: exX.
    + move=> n ρ' t1 ρts cs rho_ρ' _ /= rho_ρts; rewrite -CAppS_rcons.
      rewrite -(map_rcons (fun ρt => ξ [ρt.1] ρt.2) _ (ρ, u)).
      apply/Exc1 => //; [by rewrite size_rcons | move=> ρt].
      by rewrite mem_rcons in_cons => /orP[/eqP->//|]; apply/rho_ρts.
    + admit.
    + move=> /= n nfc c' ρts exc' isnfc rho_ρs.
      rewrite -CAppS_rcons -(map_rcons (fun ρt => ξ [ρt.1] ρt.2) _ (ρ, u)).
      constructor => //= ρt; rewrite mem_rcons in_cons => /orP.
      by case=> [/eqP->//|]; apply/rho_ρs.
  by apply/rhored_trans_appL=> //; case: dec=> hw; tauto.
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
