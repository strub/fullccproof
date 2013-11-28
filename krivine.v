(* -------------------------------------------------------------------- *)
Require Import ssreflect eqtype ssrbool ssrnat ssrfun seq Recdef.

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
Definition neutral (t : term) : bool :=
  if t is λ [_] then false else true.

Definition xneutral (t : term) : bool :=
  neutral (curry t).1.

(* -------------------------------------------------------------------- *)
Lemma xneutralP (t : term):
  reflect (exists x ts, t = #x ·! ts) (xneutral t).
Proof.
  apply: (iffP idP); last first.
    by case=> [x] [ts] ->; rewrite /xneutral crcr.
  rewrite /xneutral -{2}[t]curryE; case h: (curry t).1 => [x|u1 u2|u] //= _.
  + by exists x; exists (curry t).2.
  + by move/(congr1 isapp): h; rewrite (negbTE (crNapp _)).
Qed.

(* -------------------------------------------------------------------- *)
Definition iswhnf (t : term) : bool :=
  match curry t with
  | (#(_) , _   ) => true
  | (λ [_], [::]) => true
  | (_    , _   ) => false
  end.

(* -------------------------------------------------------------------- *)
Inductive IsWhnf : term -> Prop :=
| IsWhnfLam : forall t, IsWhnf (λ [t])
| IsWhnfVar : forall x ts, IsWhnf (#x ·! ts).

(* -------------------------------------------------------------------- *)
Lemma iswhnfP (t : term): reflect (IsWhnf t) (iswhnf t).
Proof.
  apply: (iffP idP).
  * rewrite /iswhnf; case h: (curry t) => [ht a].
    rewrite -[t]curryE; case: ht h => [x|u1 u2|u] -> //=.
    + by move=> _; apply: IsWhnfVar.
    + by case: a => [/=|v vs //] _; constructor.
  * by elim=> //= x ts; rewrite /iswhnf crcr.
Qed.

(* -------------------------------------------------------------------- *)
Fixpoint isnf_r (b : bool) (t : term) : bool :=
  match t with
  | λ [t]   => b && (isnf_r true t)
  | #(_)    => true
  | u1 · u2 => (isnf_r false u1) && (isnf_r true u2)
  end.

Definition isnf := fun t => isnf_r true t.

(* -------------------------------------------------------------------- *)
Inductive IsNf : term -> Prop :=
| IsNfLam : forall t, IsNf t -> IsNf (λ [t])
| IsNfVar : forall x ts, (forall t, t \in ts -> IsNf t) -> IsNf (#x ·! ts).

(* -------------------------------------------------------------------- *)
Derive Inversion IsNf_appI with
  (forall t u, IsNf (t · u)) Sort Prop.

Derive Inversion IsNf_appI_r with
  (forall t, IsNf (λ [t])) Sort Prop.

Lemma IsNf_lamI t (P : term -> Prop):
     (IsNf (λ [t]) -> forall u, IsNf t -> u = t -> P t)
  -> IsNf (λ [t]) -> P t.
Proof.
  move=> h; inversion 1 using IsNf_appI_r; first exact: h.
  move=> _ x ts _; elim/last_ind: ts => [|u ts _] //.
  by rewrite AppS_rcons.
Qed.

(* -------------------------------------------------------------------- *)
Lemma isnfP: forall t, reflect (IsNf t) (isnf t).
Proof.                          (* FIXME: refactor using `curry' *)
  pose IsNfI t := exists n ts, (forall u, u \in ts -> IsNf u) /\ t = #n ·! ts.

  have h t b: reflect (if b then IsNf t else IsNfI t) (isnf_r b t).
  + elim: t b => [x|t IHt u IHu|t IHt] b /=; try constructor.
    * by case: b; [apply (@IsNfVar _ [::]) | exists x; exists [::]].
    * case: b IHt IHu => /(_ false) IHt /(_ true) IHu; apply: (iffP idP).
      - case/andP=> /IHt [x [ts [NFts ->]]] /IHu NFu.
        rewrite -AppS_rcons; apply: (@IsNfVar x (rcons ts u)).
        by move=> v; rewrite mem_rcons in_cons => /orP [/eqP->|/NFts].
      - inversion 1 using IsNf_appI=> _ x; elim/last_ind => [//|ts v _].
        move=> NFts; rewrite AppS_rcons=> [[tsE vE]]; apply/andP; split.
        + apply/IHt; rewrite -tsE; exists x; exists ts; split=> // w w_in_ts.
          by apply: NFts; rewrite mem_rcons in_cons w_in_ts orbT.
        + by apply/IHu; apply NFts; rewrite mem_rcons vE in_cons eqxx.
      - case/andP => /IHt [x [ts [NFts ->]]] /IHu NFu.
        exists x; exists (rcons ts u); rewrite -AppS_rcons; split=> //.
        by move=> v; rewrite mem_rcons in_cons => /orP [/eqP->|/NFts].
      - case=> [x] []; elim/last_ind => [[//]|ts v _] [NFts].
        rewrite AppS_rcons=> [[tsE uE]]; apply/andP; split.
        + apply/IHt; exists x; exists ts; rewrite tsE; split=> // w w_in_ts.
          by apply: NFts; rewrite mem_rcons in_cons w_in_ts orbT.
        + by apply/IHu; apply: NFts; rewrite mem_rcons in_cons uE eqxx.
    * case: b IHt => /=; last first.
        constructor=> [[x] []]; elim/last_ind=> [|v ts _] [_] //.
        by rewrite AppS_rcons.
      move/(_ true)=> IH; apply: (iffP idP).
      - by move/IH=> NFt; constructor.
      - by inversion 1 using IsNf_lamI => _ _ NFt _; apply/IH.
  by move=> t; move: (h t true).
Qed.

(* -------------------------------------------------------------------- *)
Fixpoint height (t : term) : nat :=
  match t with
  | #(_)    => 0
  | t1 · t2 => maxn (height t1) (height t2)
  | λ [t]   => (height t).+1
  end.

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
Module HeightI.
  Fixpoint h (c : closure) : nat :=
    match c with
    | ⌊_⌋      => 0
    | ^(_)     => 0
    | λλ [c]   => (h c).+1
    | c1 ○ c2  => (maxn (h c1) (h c2)).+1
    | ξ [cs] t =>
        let fix ht t hs k {struct t} :=
          match t with
          | #i      => if i < k then 1 else nth 0 hs (i-k)
          | λ [t]   => (ht t hs k.+1).+1
          | t1 · t2 => (maxn (ht t1 hs k) (ht t2 hs k)).+1
          end
        in
          ht t [seq (h c).+1 | c <- cs] 0
    end.
End HeightI.

(* -------------------------------------------------------------------- *)
Module Type HeightSig.
  Parameter h  : closure -> nat.
  Parameter hE : h = HeightI.h.
End HeightSig.

Module Height : HeightSig.
  Definition h := HeightI.h.

  Lemma hE : h = HeightI.h.
  Proof. by []. Qed.
End Height.

Notation h := Height.h.
Canonical h_unlock := Unlockable Height.hE.

(* -------------------------------------------------------------------- *)
Fixpoint ht t hs k :=
  match t with
  | #i      => if i < k then 1 else (nth 0 hs (i-k))
  | λ [t]   => (ht t hs k.+1).+1
  | t1 · t2 => (maxn (ht t1 hs k) (ht t2 hs k)).+1
  end.

Lemma hE: forall c,
  h c = match c with
        | ^n               => 0
        | ⌊n⌋              => 0
        | λλ [c]           => (h c).+1
        | c1 ○ c2          => (maxn (h c1) (h c2)).+1
        | ξ [cs] #n        => nth 0 [seq (h c).+1 | c <- cs] n
        | ξ [cs] (λ [t])   => (h (ξ [^0 :: cs] t)).+1
        | ξ [cs] (t1 · t2) => (maxn (h (ξ [cs] t1)) (h (ξ [cs] t2))).+1
        end.
Proof.
  have CE cs t: h (ξ [cs] t) = ht t [seq (h c).+1 | c <- cs] 0.
    by rewrite unlock /=.
  case=> [|n|n|c1 c2|c]; try by rewrite unlock.
  have htE t hs k: ht t hs k = ht t ((nseq k 1) ++ hs) 0.
    elim: t hs k => [n|t1 IH1 t2 IH2|t IH] hs k //=.
    + rewrite nth_cat subn0 size_nseq; case: ltnP=> //.
      by rewrite nth_nseq => ->.
    + by rewrite IH1 IH2.
    + by rewrite IH [X in _=X.+1]IH.
  have nseqhE i cs:
      [seq (h c).+1 | c <- (nseq i ^0) ++ cs]
    = (nseq i 1 ++ [seq (h c).+1 | c <- cs]).
    by rewrite map_cat map_nseq unlock.
  move=> t cs; rewrite CE; have: cs = (nseq 0 ^0) ++ cs by [].
  set i := {1}0; move=> csE; rewrite -{1}/i {-1}csE => {csE}.
  elim: t i => [n|t1 IH1 t2 IH2|t IH] i //=.
  + rewrite map_cat nth_cat size_map size_nseq; case: ltnP=> //.
    move=> lt_ni; rewrite (nth_map ^0) ?size_nseq //.
    by rewrite nth_nseq lt_ni unlock.
  + by rewrite !CE; congr (maxn _ _).+1; rewrite htE nseqhE.
  + by rewrite CE htE -nseqhE.
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
                            else ⌊n - ((size ls + size cs) - l)⌋
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

Notation sc := SC.sc.
Canonical sc_unlock := Unlockable SC.scE.

(* -------------------------------------------------------------------- *)
Fixpoint sct cs t l : closure :=
  match t with
  | #n      => if   n < size cs
               then sc (nth ⌊0⌋ cs n) l
               else ⌊n - (size cs - l)⌋
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
                                   else ⌊n - (size cs - l)⌋
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


(* Reserved Notation "↑ t"           (at level 0, format "↑ t"). *)
(* Reserved Notation "↑ [ k ] t"     (at level 0, format "↑ [ k ] t"). *)
(* Reserved Notation "↑ [ k , n ] t" (at level 0, format "↑ [ k , n ] t"). *)

(* Fixpoint lift k n t := *)
(*   match t with *)
(*   | #x      => if x >= k then #(x+n) else #x *)
(*   | t1 · t2 => ↑[k,n] t1 · ↑[k,n] t2 *)
(*   | λ [t]   => λ [↑[k.+1,n] t] *)
(*   end *)
(*     where "↑ [ k , n ] t" := (lift k n t). *)

(* Notation "↑ [ k ] t" := (↑[k,1] t). *)
(* Notation "↑ t"       := (↑[0] t). *)


(* -------------------------------------------------------------------- *)
Reserved Notation "⇑ [ l ] c"         (at level 0, format "⇑ [ l ] c").
Reserved Notation "⇑ [ k , l ] c"     (at level 0, format "⇑ [ k , l ] c").
Reserved Notation "⇑ [ k , n , l ] c" (at level 0, format "⇑ [ k , n , l ] c").

(* Fixpoint lift_clos k n (l : nat) c : closure := *)
(*   if n == 0 then c *)
(*   else *)
(*     match c with *)
(*       | ⌊x⌋     => if x >= k then ⌊x + n⌋ else ⌊x⌋ *)
(*       | ^i      => let x := ⌊i - l⌋ *)
(*                    in if x >= k then ⌊x + n⌋ else ⌊x⌋ *)
(*       | λλ [cb] => λλ [⇑ [k + 1, n, l + 1] cb] *)
(*       | cm ○ cn => (⇑ [k, n, l] cm) ○ (⇑ [k, n, l] cn) *)
(*       | ξ [r] t => *)
(*         let fix lct k n l ls c : closure := *)
(*             match t with *)
(*               | #i => *)
(*                 let c' := nth ⌊0⌋ ls i *)
(*                 in match c' with *)
(*                      | ⌊0⌋ => (* out of bound *) *)
(*                        let x := i - (size ls - l) *)
(*                        in if x >= k then ⌊x + n⌋ else ⌊x⌋ *)
(*                      | _   => *)
(*                        ξ [take (i - 1) ls ++ *)
(*                                (lct k n l ls c') :: drop i ls] t *)
(*                    end *)
(*               | λ [b]   => lct k n l ls (λλ [ξ [^(l + 1) :: ls] b]) *)
(*               | m1 · m2 => lct k n l ls ((ξ [ls] m1) ○ (ξ [ls] m2)) *)
(*             end *)
(*         in lct k n c l [::] *)
(*     end *)
(*       where "⇑ [ k , n , l ] c" := (lift_clos k n l c). *)
(* ALVARO: I really tried to make it a fixpoint `:| *)

Function lift_clos (k n l : nat) (c : closure) {measure h c} : closure :=
  if n == 0 then c
  else
    match c with
      | ⌊x⌋     => if x >= k then ⌊x + n⌋ else ⌊x⌋
      | ^i      => let x := i - l
                   in if x >= k then ⌊x + n⌋ else ⌊x⌋
      | λλ [cb] => λλ [lift_clos (k + 1) n (l + 1) cb]
      | cm ○ cn => (lift_clos k n l cm) ○ (lift_clos k n l cn)
      | ξ [r] t =>
        match t with
          | #i =>
            let c' := nth ⌊0⌋ r i
            in match c' with
                 | ⌊0⌋ => (* out of bound *)
                   let x := i - (size r - l)
                   in if x >= k then ⌊x + n⌋ else ⌊x⌋
                 | _   =>
                   ξ [take (i - 1) r ++ (lift_clos k n l c') :: drop i r] t
               end
          | λ [b]   => lift_clos k n l (λλ [ξ [^(l + 1) :: r] b])
          | m1 · m2 => lift_clos k n l ((ξ [r] m1) ○ (ξ [r] m2))
        end
    end.
Proof.
  admit. admit. admit. admit. admit.
  admit. admit. admit. admit. admit.
Qed.

(* Notation "⇑ [ k , l ] c" := (⇑[k, 1, l] c). *)
(* Notation "⇑ [ l ] c"     := (⇑[0, l] c). *)
(* ALVARO: What is wrong with this? *)

(* -------------------------------------------------------------------- *)
Lemma lift_clos_n0 c k l: lift_clos k 0 l c = c.
Proof.
  (* elim: c k => /= [n|c IHt u IHu|c IH] k. *)
  (* + by rewrite addn0; case: leqP. *)
  (* + by rewrite !(IHt, IHu). *)
  (* + by rewrite IH. *)
  admit.
Qed.

(* -------------------------------------------------------------------- *)
Coercion term_of_closure_r := term_of_closure #(0).
Coercion term_of_ephemeral : ephemeral >-> term.

(*
(* -------------------------------------------------------------------- *)
Lemma L B N ρ ρ':
    σc (ξ [ξ [ρ'] N :: ρ] B) 0
  = (σc (ξ [^1 :: ρ] B) 1)[!0 ← σc (ξ [ρ'] N) 0] :> term.
Proof.
  elim: B => /= [n|t IHt u IHu|t IHt].
  + case: n => [|n]; last first.
      rewrite ![sc (ξ [_] #(_)) _]scE /= !ltnS; case: ltnP.
        move=> ltn_n_szρ.

Lemma L B N ρ ρ' μ:
    σc (ξ [μ ++ ξ [ρ'] N :: ρ] B) (size μ)
  = (σc (ξ [μ ++ ^1 :: ρ] B) (size μ).+1)[!size μ ← σc (ξ [ρ'] N) (size μ)] :> term.
Proof.
  elim: B μ => /= [n|t IHt u IHu|t IHt] μ.
  + rewrite ![sc (ξ [_] #(_)) _]scE !size_cat /=.

  

(* -------------------------------------------------------------------- *)
Lemma L B N ρ l:
  l <= size ρ ->
      σc (ξ [ξ [ρ] N :: ρ] B) l
    = σc (ξ [ρ] (B[!0 ← N])) l.
Proof.
  move=> le_l_szρ; apply/eqP; rewrite eqE /= !scCE; apply/eqP.
  move: le_l_szρ; rewrite -[_::_]cat0s -{1 4}[ρ]cat0s.
  set μ := [::]; have <-: size μ = 0 by []; move: μ => μ.
  elim: B μ l => [n|t1 IH1 t2 IH2|t IH] /= μ l le_l_szρ.
  + rewrite {1}size_cat; case: (ltnP n (size μ)).
      move=> lt_n_szμ; rewrite ltn_addr //=.
      by rewrite !nth_cat size_cat ltn_addr // lt_n_szμ.
    rewrite leq_eqVlt => /orP [/eqP <- /=|lt_szμ_n].
      rewrite -addSnnS ltn_addr // nth_cat ltnn.
      rewrite subnn /= eqxx scCE; move: le_l_szρ.
      rewrite -[_++_]cat0s -{2}[ρ]cat0s.
      set i := 0; set Ξ := [::]; have ->: i = size Ξ by [].
      elim: {i} N Ξ l => /= [k|t1 IH1 t2 IH2|t IH] Ξ l le_l_sz.
      + rewrite !size_cat [_<=k]leqNgt; case: (ltnP k (size Ξ)) => /=.
          move=> lt_k_szΞ; rewrite ltn_addr //=.
          by rewrite {1}size_cat ltn_addr // 2!nth_cat lt_k_szΞ.
        move=> le_szΞ_k; apply/esym; rewrite 2!{1}size_cat addnA.
        rewrite addnAC ltn_add2r catA nth_cat size_cat.
        rewrite ltn_add2r [k < size Ξ]ltnNge le_szΞ_k /=.
        rewrite subnDr nth_cat [k < size Ξ]ltnNge le_szΞ_k /=.
        case: ltnP => /= [//|]; rewrite -{1}size_cat -catA => le_szΞDszρ.
        admit.
      + by rewrite !(IH1, IH2).
      + by rewrite -cat_cons IH.
    rewrite /leq subnDA subSn 1?ltnW // -/(leq _ _) /= ltnS.
    rewrite eqn_leq [n <= _]leqNgt lt_szμ_n /=.
    rewrite [_.-1<_]/leq [X in n.-1.+1-X]size_cat.
    rewrite subnDA (@ltn_predK (size μ)) // -/(leq _ _).
    case: leqP=> [leq_nBszμ_szρ|]; last first.
      move=> lt_szρ_nBszμ; rewrite !size_cat /= addnS.
      rewrite -size_cat !subnBA // 1?ltnW // subnS.
      case: {lt_szρ_nBszμ} n lt_szμ_n => /= [//|n] _.
      by rewrite addSn subSKn.
    rewrite !nth_cat !ltnNge -![size μ <= _]ltnS.
    rewrite (@ltn_predK (size μ)) // ltnW // lt_szμ_n /=.
    case: n lt_szμ_n leq_nBszμ_szρ => /= [//|n].
    by rewrite ltnS => leq_szμ_n leq_SnBszμ_szρl; rewrite subSn.
  + by rewrite !(IH1, IH2).
  + by rewrite -cat_cons IH.
Qed.
*)

(* -------------------------------------------------------------------- *)
(*                     Small-step call-by-name                          *)
(* -------------------------------------------------------------------- *)
Definition cbn (t : term) : option term :=
  match curry t with
  | (λ [b], u :: a) => Some (b[!0 ← u] ·! a)
  | (_    , _     ) => None
  end.

(* -------------------------------------------------------------------- *)
(*                     Small-step normal order                          *)
(* -------------------------------------------------------------------- *)
Fixpoint nor (t : term) : option term :=
  match t with
  | #(_)      => None
  | λ [b]     => omap (fun b' => λ [b']) (nor b)
  | m · n     => 
      match cbn m with
      | Some (λ [b]) => Some (b[!0 ← n])
      | Some m'      => Some (m' · n)
      | None         =>
          match nor m with
          | Some m' => Some (m' · n)
          | None    => omap (fun (n' : term) => m · n') (nor n)
          end
      end
  end.

(* -------------------------------------------------------------------- *)
Reserved Notation "t '→_no' u" (at level 50, no associativity, format "t  '→_no'  u").

Inductive no : term -> term -> Prop :=
| NOBeta : forall B N, (λ [B]) · N →_no B[!0 ← N]
| NOM1   : forall M M' N, ~ (IsWhnf M) -> M →_no M' -> M · N →_no M' · N
| NOM2   : forall M M' N, IsWhnf M -> (neutral M) -> M →_no M' -> M · N →_no M' · N
| NONu   : forall M N N', IsNf M -> (neutral M) -> N →_no N' -> M · N →_no M · N'
| NOXi   : forall B B', B →_no B' -> λ [B] →_no λ [B']

  where "t '→_no' u" := (no t u).

(* -------------------------------------------------------------------- *)
Lemma whnf_cbn_normal t: IsWhnf t -> cbn t = None.
Proof. by elim=> //= x ts; rewrite /cbn crcr. Qed.

(* -------------------------------------------------------------------- *)
Lemma cbnP: forall t u, cbn t = Some u -> t →_no u.
Proof.
  move=> t v; rewrite /cbn; case h: (curry t) => [ht a].
  rewrite -[t]curryE h /=; case: {h} ht => // b.
  case: a => [//|u us] /= [<-] {t v}.
  elim/last_ind: us => [|vs v IH]; first by constructor.
  rewrite !AppS_rcons; apply: NOM1; last by apply: IH.
  by move/iswhnfP; rewrite -AppS_cons /iswhnf crcr.
Qed.

(* -------------------------------------------------------------------- *)
(* Small-step closure call-by-name *)
Function clos_cbn (c : closure) (l : nat) {measure h c}: option closure :=
  match c with
    | ξ [r] t =>
      match t with
        | #n =>
          match nth ⌊0⌋ r n with
            | (ξ [_] _ | ^_) as c' => clos_cbn c' l
            | ⌊0⌋                  => Some ⌊(n - (length r - l))⌋
            | _                    => None (* imp. case *)
          end
        | λ [b] => Some (λλ [ξ [^(l + 1) :: r] b])
        | m · n => Some ((ξ [r] m) ○ (ξ [r] n))
      end
    | ^n      => Some ⌊l - n⌋
    | λλ [cb] => None
    | cm ○ cn => match clos_cbn cm l with
                   | Some cm' =>
                     match cm' with
                       | λλ [ξ [^_ :: r'] t] => Some (ξ [cn :: r'] t)
                       | λλ [cb]             => None (* imp. case *)
                       | _                   => Some (cm' ○ cn)
                     end
                   | None => None
                 end
    | ⌊n⌋ => None
  end.
Proof.
  (* Subgoal 1 *)
  intros.
  rewrite (hE (ξ [r] #n)).
  rewrite (nth_map ⌊0⌋) ?teq1 //.
  rewrite ltnNge; apply/negP => le_szr_n; move: teq1.
  by rewrite nth_default.
  (* Subgoal 2 *)
  intros.
  rewrite (hE (ξ [r] #n)).
  rewrite (nth_map ⌊0⌋) ?teq1 //.
  rewrite ltnNge; apply/negP => le_szr_n; move: teq1.
  by rewrite nth_default.
  (* Subgoal 3 *)
  intros.
  rewrite (hE (cm ○ cn)).
  admit.
Qed.

(* -------------------------------------------------------------------- *)
(* Small-step closure normal order *)
(* Function clos_nor (c : closure) (l : nat) {measure h c} : option closure := *)
(*   match c with *)
(*     | ξ [r] t => *)
(*       match t with *)
(*         | #n    => match nth ⌊0⌋ r n with *)
(*                      | (ξ [_] _ | ^_) as c' => clos_nor c' l *)
(*                      | ⌊0⌋                  => Some ⌊n - (length r - l)⌋ *)
(*                      | _                    => None (* imp. case *) *)
(*                   end *)
(*         | λ [b] => Some (λλ [ξ [^(l + 1) :: r] b]) *)
(*         | m · n => Some (ξ [r] m ○ ξ [r] n) *)
(*       end *)
(*     | ^n      => Some ⌊l - n⌋ *)
(*     | λλ [cb] => let ob := clos_nor cb (l + 1) *)
(*                  in match ob with *)
(*                       | (Some cb') => Some (λλ [cb']) *)
(*                       | None       => None *)
(*                     end *)
(*     | cm ○ cn => match clos_cbn cm l with *)
(*                    | Some cm' => *)
(*                      match cm' with *)
(*                        | λλ [ξ [^_ :: r'] t] => Some (ξ [cn :: r'] t) *)
(*                        | _ => *)
(*                          let om := clos_nor cm' l *)
(*                          in match om with *)
(*                               | Some cm'' => *)
(*                                 let on := clos_nor cn l *)
(*                                 in match on with *)
(*                                      | Some cn' => Some (cm'' ○ cn') *)
(*                                      | None     => None *)
(*                                    end *)
(*                               | None => None *)
(*                             end *)
(*                      end *)
(*                    | None => None *)
(*                  end *)
(*     | ⌊_⌋ => None *)
(*   end. *)
(* Proof. *)

Lemma clos_nor:
  forall (c : closure) (l : nat), option closure.
  admit.
Qed.

(* -------------------------------------------------------------------- *)
Fixpoint iscneu_r (c : closure) : bool :=
  match c with
    | ⌊_⌋     => true
    | c1 ○ c2 => (iscneu_r c1)
    | _       => false
  end.

Fixpoint iscwhnf_r (c : closure) : bool :=
  match c with
    | λλ [cb] => true
    | _       => iscneu_r c
  end.

Definition iscneu := fun c => iscneu_r  c.

Definition iscwhnf := fun c => iscwhnf_r c.

Fixpoint iscnf_r (b : bool)(c : closure) : bool :=
  match c with
    | λλ [cb] => b && iscnf_r true cb
    | ⌊_⌋     => true
    | c1 ○ c2 => iscnf_r false c1 && iscnf_r true c2
    | _       => false
  end.

Fixpoint iscneunf_r (c : closure) : bool :=
  match c with
    | ⌊_⌋     => true
    | c1 ○ c2 => (iscneunf_r c1) && (iscnf_r true c2)
    | _       => false
  end.

Definition iscneunf := fun c => iscneunf_r c.

Definition iscnf := fun c => iscnf_r true c.

(* -------------------------------------------------------------------- *)
(* Curry thing for closures *)

(* Inductive IsCWhnf : closure -> Prop := *)
(* | IsCWhnfLam : forall c, IsCWhnf (λ [c]) *)
(* | IsCWhnfVar : forall x cs, IsWhnf (#x ·! cs). *)

(* -------------------------------------------------------------------- *)
(* Call-by-name ephemeral expansion *)
Function cbn_eph_exp (c : closure) (l : nat) {measure h c} : closure :=
  match c with
    | ξ [r] t =>
      match t with
        | #n =>
          match nth ⌊0⌋ r n with
            | (ξ [_] _ | ^_) as c' => cbn_eph_exp c' l
            | ⌊0⌋                  => ⌊n - (length r - l)⌋
            | _                    => ⌊0⌋ (* imp. case *)
          end
        | λ [b] => c
        | m · n => cbn_eph_exp (ξ [r] m ○ ξ [r] n) l
      end
    | ^n      => ⌊n - l⌋
    | ⌊_⌋     => c
    | λλ [cb] => c
    | cm ○ cn => let cm' := cbn_eph_exp cm l
                 in cm' ○ cn
  end.
Proof.
admit. admit. admit. admit.
Qed.

(* -------------------------------------------------------------------- *)
(* Normal order ephemeral expansion *)
Function nor_eph_exp (c : closure) (l : nat) {measure h c} : closure :=
  match c with
    | ξ [r] t =>
      match t with
        | #n =>
          match nth ⌊0⌋ r n with
            | (ξ [_] _ | ^_) as c' => nor_eph_exp c' l
            | ⌊0⌋                  => ⌊n - (length r - l)⌋
            | _                    => ⌊0⌋ (* imp. case *)
          end
        | λ [b] => c
        | m · n => nor_eph_exp (ξ [r] m ○ ξ [r] n) l
      end
    | ^n      => ⌊n - l⌋
    | ⌊n⌋     => c
    | λλ [cb] => c
    | cm ○ cn => let cm' := cbn_eph_exp cm l
                 in cm' ○ cn
  end.
Proof.
admit. admit. admit.
Qed.

(* -------------------------------------------------------------------- *)
Fixpoint iscexp_r (b : bool)(c : closure) : bool :=
  match c with
    | λλ [cb] => b && iscexp_r true cb
    | ⌊_⌋     => true
    | (λλ [ξ [^_ :: _] _]) ○ _ => true
    | c1 ○ c2 => (iscexp_r false c1) || (iscnf_r false c1 && iscnf_r true c2)
    | _       => false
  end.

Definition iscexp := fun c => iscexp_r true c.

(* -------------------------------------------------------------------- *)
(* Call-by-name beta contraction *)
Function cbn_beta (c : closure) : option closure :=
  match c with
    | ξ [r] t => None
    | λλ [cb] => None
    | ^n      => None
    | (λλ [ξ [^_ :: r] b]) ○ cn => Some (ξ [cn :: r] b)
    | cm ○ cn => let om := cbn_beta cm
                 in match om with
                      | Some cm' => Some (cm' ○ cn)
                      | None     => None
                    end
    | ⌊_⌋ => None
  end.

(* -------------------------------------------------------------------- *)
(* Normal order beta contraction *)
Function nor_beta (c : closure) (l : nat) : option closure :=
  match c with
    | ξ [r] t => None
    | λλ [cb] => let ob := nor_beta cb (l + 1)
                 in match ob with
                      | Some cb' => Some (λλ [cb'])
                      | None     => None
                    end
    | ^n      => None
    | (λλ [ξ [^_ :: r] b]) ○ cn => Some (ξ [cn :: r] b)
    | cm ○ cn =>
      let om := cbn_beta cm
      in match om with
           | Some cm' => Some (cm' ○ cn)
           | None     =>
             let om' := nor_beta cm l
             in match om' with
                  | Some cm'' => Some (cm'' ○ cn)
                  | None      => let on := nor_beta cn l
                                 in match on with
                                      | Some cn' => Some (cm ○ cn')
                                      | None     => None
                                    end
                end
         end
    | ⌊_⌋ => None
  end.

(* -------------------------------------------------------------------- *)
(* Lemma: ephemeral expansion coincides with multiple-step normal order *)

Fixpoint times_opt {A : Type} (n : nat) (f : A -> option A) (a : A)
: option A :=
  match n with
    | O    => Some a
    | S n' => let oa := f a
              in match oa with
                   | Some a' => times_opt n' f a'
                   | None    => None
                 end
  end.

Lemma eph_mult_nor :
  forall (c : closure) (l : nat), exists (n : nat),
    times_opt n (fun c => clos_nor c 0) c = Some (nor_eph_exp c l).
Proof.
  admit.
Qed.

(* -------------------------------------------------------------------- *)
(* Theorem: reduction commutes with sigmac *)

Definition map_option {A B : Type} (f : A -> B) (o : option A) : option B :=
  match o with
    | Some x => Some (f x)
    | None   => None
  end.

Theorem red_comm_sc :
  forall (t : term),
    map_option (fun c => sc c 0) (nor_beta (nor_eph_exp (ξ [[::]] t) 0) 0) =
    map_option closure_of_term (nor t).


(*
*** Local Variables: ***
*** coq-load-path: ("ALEA" "ssreflect" ".") ***
*** End: ***
 *)
