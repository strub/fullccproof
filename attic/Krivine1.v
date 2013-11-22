Require Import List Lt Le Compare_dec Minus Recdef Max.

(*****************************************************************************)
(* Naming cases *)
Open Scope list_scope.

Require String. Open Scope string_scope.

Ltac move_to_top x :=
  match reverse goal with
    | H : _ |- _=> try move x after H
  end.

Tactic Notation "assert_eq" ident(x) constr(v) :=
  let H := fresh in
  assert (x = v) as H by reflexivity;
    clear H.

Tactic Notation "Case_aux" ident(x) constr(name) :=
  first [
      set (x := name); move_to_top x
    | assert_eq x name; move_to_top x
    | fail 1 "because we are working on a different case" ].

Tactic Notation "Case" constr(name) := Case_aux Case name.
Tactic Notation "SCase" constr(name) := Case_aux SCase name.
Tactic Notation "SSCase" constr(name) := Case_aux SSCase name.
Tactic Notation "SSSCase" constr(name) := Case_aux SSSCase name.
Tactic Notation "SSSSCase" constr(name) := Case_aux SSSSCase name.
Tactic Notation "SSSSSCase" constr(name) := Case_aux SSSSSCase name.
Tactic Notation "SSSSSSCase" constr(name) := Case_aux SSSSSSCase name.

(*****************************************************************************)
(* Terms *)

Inductive lambda_term : Type :=
| Ind : nat -> lambda_term
| Lam : lambda_term -> lambda_term
| App : lambda_term -> lambda_term -> lambda_term.

(* Substitution *)

Fixpoint update (m : nat) (n : nat) (t : lambda_term) : lambda_term :=
  match t with
    | (Ind p) as i=>
      match nat_compare p n with
        | Gt => Ind (p + m)
        | _ => i
      end
    | Lam body => Lam (update m (n + 1) body)
    | App rator rand => App (update m n rator) (update m n rand)
  end.

Fixpoint substitute (t : lambda_term) (sub : lambda_term) (n : nat)
: lambda_term :=
  match t with
    | (Ind m) as i =>
      match nat_compare m n with
        | Eq => update n 0 sub
        | Gt => Ind (m - 1)
        | Lt => i
      end
    | Lam body => Lam (substitute body sub (n + 1))
    | App rator rand => App (substitute rator sub n) (substitute rand sub n)
  end.

(* Small-step call-by-name *)

Fixpoint cbn (t : lambda_term) : option lambda_term :=
  match t with
    | Ind n => None
    | Lam b => None
    | App m n =>
      match cbn m with
        | Some m' =>
          match m' with
            | Lam b => Some (substitute m n 0)
            | _ => Some (App m' n)
          end
        | None => None
      end
  end.

Fixpoint nor (t : lambda_term) : option lambda_term :=
  match t with
    | Ind n => None
    | Lam b =>
      match nor b with
        | Some b' => Some (Lam b')
        | None => None
      end
    | App m n =>
      match cbn m with
        | Some m' =>
          match m' with
            | Lam b => Some (substitute m n 0)
            | _ => Some (App m' n)
          end
        | None =>
          match nor m with
            | Some m' => Some (App m' n)
            | None =>
              match nor n with
                | Some n' => Some (App m n')
                | None => None
              end
          end
      end
  end.

(*****************************************************************************)
(* Closures *)


Inductive bind : Type :=
| Bind : lambda_term -> list bind -> bind
| Par : nat -> bind.

Definition environment := list bind.

Inductive closure : Type :=
| Clo : lambda_term -> environment -> closure
| CLam : closure -> closure
| CApp : closure -> closure -> closure
| Lev : nat -> closure
| Grd : nat -> closure.

Definition term := prod closure nat.

Inductive lower: term -> term -> Prop :=
(* | LBind : *)
(*     forall (t : lambda_term) (l : nat) *)
(*            (e e' : environment) (n : nat), *)
(*        (nth n e (Par 0) = Bind t e') *)
(*        -> lower (Clo t e', l) (Clo (Ind n) e, l) *)


   (* forall (t : term) (c : closure) (l : nat) (t0 : lambda_term) *)
   (*   (e : environment) (n : nat), *)
   (* t0 = Ind n -> *)
   (* c = Clo (Ind n) e -> *)
   (* t = (Clo (Ind n) e, l) -> *)
   (* forall (t' : lambda_term) (e' : list bind), *)
   (* nth n e (Par 0) = Bind t' e' -> lower (Clo t' e', l) (Clo (Ind n) e, l) *)


| LLam :
    forall (l : nat) (e : environment) (b : lambda_term),
      lower (CLam (Clo b (Par l :: e)), l + 1) (Clo (Lam b) e, l)
(* | LCLam : *)
(*    forall (l : nat) (cb : closure), *)
(*    lower (cb, l) (CLam cb, l) *)
(* | LAppL : *)
(*     forall (l : nat) (e : environment) (m n : lambda_term), *)
(*     lower (Clo n e, l) (Clo (App m n) e, l) *)
.

Lemma wf_lower :
  well_founded lower.
  unfold well_founded.
  intros a.
  apply Acc_intro.
  (* intros y H. *)
  (* inversion H. *)
  (* induction e as [| b1 e1]. *)
  (* Case "e = nil". *)
  (*   assert (H3 : nth n nil (Par 0) = Par 0). *)
  (*   SCase "nth ... = Par 0". *)
  (*     simpl. case n; reflexivity. *)
  (*   exfalso. *)
  (*   rewrite H0 in H3. admit. (* prove False from the inconsistent assumption *) *)
  (* Case "e = b1 :: e1". *)
  (*   apply Acc_intro. *)
  (*   intros. *)
    

  (* SCase "length nil <= 0". *)
  (*   simpl. apply le_0_n. *)
  (*   assert (H4 : nth n e *)
  (*   apply Acc_intro. *)
  (*   intros y0 H3. *)
  (*   inversion H3. *)
  Case "Lam".
    apply Acc_intro.
    intros y0 H2.
    inversion H2.
    apply Acc_intro.
    intros y1 H4.
    inversion H4.
  (* Case "AppL". *)
  (*   apply Acc_intro. *)
  (*   intros y0 H2. *)
  (*   inversion H2. *)
  (*   SCase "--Lam". *)
  (*     apply Acc_intro. *)
  (*     intros. *)
  (*     inversion H4. *)
    (* admit. *)
    (* admit. *)
Qed.


Function height (t : term) {wf lower t}: nat :=
  match t with
    | (Clo t e, l)    =>
      match t with
        (* | Ind n   => let b := nth n e (Par 0) *)
        (*              in match b with *)
        (*                   | Bind t' e' => 1 + height (Clo t' e', l) *)
        (*                   | _          => 0 *)
        (*                 end *)
        | Lam b   => height (CLam (Clo b ((Par l) :: e)), l + 1)
        (* | App m n => height (CApp (Clo m e) (Clo n e), l) *)
        | _       => 0
      end
    (* | (CLam cb, l)    => 1 + height (cb, l) *)
    (* | (CApp cm cn, l) => max (height (cm, l)) (height (cn, l)) *)
    (* | (Lev n, l)      => 0 *)
    (* | (Grd n, l)      => 0 *)
    | _               => 0
  end.
Proof.
  (* Case "Bind". *)
  (*   intros t c l t0 e n H1 H2 H3 t' e'. *)
  (*   apply LBind. *)
  Case "Lam".
    intros.
    apply LLam.
  (* Case "AppL". *)
  (*   apply LAppL *)
  Case "wf".
    apply wf_lower.
Qed.
