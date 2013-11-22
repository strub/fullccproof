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

Inductive Fin : nat -> Type :=
| First : forall {n : nat}, Fin (S n)
| Next : forall {n : nat}, Fin n -> Fin (S n).

Inductive Exists (A : Type) (P : A -> Prop) (Q : A -> Type) : Type :=
  witness : forall (x : A), P x -> Q x -> Exists A P Q.

Inductive bind : nat -> Type :=
| Bind : forall {m n : nat},
           lambda_term -> environment m -> m < (S n) -> bind (S n)
| Par : forall {n : nat}, nat -> bind n

with environment : nat -> Type :=
| Env : forall {n : nat},
          Fin n -> Exists nat (fun m => m <= n) bind -> environment n.

Definition env (n : nat) := Fin n -> Exists nat (fun m => m <= n) bind.

Lemma Env_0_inv (n : nat) : Fin 0 -> Exists nat (fun m => m <= n) bind.
  inversion 1.
Qed.

Definition enil : env 0 := Env_0_inv 0.

Lemma stub : forall {n : nat}, Exists nat (fun m : nat => m <= S n) bind.
  admit.
Qed.

Definition econs (n : nat) (b : bind (S n)) (e : env n) : env (S n) :=
  let P :=
      fun k =>
        match k return Type with
          | O => Empty_set
          | S n' => env n' -> Exists nat (fun m => m <= S n) bind
        end
  in
  fun i =>
    match i in Fin Sn return P Sn with
      | First n'
        => fun e' => witness nat   (fun m => m <= S n) bind
                             (S n) (le_refl (S n))     b
      | Next n' i'
        => fun e'
           => match e' i' with
                | witness m' p' b'
                  => match b' with
                       | Par n'' l
                         => witness nat (fun m => m <= S n) bind
                                    n'' (le_refl (S n))     (@Par n'' l)
                            (* stub *)
                       | Bind m'' n'' lt e'' p''
                         => stub
                            (* witness nat (fun m => m <= S n) bind *)
                            (*         m'  (le_refl (S n))     b' *)
                     end
              end
    end e.

Definition ehead {n : nat} (e : env (S n))
: Exists nat (fun m => m <= (S n)) bind :=
  e (@First n).

(* Definition etail {l : nat} (e : env (S l)) : env l := *)
(*   fun i => e (@Next l i). *)

(* Lemma l_S_l_minus_1 : *)
(*   forall {l : nat}, *)
(*     Fin (S (l - 1)) -> Fin l. *)
(*   intros. simpl in H. *)
(* Qed. *)

(* Fixpoint selector (l n : nat) : Fin (S l) := *)
(*   match n with *)
(*     | O => First l *)
(*     | S n' => Next l (l_S_l_minus_1 (selector (l - 1) n')) *)
(*   end. *)

(* Fixpoint enth {l : nat} (n : nat) (e : env (S l)) *)
(* : Exists nat (fun m => m <= (S l)) bind := *)
(*   e (selector l n). *)

Inductive Exists (A : Type) (P : A -> Prop) (Q : A -> Type) : Type :=
  witness : forall (x : A), P x -> Q x -> Exists A P Q.

Inductive bind : nat -> Type :=
| Bind : forall {n : nat}, lambda_term -> environment n -> bind (S n)
| Par : forall {n : nat}, nat -> bind n

with environment : nat -> Type :=
| ENil : environment 0
| ECons : forall {n : nat}, bind (S n) -> environment n -> environment (S n).


Fixpoint enth {l m : nat} (n : nat) (e : environment l)
: Exists nat (fun m => m <= l) bind :=
  let P :=
      fun k =>
        match k return Type with
          | _ => Exists nat (fun m => m <= k) bind
        end
  in
  match n with
    | O => match e in environment Sn return P Sn with
             | ENil => witness nat (fun m => m <= l) bind
                               0   (le_0_n l)        (@Par 0 0)
             (* | ECons n0 b e' => witness nat    (fun m => m <= l) bind *)
             (*                            (S n0)  b *)
             | _ => witness nat (fun m => m <= l) bind
                            0   (le_0_n l)        (@Par 0 0)
           end
    | _ => witness nat (fun m => m <= l) bind
                   0   (le_0_n l)        (@Par 0 0)
  end.

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
