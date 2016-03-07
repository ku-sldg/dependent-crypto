(**
Signing - Simple definitions for message signing and signature checking

Perry Alexander
The University of Kansas

Provides definitions for:
- [is_signed] - proof that signature checking is decidable and provides a decision procedure for signature check. 
- [check] - checks a signature on a message with a given key.  Returns a proof that the check succeeds or does not succeed.
- [check_dec] - proof that signature checking is decidable and provides a decision procedure for signature checking.  Alternative function for [check].


Depends on:
- DepCrypto.v
*)

Module Signing.

Require Import Omega.
Require Import CpdtTactics.
Require Import Eqdep_dec.
Require Import Peano_dec.
Require Import Coq.Program.Equality.
Require Export Crypto.

(** Generate a signature using encryption and hash *)

Definition sign(m:message)(k:keyType) :=
  (pair m (encrypt (hash m) k)).

Example sign_ex1:
  sign (basic 1) (public 1) =
  pair (basic 1)
       (encrypt (hash (basic 1)) (public 1)).
Proof.
  cbv. reflexivity.
Qed.

(** [message_eq_lemma] is currently unused. *)

(** [whack_right] is an experimental ltac function that was used to prove
 decidability of message equality.  It is currently unused. *)

Ltac whack_right :=
  match goal with
  | [ |- {basic ?P = basic ?Q}+{basic ?P <> basic ?Q} ] =>
    (eq_not_eq (eq_nat_dec P Q))
  | [ |- {key ?P = key ?Q}+{key ?P <> key ?Q} ] =>
    (eq_not_eq (eq_key_dec P Q))
  | [ |- {encrypt ?P ?P' = encrypt ?Q ?Q'}+{encrypt ?P ?P' <> encrypt ?Q ?Q'} ] =>
    auto 
  | [ H : {?P = ?Q}+{?P <> ?Q} |- {hash ?P = hash ?Q}+{hash ?P <> hash ?Q} ] =>
    (eq_not_eq H)
  | [ H1 : {?P = ?P'}+{?P <> ?P'},
      H2 : {?Q = ?Q'}+{?Q <> ?Q'}
      |- {pair ?P ?Q = pair ?P' ?Q'}+{pair ?P ?Q <> pair ?P' ?Q'} ] =>
    (eq_not_eq' H1 H2)
  | [ |- _ ] => right; unfold not; intros; inversion H
  end.

Fixpoint message_eq(m1 m2:message):Prop :=
  match m1 with
  | basic x => match m2 with
              | basic y => x = y
              | _ => False
              end
  | hash x => match m2 with
             | hash y => message_eq x y
             | _ => False
             end
  | key k => match m2 with
            | key k' => k = k'
            | _ => False
            end
  | encrypt m k => match m2 with
                  | encrypt m' k' => message_eq m m' /\ k = k'
                  | _ => False
                  end
  | pair p1 p2 => match m2 with
                 | pair p1' p2' => message_eq p1 p1' /\ message_eq p2 p2'
                 | _ => False
                 end
  | bad => match m2 with
          | bad => True
          | _ => False
          end
  end.

Theorem message_eq_dec: forall m1 m2:(message),
    {(message_eq m1 m2)} + {not (message_eq m1 m2)}.
Proof.
  induction m1; induction m2;
  match goal with
    | [ |- {message_eq (basic ?X) (basic ?Y)} + {~ message_eq (basic ?X) (basic ?Y)} ] =>
      (eq_not_eq (eq_nat_dec X Y))
    | [ |- {message_eq (key ?X) (key ?Y)} + {~ message_eq (key ?X) (key ?Y)} ] => destruct (eq_key_dec k k0); [ left; subst; reflexivity | right; unfold not; intros; simpl in H; contradiction ]
    | [ |- {message_eq (encrypt ?M1 ?K) (encrypt ?M2 ?K0)} +
   {~ message_eq (encrypt ?M1 ?K) (encrypt ?M2 ?K0)} ] => try tauto
    | [ |- _ ] => try tauto (* right; unfold not; intros H; inversion H*)
  end.
  destruct (eq_key_dec k k0); specialize IHm1 with m2. subst. destruct IHm1.
  left. simpl. tauto.
  right. unfold not. intros. inversion H. contradiction.
  right. unfold not. intros. inversion H. contradiction.
  specialize IHm1 with m2. destruct IHm1. left. simpl. tauto.
  right. unfold not. intros. simpl in H. contradiction.

  specialize IHm1_1 with m2_1.
  specialize IHm1_2 with m2_2.
  destruct IHm1_1. destruct IHm1_2.

  left. simpl. tauto.
  right. unfold not. intros. simpl in H.  destruct H; contradiction.
  right. unfold not. intros. simpl in H.  destruct H; contradiction.
  left. reflexivity.
Defined.

Hint Resolve message_eq_dec.

Definition is_signed(m:message)(k:keyType):Prop :=
  match m in message with
  | pair n n' => match (decrypt n' k) with
               | inleft m' => (message_eq (hash n) m')
               | inright _ => False
               end
  | _ => False
  end.

Example ex1: is_signed (sign (basic 1) (private 1)) (public 2) -> False.
Proof.
  simpl. tauto.
Qed.

Example ex2: is_signed (sign (basic 1) (symmetric 1)) (public 2) -> False.
Proof.
  simpl. tauto.
Qed.

Example ex3: is_signed (sign (basic 1) (symmetric 1)) (symmetric 2) -> False.
Proof.
  simpl; tauto.
Qed.

Example ex4: is_signed (sign (basic 1) (symmetric 1)) (symmetric 1).
Proof.
  simpl. tauto.
Qed.

Example ex5: is_signed (sign (basic 1) (private 1)) (public 1).
Proof.
  simpl. tauto.
Qed.

Theorem check_dec: forall m:message, forall k, {(is_signed m k)}+{not (is_signed m k)}.
Proof.
  destruct k.
  destruct m.
  right; unfold not; intros; inversion H.
  right; unfold not; intros; inversion H.
  right; unfold not; intros; inversion H.
  right; unfold not; intros; inversion H.
  destruct (message_eq_dec m2 (encrypt (hash m1) (symmetric k))).
  left. unfold is_signed.




  destruct k;
  destruct m2; try tauto.
    destruct m2; try tauto.
      destruct (is_inverse k k0).
        destruct (message_eq_dec m1 m2); try tauto.
        left. subst. simpl. tauto.
          right. unfold not. intros. simpl in H. tauto.
          right. unfold not. intros. simpl in H. tauto.
   *)
  
Example sign_1_ex: is_signed (sign (basic 1) (private 1)) (public 1).
Proof.
  reflexivity.
Qed.

Example sign_2_ex: not (is_signed (sign (basic 1) (private 1)) (public 2)).
Proof.
  unfold not; intros. simpl in H. assumption.
Qed.

Notation " 'good' " := (left _ _).

Notation " 'bad' " := (right _ _).

Example is_signed_ex1: is_signed (sign (basic 1) (private 1)) (public 1).
Proof.
  cbv. reflexivity.
Qed.

Example is_signed_ex2: is_signed (sign (basic 1) (private 1)) (public 2) -> False.
Proof.
  cbv. tauto.
Qed.

End Signing.