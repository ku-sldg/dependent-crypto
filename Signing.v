(**
Signing - Simple definitions for message signing and signature checking

Perry Alexander
The University of Kansas

Provides definitions for:
- [is_signed] - proof that signature checking is decidable and provides a decision procedure for signature check. 
- [check] - checks a signature on a message with a given key.  Returns a proof that the check succeeds or does not succeed.
- [check_dec] - proof that signature checking is decidable and provides a decision procedure for signature checking.  Alternative function for [check].


Depends on:
- Crypto.v
*)

Module Signing.

Require Import Omega.
Require Import CpdtTactics.
Require Import Eqdep_dec.
Require Import Peano_dec.
Require Import Coq.Program.Equality.
Require Export Crypto.

(** Generate a signature using encryption and hash *)

Definition sign{t:type}(m:message t)(k:keyType) :=
  (pair t (Encrypt Hash) m (encrypt Hash (hash t m) k)).

Example sign_ex1:
  sign (basic 1) (public 1) =
  pair Basic (Encrypt Hash) (basic 1)
       (encrypt Hash (hash Basic (basic 1)) (public 1)).
Proof.
  cbv. reflexivity.
Qed.

(** [hash_eq_dec] is currently admitted and not usable. *)

Theorem hash_eq_dec: forall t1 t2 m1 m2,
    {hash t1 m1 = hash t2 m2} + {hash t1 m1 <> hash t2 m2}.
Proof.
  dependent induction m1; dependent induction m2.
  eq_not_eq (eq_nat_dec n n0).
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  eq_not_eq (eq_key_dec k k0).
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  destruct (eq_type_dec t t0). subst.
Admitted.


(** [message_eq_lemma] is currently unused. *)

Theorem message_eq_lemma: forall t, forall m:(message t), forall m':(message t), forall k k',
    {m=m'}+{m<>m'} ->
    {k=k'}+{k<>k'} ->
    {(encrypt t m k)=(encrypt t m' k')}+{(encrypt t m k) <> (encrypt t m' k')}.
Proof.
  intros.
  destruct H; destruct H0.
  left; subst; reflexivity.
  right; subst; unfold not; intros; inversion H; contradiction.
  right. subst. unfold not. intros. inversion H. apply inj_pair2_eq_dec in H1. contradiction.
  apply eq_type_dec.
  right. unfold not. intros. inversion H. apply inj_pair2_eq_dec in H1. contradiction.
  apply eq_type_dec.
Defined.

Hint Resolve message_eq_lemma.

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

Fixpoint message_eq{t1 t2:type}(m1:message t1)(m2:message t2):Prop :=
  if (eq_type_dec t1 t2)
  then match m1 with
       | basic x => match m2 with
                   | basic y => x = y
                   | _ => False
                   end
       | hash _ x => match m2 with
                    | hash _ y => message_eq x y
                    | _ => False
                    end
       | key k => match m2 with
                 | key k' => k = k'
                 | _ => False
                 end
       | encrypt _ m k => match m2 with
                         | encrypt _ m' k' => message_eq m m' /\ k = k'
                         | _ => False
                         end
       | pair _ _ p1 p2 => match m2 with
                          | pair _ _ p1' p2' => message_eq p1 p1' /\ message_eq p2 p2'
                          | _ => False
                          end
       | bad _ => match m2 with
                 | bad _ => True
                 | _ => False
                 end
       end
  else False.

Theorem message_eq_dec: forall t1 t2, forall m1:(message t1), forall m2:(message t2),
        {(message_eq m1 m2)} + {not (message_eq m1 m2)}.
Proof.
  dependent induction m1; dependent induction m2;
    match goal with
    | [  |- {message_eq (basic ?X) (basic ?Y)} + {~ message_eq (basic ?X) (basic ?Y)} ] =>
      (eq_not_eq (eq_nat_dec X Y))
    | [  |- {message_eq (basic ?X) (bad ?T)} + {~ message_eq (basic ?X) (bad ?T)} ] =>
      (right; unfold not; intros H; unfold message_eq in H; destruct (eq_type_dec Basic t); [ assumption | assumption ])
    | [  |- {message_eq (key ?X) (key ?Y)} + {~ message_eq (key ?X) (key ?Y)} ] => destruct (eq_key_dec k k0); [ left; subst; reflexivity | right; unfold not; intros; simpl in H; contradiction ]
    | [  |- {message_eq (key ?X) (bad ?T)} + {~ message_eq (key ?X) (bad ?T)} ] =>  right; unfold not; intros H; unfold message_eq in H; destruct t; try (simpl in H; tauto)
    | [ J: _ |- _ ] => try tauto (* right; unfold not; intros H; inversion H*)
    end.
  specialize IHm1 with (encrypt t0 m2 k0).
  destruct IHm1.
Admitted.

(*
Theorem message_eq_dec: forall t, forall m:(message t), forall m':(message t), {m=m'}+{m<>m'}.
Proof.
  dependent induction m; dependent induction m'.
  (eq_not_eq (eq_nat_dec n n0)).
  right; unfold not; intros; inversion H.
  (eq_not_eq (eq_key_dec k k0)).
  right; unfold not; intros; inversion H.

  specialize IHm with m'.
  destruct IHm; destruct (eq_key_dec k k0);
  [ left; subst; reflexivity
  | right; unfold not; intros; inversion H; contradiction
  | right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1;
    [contradiction | apply eq_type_dec]
  | right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1;
    [contradiction | apply eq_type_dec]].

  right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1.
  
  destruct (eq_type_dec t t0); subst.
  specialize IHm with m'.
  destruct IHm;
  [ left; subst; reflexivity 
  | right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1;
    [contradiction | apply eq_type_dec]].
  right. unfold not. intros. inversion H. contradiction.

  right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1.

  specialize IHm2 with m'2.
  specialize IHm1 with m'1.
  destruct IHm1; destruct IHm2;
  [ left; subst; reflexivity 
  | right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1; apply inj_pair2_eq_dec in H2; [ contradiction | apply eq_type_dec | apply eq_type_dec | apply eq_type_dec ]
  | right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1; apply inj_pair2_eq_dec in H2; [ contradiction | apply eq_type_dec | apply eq_type_dec | apply eq_type_dec ]
  | right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1; apply inj_pair2_eq_dec in H2; [ contradiction | apply eq_type_dec | apply eq_type_dec | apply eq_type_dec ]].

  right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1.
  right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1.
  right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1.
  right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1.
  right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1.
  right; unfold not; intros; inversion H; apply inj_pair2_eq_dec in H1.
  left; reflexivity.
Defined.
  
Hint Resolve message_eq_dec.
 *)

Definition signed_message_type{t:type}(m:message (Pair t (Encrypt Hash))):type := t.

Definition is_signed{t:type}(m:message (Pair t (Encrypt Hash)))(k:keyType):Prop :=
  match m in (message r) with
  | pair r1 (Encrypt Hash) n n' => match (decrypt n' k) with
                                  | inleft m' => (message_eq (hash r1 n) m')
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

  Theorem check_dec: forall t:type, forall m:message (Pair t (Encrypt Hash)), forall k, {(is_signed m k)}+{not (is_signed m k)}.
  Proof. Admitted.
(*
  destruct k.
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