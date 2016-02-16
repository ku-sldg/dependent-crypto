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

Eval compute in sign (basic 1) (public 1).

Ltac eq_key_helper :=
  match goal with
  | [ |- {symmetric ?P = symmetric ?Q} + {symmetric ?P <> symmetric ?Q} ] =>
    (eq_not_eq (eq_nat_dec P Q))
  | [ |- {public ?P = public ?Q} + {public ?P <> public ?Q} ] =>
    (eq_not_eq (eq_nat_dec P Q))
  | [ |- {private ?P = private ?Q} + {private ?P <> private ?Q} ] =>
    (eq_not_eq (eq_nat_dec P Q))
  | [ |- _ ] => right; unfold not; intros; inversion H
  end.

Theorem eq_key_dec: forall k k':keyType, {k=k'}+{k<>k'}.
Proof.
  intros.
  destruct k; destruct k'; eq_key_helper.
Defined.
  
Hint Resolve eq_key_dec.

Theorem eq_type_dec: forall x y : type, {x = y} + {x <> y}.
Proof.
  induction x, y;
  match goal with
  | [ |- {?T = ?T} + {?T <> ?T} ] => left; reflexivity
  | [ |- {?C ?T = ?C ?U} + {?C ?T <> ?C ?U} ] => specialize IHx with y; destruct IHx; [ left; subst; reflexivity | right; unfold not; intros; inversion H; contradiction ]
  | [ |- {?C ?T ?U = ?C ?T' ?U'} + {?C ?T ?U <> ?C ?T' ?U'} ] => specialize IHx1 with y1; specialize IHx2 with y2; destruct IHx1; destruct IHx2; 
  [ left; subst; reflexivity
   | subst; right; unfold not; intros; inversion H; contradiction
   | subst; right; unfold not; intros; inversion H; contradiction
   | subst; right; unfold not; intros; inversion H; contradiction ]
  | [ |- _ ] => right; unfold not; intros; inversion H 
  end.
  Defined.

Theorem hash_eq_dec: forall t1 t2 m1 m2, {hash t1 m1 = hash t2 m2} + {hash t1 m1 <> hash t2 m2}.
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

Definition signed_message_type{t:type}(m:message (Pair t (Encrypt (Hash t)))):type := t.
  
Definition is_signed{t:type}(m:message (Pair t (Encrypt (Hash t))))(k:keyType):Prop.
  refine match m in (message r) with
         | pair r1 (Encrypt (Hash r2)) n n' => if (eq_type_dec r1 r2)
                                              then match (decrypt n' k) with
                                                   | inleft m' => _
                                                   | inright _ => False
                                                   end
                                              else False
         | _ => False
         end.
  Proof.
    subst.
    apply (if (message_eq_dec _ (hash r2 n) m') then True else False).
  Defined.

  Definition hash_eq{r1 r2:type}(h1:message (Hash r1))(h2:message (Hash r2)):Prop. refine (if (eq_type_dec r1 r2) then True else False).

Definition is_signed'{t:type}(m:message (Pair t (Encrypt (Hash t))))(k:keyType):Prop.
  refine match m with
         | pair r1 (Encrypt (Hash r2)) n n' => if (eq_type_dec r1 r2)
                                              then match (decrypt n' k) with
                                                   | inleft _ => True
                                                   | inright _ => False
                                                   end
                                              else False
         | _ => False
         end.
  Proof.
  Defined.

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

  Example ex4: is_signed' (sign (basic 1) (symmetric 1)) (symmetric 1).
  Proof.
    reflexivity.
  Qed.

  
  Theorem check_dec: forall t:type, forall m:message (Pair t (Encrypt (Hash t))), forall k, {(is_signed m k)}+{not (is_signed m k)}.
  Admitted.

  (* Proof.
  intros.
  destruct m; try tauto.
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
  unfold is_signed. fold (is_signed (t := Basic)).
Admitted.

Example sign_2_ex: not (is_signed (sign (basic 1) (private 1)) (public 2)).
Proof.
  unfold not. intros.
  simpl in H. assumption.
Qed.

(*
Eval compute in check_dec (sign (basic 1) (private 1)) (public 1).

Eval compute in check_dec (sign (basic 1) (private 1)) (public 2).
 *)

Notation " 'good' " := (left _ _).

Notation " 'bad' " := (right _ _).

(*
Eval compute in check_dec (sign (basic 1) (private 1)) (public 1).

Eval compute in check_dec (sign (basic 1) (private 1)) (public 2).
 *)


End Signing.