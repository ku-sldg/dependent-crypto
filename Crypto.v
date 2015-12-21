(** 
Perfect Crypto - Simple definitions for message encryption and signing using
symmetric and assymetric keys

Perry Alexander
The University of Kansas

Provides definitions for:

- [keyType] - [symmetric], [public] and [private] key constructors.
- [inverse] - defines the inverse of any key.
- [is_inverse] - proof that [inverse] is decidable and provides a decision procesure for [inverse].
- [is_not_decryptable] - predicate indicating that a message is or is not decryptable using a specified key.
- [decrypt] - attempts to decrypt a message with a given key.  Returns the decrypted message if decryption occurs.  Returns a proof that the message cannot be decrypted with the key if decryption does not occur.
- [is_signed] - proof that signature checking is decidable and provides a decision procedure for signature check.
- [check] - checks a signature on a message with a given key.  Returns a proof that the check succeeds or does not succeed.
- [check_dec] - proof that signature checking is decidable and provides a decision procedure for signature checking.  Alternative function for [check].
*)

Require Import Omega.
Require Import Ensembles.

Ltac eq_not_eq P := destruct P;
  [ (left; subst; reflexivity) | 
    (right; unfold not; intros; inversion H; contradiction) ].

Ltac eq_not_eq' P Q := destruct P; destruct Q;
  [ (subst; left; reflexivity) |
    (right; unfold not; intros; inversion H; contradiction) |
    (right; unfold not; intros; inversion H; contradiction) |
    (right; unfold not; intros; inversion H; contradiction) ].

(** Key values will be [nat] *)

Definition key_val : Type := nat.

(** Key types are [symmetric], [public] and [private]. *)
Inductive keyType: Type :=
| symmetric : key_val -> keyType
| private : key_val -> keyType
| public : key_val -> keyType.

(** A [symmetric] key is its own inverse.  A [public] key is the inverse of
  the [private] key with the same [key_val].  A [private] key is the inverse of
  the [public] key with the same [key_val]. *)

Fixpoint inverse(k:keyType):keyType :=
match k with
| symmetric k => symmetric k
| public k => private k
| private k => public k
end.

Ltac is_inverse_helper :=
  match goal with
  | [ |- {symmetric ?P = (inverse (symmetric ?Q))}+{symmetric ?P <> (inverse (symmetric ?Q))} ] => (eq_not_eq (eq_nat_dec P Q))
  | [ |- {private ?P = (inverse (public ?Q))}+{private ?P <> (inverse (public ?Q))} ] => (eq_not_eq (eq_nat_dec P Q))
  | [ |- {public ?P = (inverse (private ?Q))}+{public ?P <> (inverse (private ?Q))} ] => (eq_not_eq (eq_nat_dec P Q))
  | [ |- _ ] => right; simpl; unfold not; intros; inversion H
  end.

Theorem is_inverse:forall k k', {k = (inverse k')}+{k <> (inverse k')}.
Proof.
  intros.
  destruct k; destruct k'; is_inverse_helper.
Defined.


(** Proof that inverse is decidable for any two keys. The resulting proof
 gives us the function [is_inverse] that is a decision procedure for key 
 inverse checking.  It will be used in [decrypt] and [check] later in the
 specification. *)
Theorem is_inverse:forall k k', {k = (inverse k')}+{k <> (inverse k')}.
Proof.
  intros.
  destruct k; destruct k'.
  destruct (eq_nat_dec k k0) as [Hinv | Hninv].
    left. subst. reflexivity.
    right. simpl. unfold not. intros. inversion H. contradiction.
  right; simpl; unfold not; intros; inversion H.
  right. simpl. unfold not. intros. inversion H.
  right. simpl. unfold not. intros. inversion H.
  right. simpl. unfold not. intros. inversion H.
  destruct (eq_nat_dec k k0) as [Hinv | Hninv].
    left. subst. reflexivity.
    right. simpl. unfold not. intros. inversion H. contradiction.
  right. simpl. unfold not. intros. inversion H.
  destruct (eq_nat_dec k k0) as [Hinv | Hninv].
    left. subst. reflexivity.
    right. simpl. unfold not. intros. inversion H. contradiction.
  right. simpl. unfold not. intros. inversion H.
Defined.

Eval compute in (is_inverse (public 1) (private 1)).

Eval compute in (is_inverse (public 1) (private 2)).

Eval compute in (is_inverse (public 2) (private 1)).

Eval compute in (is_inverse (private 1) (public 1)).

Eval compute in (is_inverse (symmetric 1) (symmetric 1)).

Eval compute in (is_inverse (symmetric 1) (symmetric 2)).

(** Various proofs for keys and properties of the inverse operation.  All keys
  must have an inverse.  All keys have a unique inverse.  Equal inverses come
  from equal keys *)

Theorem inverse_injective : forall k1 k2, inverse k1 = inverse k2 -> k1 = k2.
Proof.
  intros.
  destruct k1; destruct k2; simpl in H; try (inversion H); try (reflexivity).
Qed.

Hint Resolve inverse_injective.

Theorem inverse_inverse : forall k, inverse (inverse k) = k.
Proof.
  intros. destruct k; try reflexivity.
Qed.

Hint Resolve inverse_inverse.

Theorem inverse_surjective : forall k, exists k', (inverse k) = k'.
Proof.
  intros. exists (inverse k). auto.
Qed.

Hint Resolve inverse_surjective.

Theorem inverse_bijective : forall k k',
    inverse k = inverse k' ->
    k = k' /\ forall k, exists k'', inverse k = k''.
Proof.
  auto.
Qed.

(** Basic messages held abstract.  Compound messages are keys, encrypted and
  signed messages, hashes and pairs. *) 

Inductive message : Type :=
| basic : nat -> message
| key : keyType -> message
| encrypt : message -> keyType -> message
| hash : message -> message
| pair : message -> message -> message.

(** Predicate that determines if a message cannot be decrypted.  Could be
  that it is not encrypted to begin with or the wrong key is used. *)

Definition is_not_decryptable(m:message)(k:keyType):Prop :=
  match m with
  | encrypt m' k' => k <> inverse k'
  | _ => True
  end.

Definition is_decryptable(m:message)(k:keyType):Prop :=
  match m with
  | encrypt m' k' => k = inverse k'
  | _ => False
  end.


(** [decrypt] returns either a decrypted message or a proof of why the message
  cannot be decrypted. *)

Fixpoint decrypt(m:message)(k:keyType):message+{(is_not_decryptable m k)}.
refine
  match m with
  | basic _ => inright _ _
  | key _ => inright _ _
  | encrypt m' j => (if (is_inverse k j) then (inleft _ m') else (inright _ _ ))
  | hash _ => inright _ _
  | pair _ _ => inright _ _
  end.
Proof.
  reflexivity.
  reflexivity.
  simpl. assumption.
  reflexivity.
  reflexivity.
Defined.
  
Eval compute in decrypt(encrypt (basic 1) (symmetric 1)) (symmetric 1).

Eval compute in decrypt(encrypt (basic 1) (symmetric 1)) (symmetric 2).

(** Predicate that determines if a message is properly signed. *)

(** Signature check returns either a proof that the signature is correct
  or a proof that the signature is not correct. *)

Definition sign(m:message)(k:keyType):message :=
  (pair m (encrypt (hash m) k)).

Theorem eq_key_dec: forall k k':keyType, {k=k'}+{k<>k'}.
Proof.
  intros.
  destruct k; destruct k'.
  destruct (eq_nat_dec k k0).
  left. rewrite e. reflexivity.
  right. unfold not. intros. inversion H. contradiction.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  destruct (eq_nat_dec k k0).
  left. rewrite e. reflexivity.
  right. unfold not. intros. inversion H. contradiction.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  destruct (eq_nat_dec k k0).
  left. rewrite e. reflexivity.
  right. unfold not. intros. inversion H. contradiction.
Defined.

Hint Resolve eq_key_dec.

Theorem message_eq_lemma: forall m m' k k',
    {m=m'}+{m<>m'} ->
    {k=k'}+{k<>k'} ->
    {(encrypt m k)=(encrypt m' k')}+{(encrypt m k) <> (encrypt m' k')}.
Proof.
  intros.
  destruct H; destruct H0.
    left. subst. reflexivity.
    right. unfold not. intros. inversion H. contradiction.
    right. unfold not. intros. inversion H. contradiction.
    right. unfold not. intros. inversion H. contradiction.
Qed.

Hint Resolve message_eq_lemma.

Theorem message_eq_dec: forall m m':message, {m=m'}+{m<>m'}.
Proof.
  induction m,m'.
  destruct (eq_nat_dec n n0).
    left. subst. reflexivity.
    right. unfold not. intros. inversion H. contradiction.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  destruct (eq_key_dec k k0).
    left. subst. reflexivity.
    right. unfold not. intros. inversion H. contradiction.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  specialize IHm with m'.
  apply message_eq_lemma. assumption. apply eq_key_dec.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  specialize IHm with m'.
  destruct IHm.
  left. subst. reflexivity.
  right. unfold not. intros. inversion H. contradiction.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  right. unfold not. intros. inversion H.
  specialize IHm1 with m'1.
  specialize IHm2 with m'2.
  destruct IHm1; destruct IHm2.
  subst. left. reflexivity.
  right. unfold not. intros. inversion H. contradiction.
  right. unfold not. intros. inversion H. contradiction.
  right. unfold not. intros. inversion H. contradiction.
Defined.

Ltac whack_right :=
  match goal with
  | [ |- {basic ?P = basic ?Q}+{basic ?P <> basic ?Q} ] => (eq_not_eq (eq_nat_dec P Q))                                                          
  | [ |- {key ?P = key ?Q}+{key ?P <> key ?Q} ] => (eq_not_eq (eq_key_dec P Q))
  | [ |- {encrypt ?P ?P' = encrypt ?Q ?Q'}+{encrypt ?P ?P' <> encrypt ?Q ?Q'} ] => auto 
  | [ H : {?P = ?Q}+{?P <> ?Q} |- {hash ?P = hash ?Q}+{hash ?P <> hash ?Q} ] => (eq_not_eq H)
  | [ H1 : {?P = ?P'}+{?P <> ?P'},
      H2 : {?Q = ?Q'}+{?Q <> ?Q'}
      |- {pair ?P ?Q = pair ?P' ?Q'}+{pair ?P ?Q <> pair ?P' ?Q'} ] => (eq_not_eq' H1 H2)
  | [ |- _ ] => right; unfold not; intros; inversion H
  end.

Theorem message_eq_dec': forall m m':message, {m=m'}+{m<>m'}.
Proof.
  induction m; induction m';
  try (specialize (IHm m'));
  try (specialize (IHm1 m'1));
  try (specialize (IHm2 m'2));
  whack_right.
Defined.

Hint Resolve message_eq_dec'.

Theorem is_hash_dec: forall m h, {h=(hash m)}+{h<>(hash m)}.
Proof.
  intros.
  destruct (message_eq_dec h (hash m)).
  left. assumption.
  right. assumption.
Defined.

Hint Resolve is_hash_dec.

Definition is_signed(m:message)(k:keyType):Prop :=
  match m with
  | (pair m m') => match m' with
                  | encrypt m'' k' =>  match m'' with
                                      | (hash m''') => m=m''' /\ (k = inverse k')
                                      | _ => False
                                      end
                  | _ => False
                  end
  | _ => False
  end.

Example sign_1_ex: is_signed (pair (basic 1) (encrypt (hash (basic 1)) (private 1))) (public 1).
Proof.
  simpl. tauto.
Qed.

Example sign_2_ex: not (is_signed (pair (basic 1) (encrypt (hash (basic 1)) (private 1))) (public 2)).
Proof.
  unfold not. intros.
  simpl in H. inversion H. inversion H1.
Qed.

Theorem check_dec: forall m:message, forall k, {(is_signed m k)}+{not (is_signed m k)}.
Proof.
  intros.
  destruct m.
  right. unfold is_signed. tauto.
  right. unfold is_signed. tauto.
  right. unfold is_signed. tauto.
  right. unfold is_signed. tauto.
  destruct m2.
    right. unfold not. intros. unfold is_signed in H. tauto.
    right. unfold not. intros. unfold is_signed in H. tauto.
    destruct m2.
      right; unfold not; intros; simpl in H; tauto.
      right; unfold not; intros; simpl in H; tauto.
      right; unfold not; intros; simpl in H; tauto.
      destruct (is_inverse k k0).
        destruct (message_eq_dec m1 m2).
          left. subst. simpl. tauto.
          right. unfold not. intros. simpl in H. tauto.
        right. unfold not. intros. simpl in H. tauto.
      right. unfold not. intros. simpl in H. assumption.
      right. unfold not. intros. simpl in H. assumption.
      right. unfold not. intros. simpl in H. assumption.
Defined.
            
Eval compute in check_dec (sign (basic 1) (private 1)) (public 1).

Eval compute in check_dec (sign (basic 1) (private 1)) (public 2).

Notation " 'good' " := (left _ _).

Notation " 'bad' " := (right _ _).

Eval compute in check_dec (sign (basic 1) (private 1)) (public 1).

Eval compute in check_dec (sign (basic 1) (private 1)) (public 2).

Theorem m2 : forall P Q R: Prop, P -> Q -> R -> Q.
Proof.
  intros. match goal with | [ B : _ |- _ ] => exact B end.
Qed.                                                 

(** [notHyp] determines if [P] is in the assumption set of a proof state.
  The first match case simply checks to see if [P] matches any assumption and
  fails if it does.  The second match case grabs everything else.  If [P]
  is a conjunction, it checks to see if either of its conjuncts is an
  assumption calling [notHyp] recursively. 

*)

Ltac notHyp P :=
  match goal with
  | [ _ : P |- _ ] => fail 1
  | _ =>
    match P with
    | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
    | _ => idtac
    end
  end.
                           
Ltac extend pf :=
  let t := type of pf in
  notHyp t; generalize pf; intro.