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

(** Proof that inverse is decidable for any two keys. The resulting proof
 gives us the function [is_inverse] that is a decision procedure for key 
 inverse checking.  It will be used in [decrypt] and [check] later in the
 specification. *)
Theorem is_inverse:forall k k', {k = (inverse k')}+{k <> (inverse k')}.
Proof.
  intros.
  destruct k; destruct k'.
  destruct (eq_nat_dec k k0) as [Hinv | Hninv].
    left. simpl. auto.
    right. simpl. unfold not. intros. inversion H. contradiction.
  right; simpl; unfold not; intros; inversion H.
  right. simpl. unfold not. intros. inversion H.
  right. simpl. unfold not. intros. inversion H.
  right. simpl. unfold not. intros. inversion H.
  destruct (eq_nat_dec k k0) as [Hinv | Hninv].
    left. simpl. auto.
    right. simpl. unfold not. intros. inversion H. contradiction.
  right. simpl. unfold not. intros. inversion H.
  destruct (eq_nat_dec k k0) as [Hinv | Hninv].
    left. simpl. auto.
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

Theorem is_hash(m:message):{exists m':message, m=(hash m')}+{forall m':message, m<>(hash m')}.
Proof.
  destruct m;
  try (left; intros; exists m; reflexivity);
  try (right; intros; unfold not; intros; inversion H).
Defined.

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

Theorem message_eq_dec: forall m m':message, {m=m'}+{m<>m'}.
Proof.
  intros.
  induction m; induction m'.
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
  inversion IHm. subst.
  


  
  
Definition is_signed{T:Type}(m:message T)(k:keyType):Prop :=
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

(** I think I just proved that nothing is signed.  Sigh... *)

Theorem check_dec: forall T, forall m:(message T), forall k, {(is_signed m k)}+{not (is_signed m k)}.
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
        left. unfold not. simpl. split.
        
Defined.
    
Eval compute in check_dec nat (sign (basic nat 1) (private 1)) (public 1).

Eval compute in check_dec nat (sign (basic nat 1) (private 1)) (public 2).

(** Uncomment these Notation definitions if you would rather use [good] and
  [bad] while hiding proof values than use [inleft] and [inright].  This
  enables code that looks like this:

  [if good then ...]

Notation " 'good' " := (left _ _).

Notation " 'bad' " := (right _ _).

Eval compute in check_dec nat (sign nat (basic nat 1) (private 1)) (public 1).

Eval compute in check_dec nat (sign nat (basic nat 1) (private 1)) (public 2).
*)