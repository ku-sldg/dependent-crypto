(** 
Perfect Crypto - Simple definitions for message encryption using
symmetric and assymetric keys

Perry Alexander
The University of Kansas

Provides definitions for:

- [keyType] - [symmetric], [public] and [private] key constructors.
- [inverse] - defines the inverse of any key.
- [is_inverse] - proof that [inverse] is decidable and provides a decision procesure for [inverse].
- [is_not_decryptable] - predicate indicating that a message is or is not decryptable using a specified key.
- [decrypt] - attempts to decrypt a message with a given key.  Returns the decrypted message if decryption occurs.  Returns a proof that the message cannot be decrypted with the key if decryption does not occur.
*)

Require Import Omega.
Require Import Ensembles.
Require Import Eqdep_dec.
Require Import Peano_dec.
Require Import Coq.Program.Equality.

(** Ltac helper functions for discharging cases generated from sumbool types
  using one or two boolean cases. *)

Ltac eq_not_eq P := destruct P;
  [ (left; subst; reflexivity) |
    (right; unfold not; intros; inversion H; contradiction) ].

Ltac eq_not_eq' P Q := destruct P; destruct Q;
  [ (subst; left; reflexivity) |
    (right; unfold not; intros; inversion H; contradiction) |
    (right; unfold not; intros; inversion H; contradiction) |
    (right; unfold not; intros; inversion H; contradiction) ].

(** Key values will be [nat] by default.  Could be anything satisfying
 properties following.  *)

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
  intros;
  destruct k; destruct k';
  match goal with
  | [ |- {symmetric ?P = (inverse (symmetric ?Q))}+{symmetric ?P <> (inverse (symmetric ?Q))} ] => (eq_not_eq (eq_nat_dec P Q))
  | [ |- {private ?P = (inverse (public ?Q))}+{private ?P <> (inverse (public ?Q))} ] => (eq_not_eq (eq_nat_dec P Q))
  | [ |- {public ?P = (inverse (private ?Q))}+{public ?P <> (inverse (private ?Q))} ] => (eq_not_eq (eq_nat_dec P Q))
  | [ |- _ ] => right; simpl; unfold not; intros; inversion H
  end.
Defined.

(** I don't like these proofs.  They seem crude and are not clean.  Still
 working on them *)

Example is_inverse_ex1: forall n, if (is_inverse (public n) (private n)) then True else False.
Proof.
  intros; destruct (is_inverse (public n) (private n));
  [ trivial | 
    unfold not in n0; unfold inverse in n0; apply n0; reflexivity ].
Qed.

Example is_inverse_ex2: forall n m, n<>m -> if (is_inverse (public n) (private m)) then False else True.
Proof.
  intros; destruct (is_inverse (public n) (private m));
  trivial.
  unfold inverse in e; unfold inverse in e; inversion e; contradiction.
Qed.
  
Example is_inverse_ex3: forall n m, n=m -> if (is_inverse (symmetric m) (symmetric n)) then True else False.
Proof.
  intros; destruct (is_inverse (symmetric m) (symmetric n));
    trivial.
  subst. unfold not in n0. simpl in n0. apply n0. reflexivity.
Qed.

Example is_inverse_ex4: forall n m, n<>m -> if (is_inverse (symmetric m) (symmetric n)) then False else True.
Proof.
  intros; destruct (is_inverse (symmetric m) (symmetric n));
    trivial.
  unfold inverse in e; inversion e. symmetry in H1. contradiction.
Qed.

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
  intros; destruct k; try reflexivity.
Qed.

Hint Resolve inverse_inverse.

Theorem inverse_surjective : forall k, exists k', (inverse k) = k'.
Proof.
  intros; exists (inverse k); auto.
Qed.

Hint Resolve inverse_surjective.

Theorem inverse_bijective : forall k k',
    inverse k = inverse k' ->
    k = k' /\ forall k, exists k'', inverse k = k''.
Proof.
  auto.
Qed.

(** Index type values for crypto functions.  Each type corresponds to a basic
  type or the application of a crypto operation. *)

Inductive type : Type :=
| Basic : type
| Key : type
| Encrypt : type -> type
| Hash : type
| Pair : type -> type -> type.

(** [type] equivalence is decidable.  Should eventually use the built-in
  coq function rather than do this proof. *)

Theorem eq_type_dec: forall x y : type, {x = y} + {x <> y}.
Proof.
  induction x, y;
  match goal with
  | [ |- {?T = ?T} + {?T <> ?T} ] => left; reflexivity
  | [ |- {?C ?T = ?C ?U} + {?C ?T <> ?C ?U} ] =>
    specialize IHx with y; destruct IHx;
      [ left; subst; reflexivity
      | right; unfold not; intros; inversion H; contradiction ]
  | [ |- {?C ?T ?U = ?C ?T' ?U'} + {?C ?T ?U <> ?C ?T' ?U'} ] =>
    specialize IHx1 with y1;
      specialize IHx2 with y2;
      destruct IHx1;
      destruct IHx2; 
      [ left; subst; reflexivity
      | subst; right; unfold not; intros; inversion H; contradiction
      | subst; right; unfold not; intros; inversion H; contradiction
      | subst; right; unfold not; intros; inversion H; contradiction ]
  | [ |- _ ] => right; unfold not; intros; inversion H 
  end.
Defined.

Theorem eq_key_dec: forall k k':keyType, {k=k'}+{k<>k'}.
Proof.
  repeat decide equality.
Defined.

(* intros.
  destruct k; destruct k';
  match goal with
  | [ |- {symmetric ?P = symmetric ?Q} + {symmetric ?P <> symmetric ?Q} ] =>
    (eq_not_eq (eq_nat_dec P Q))
  | [ |- {public ?P = public ?Q} + {public ?P <> public ?Q} ] =>
    (eq_not_eq (eq_nat_dec P Q))
  | [ |- {private ?P = private ?Q} + {private ?P <> private ?Q} ] =>
    (eq_not_eq (eq_nat_dec P Q))
  | [ |- _ ] => right; unfold not; intros; inversion H
  end.
Defined.
 *)

(** Basic messages are natural numbers.  Really should be held abstract, but we
  need an equality decision procedure to determine message equality.  Compound 
  messages are keys, encrypted messages, hashes and pairs. Note that signed
  messages are pairs of a message and encrypted hash. *) 

Inductive message : type -> Type :=
| basic : nat -> message Basic
| key : keyType -> message Key
| encrypt : forall t, message t -> keyType -> message (Encrypt t)
| hash : forall t, message t -> message Hash
| pair : forall t1 t2, message t1 -> message t2 -> message (Pair t1 t2)
| bad : forall t, message t.

Theorem eq_message_dec {t} : forall m m': message t, {m=m'}+{m<>m'}.
Proof.
  intros; destruct t.
  
Abort.

(** Predicate that determines if a message cannot be decrypted.  Could be
  that it is not encrypted to begin with or the wrong key is used. *)

Definition is_not_decryptable{t:type}(m:message t)(k:keyType):Prop :=
  match m with
  | encrypt t m' k' => k <> inverse k'
  | _ => True
  end.

Definition is_decryptable{t:type}(m:message t)(k:keyType):Prop :=
  match m with
  | encrypt t m' k' => k = inverse k'
  | _ => False
  end.

(** Prove that is_not_decryptable and is_decryptable are inverses.  This is a
  bit sloppy.  Should really only have one or the other, but this theorem
  assures they play together correctly.  Note that it is not installed as
  a Hint.  *)

Theorem decryptable_inverse: forall t:type, forall m:(message t), forall k,
    (is_not_decryptable m k) <-> not (is_decryptable m k).
Proof.
  intros.
  split. destruct m; try (tauto).
  simpl. intros. assumption.
  intros. destruct m; try (reflexivity).
  simpl. tauto.
Qed.  

(** Type-level function to determine the type of a decrypted thing. *)

Definition decrypt_type(t:type):type :=
  match t with
  | Encrypt t' => t'
  | _ => t
  end.

(** [decrypt] returns either a decrypted message or a proof of why the message
  cannot be decrypted.  Really should be able to shorten the proof. *)

                 
Fixpoint decrypt{t:type}(m:message (Encrypt t))(k:keyType):message t+{(is_not_decryptable m k)}.
  refine match m in message t' return message (decrypt_type t') + {(is_not_decryptable m k)} with
         | basic _ => inright _ _
         | key _ => inright _ _
         | encrypt t m' j => (if (is_inverse k j) then (inleft _ m') else (inright _ _ ))
         | hash _ _ => inright _ _
         | pair _ _ _ _ => inright _ _
         | bad _ => inright _ _
         end.
Proof.
  reflexivity.
  reflexivity.
  simpl. assumption.
  reflexivity.
  reflexivity.
  reflexivity.
Defined.

Example decrypt_ex1: decrypt(encrypt Basic (basic 1) (symmetric 1)) (symmetric 1) = inleft (basic 1).
Proof.
  cbv. reflexivity.
Qed.

Example decrypt_ex2: decrypt(encrypt Basic (basic 1) (symmetric 1)) (symmetric 2) <> inleft (basic 1).
Proof.
  cbv. unfold not. intros. inversion H.
Qed.

(** Tactics from CPDT that are currently unused *)

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

