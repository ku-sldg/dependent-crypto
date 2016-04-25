(** 
Crypto Language - Abstract Sytax and Semantics for a simple Crypt Language

Perry Alexander
The University of Kansas

Provides definitions for:
 *)

Require Export CryptoDep.

Set Implicit Arguments.

Inductive type : Type :=
| basicT : type
| keyT : type
| encryptT : type
| signT : type
| pairT : type -> type -> type.

Inductive CryptoLang : type -> Type :=
| Message : message Basic -> CryptoLang basicT
| Key : message Key -> CryptoLang keyT
| Encrypt : forall t, CryptoLang t -> CryptoLang keyT -> CryptoLang encryptT
| Decrypt : forall t1, CryptoLang t1 -> CryptoLang keyT -> forall t2, CryptoLang t2
| Sign : forall t, CryptoLang t -> CryptoLang keyT -> CryptoLang signT
| Pair : forall t1, CryptoLang t1 -> forall t2, CryptoLang t2 -> CryptoLang (pairT t1 t2)
| Bad : forall t1, CryptoLang t1.
                   
(** Message and Key are values *)
Inductive cryptoR : forall t, CryptoLang t -> forall t, message t -> Prop :=
| MessageR: forall m, cryptoR (Message m) m
| KeyR: forall k, cryptoR (Key k) k
| EncryptR: forall p p' k k' c, cryptoR p p' -> cryptoR k k' -> cryptoR (encrypt p' k' c).