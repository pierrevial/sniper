(**************************************************************************)
(*                                                                        *)
(*     Sniper                                                             *)
(*     Copyright (C) 2021                                                 *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* If you have installed Sniper, change this line into `Require Import Sniper.Sniper`. *)
Require Import Sniper.
Require Import String.
Require Import ZArith.
Require Import Bool.
Require Import List.
Import ListNotations.




(* A full example coming from CompCert, slightly revisited.
   See: https://hal.inria.fr/inria-00289542
        https://xavierleroy.org/memory-model/doc/Memory.html (Section 3)
 *)


Section NotSoOldCompCert.

  Variable block : Set.
  Hypothesis eq_block : CompDec block.

  Variable mem: Set.
  Hypothesis dec_mem : CompDec mem.
  Variable alloc: mem -> Z -> Z -> (block * mem).
  Variable valid_block: mem -> block -> bool.

  Hypothesis alloc_valid_block_1:
    forall m lo hi b,
      valid_block (snd (alloc m lo hi)) b -> ((b = fst (alloc m lo hi)) \/ valid_block m b).

  Hypothesis alloc_valid_block_2:
    forall m lo hi b,
      ((b = fst (alloc m lo hi)) \/ valid_block m b) -> (valid_block (snd (alloc m lo hi)) b).

  Hypothesis alloc_not_valid_block:
    forall m lo hi,
       negb (valid_block m (fst (alloc m lo hi))).

  Lemma alloc_valid_block_inv m lo hi b :
    valid_block m b -> valid_block (snd (alloc m lo hi)) b.
  Proof.
    intro H. verit (alloc_valid_block_2, H).
  Qed.

  Lemma alloc_not_valid_block_2 m lo hi b' :
    valid_block m b' -> b' <> (fst (alloc m lo hi)).
  Proof.
    intro H. verit (alloc_not_valid_block, H).
  Qed.

End NotSoOldCompCert.


Section CompCertSniper.



(*** from common/AST.v ***)


Inductive typ : Type :=
  | Tint                (**r 32-bit integers or pointers *)
  | Tfloat              (**r 64-bit double-precision floats *)
  | Tlong               (**r 64-bit integers *)
  | Tsingle             (**r 32-bit single-precision floats *)
  | Tany32              (**r any 32-bit value *)
  | Tany64.             (**r any 64-bit value, i.e. any value *)

Lemma typ_eq: forall (t1 t2: typ), {t1=t2} + {t1<>t2}.
Proof. decide equality. Defined.
Global Opaque typ_eq.

Inductive rettype : Type :=
  | Tret (t: typ)                       (**r like type [t] *)
  | Tint8signed                         (**r 8-bit signed integer *)
  | Tint8unsigned                       (**r 8-bit unsigned integer *)
  | Tint16signed                        (**r 16-bit signed integer *)
  | Tint16unsigned                      (**r 16-bit unsigned integer *)
  | Tvoid.                              (**r no value returned *)



Coercion Tret: typ >-> rettype.

Lemma rettype_eq: forall (t1 t2: rettype), {t1=t2} + {t1<>t2}.
Proof. generalize typ_eq; decide equality. Defined.
Global Opaque rettype_eq.

Inductive memory_chunk : Type :=
  | Mint8signed     (**r 8-bit signed integer *)
  | Mint8unsigned   (**r 8-bit unsigned integer *)
  | Mint16signed    (**r 16-bit signed integer *)
  | Mint16unsigned  (**r 16-bit unsigned integer *)
  | Mint32          (**r 32-bit integer, or pointer *)
  | Mint64          (**r 64-bit integer *)
  | Mfloat32        (**r 32-bit single-precision float *)
  | Mfloat64        (**r 64-bit double-precision float *)
  | Many32          (**r any value that fits in 32 bits *)
  | Many64.         (**r any value *)

Definition chunk_eq: forall (c1 c2: memory_chunk), {c1=c2} + {c1<>c2}.
Proof. decide equality. Defined.

(*** from common/Memtype.v ***)

Inductive permission: Type :=
  | Freeable: permission
  | Writable: permission
  | Readable: permission
  | Nonempty: permission.


Inductive perm_order: permission -> permission -> Prop :=
  | perm_refl:  forall p, perm_order p p
  | perm_F_any: forall p, perm_order Freeable p
  | perm_W_R:   perm_order Writable Readable
  | perm_any_N: forall p, perm_order p Nonempty.


(* Definition perm_eq : forall (p1 p2: permission), { p1 = p2 } + { p1 <> p2 }.
Proof. decide equality. Defined. *)
  
(* Scheme Equality for permission. *)

(* boolean version of perm_order *)

Definition perm_orderb p p'  :=
  match (p,p') with
  | (Writable, Writable) => true 
  | (Readable, Readable) => true
  | (Freeable, _) => true
  | (Writable, Readable) => true
  | (_, Nonempty) => true
  | _ => false
end.

Lemma perm_orderb_trans:
  forall p1 p2 p3, perm_orderb p1 p2 -> perm_orderb p2 p3 -> perm_orderb p1 p3.
Proof. 
snipe. (* does not properly work, some goals should be handled *)
admit. admit. admit. admit. 
Admitted. 


Inductive perm_kind: Type :=
  | Max: perm_kind
  | Cur: perm_kind.

Definition block : Type := positive. (* from Values.v *)

Inductive val: Type :=              (* from Values.v *)
  | Vundef: val
  | Vint: int -> val
(*  | Vlong: int64 -> val *)
(*  | Vfloat: float -> val *)
(*  | Vsingle: float32 -> val *)
(*  | Vptr: block -> ptrofs -> val *)
.

Parameter mem: Type.

(** [empty] is the initial memory state. *)
Parameter empty: mem.

(** [alloc m lo hi] allocates a fresh block of size [hi - lo] bytes.
  Valid offsets in this block are between [lo] included and [hi] excluded.
  These offsets are writable in the returned memory state.
  This block is not initialized: its contents are initially undefined.
  Returns a pair [(m', b)] of the updated memory state [m'] and
  the identifier [b] of the newly-allocated block.
  Note that [alloc] never fails: we are modeling an infinite memory. *)
Parameter alloc: forall (m: mem) (lo hi: Z), mem * block.

(** [free m b lo hi] frees (deallocates) the range of offsets from [lo]
  included to [hi] excluded in block [b].  Returns the updated memory
  state, or [None] if the freed addresses are not freeable. *)
Parameter free: forall (m: mem) (b: block) (lo hi: Z), option mem.

Print val.
Locate val.

(** [load chunk m b ofs] reads a memory quantity [chunk] from
  addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the value read, or [None] if the accessed addresses
  are not readable. *)
Parameter load: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z), option val.

(** [store chunk m b ofs v] writes value [v] as memory quantity [chunk]
  from addresses [b, ofs] to [b, ofs + size_chunk chunk - 1] in memory state
  [m].  Returns the updated memory state, or [None] if the accessed addresses
  are not writable. *)
Parameter store: forall (chunk: memory_chunk) (m: mem) (b: block) (ofs: Z) (v: val), option mem.

(*** common/Memdata.v ***)


Definition size_chunk (chunk: memory_chunk) : Z :=
  match chunk with
  | Mint8signed => 1
  | Mint8unsigned => 1
  | Mint16signed => 2
  | Mint16unsigned => 2
  | Mint32 => 4
  | Mint64 => 8
  | Mfloat32 => 4
  | Mfloat64 => 8
  | Many32 => 4
  | Many64 => 8
  end.



Lemma size_chunk_pos:
  forall chunk, (size_chunk chunk > 0)%Z.
Proof.
  intros. (* snipe. *)  (* takes a lot of time and fails! but should not *)
(* destruct chunk; simpl; lia. *) 
Admitted.

Definition size_chunk_nat (chunk: memory_chunk) : nat :=
  Z.to_nat(size_chunk chunk).

Lemma size_chunk_conv:
  forall chunk, size_chunk chunk = Z.of_nat (size_chunk_nat chunk).
Proof.
  intros. (* snipe. *)  (* takes a lot of time and fails! but should not *)
destruct chunk; reflexivity. 
Qed.


Lemma size_chunk_nat_pos:
  forall chunk, exists n, size_chunk_nat chunk = S n.
Proof.
  intros. 
  (* snipe. *)  (* takes a lot of time and fails! but should not *)
 (* generalize (size_chunk_pos chunk). rewrite size_chunk_conv.
  destruct (size_chunk_nat chunk).
  simpl; intros; extlia.
  intros; exists n; auto. *)
Admitted.

(* 
Lemma size_chunk_Mptr: size_chunk Mptr = if Archi.ptr64 then 8 else 4.
Proof.
  unfold Mptr; destruct Archi.ptr64; auto.
Qed. *)

(*** Other lemmas could be treated in Memdata *)



Lemma mkmem_ext:
 forall cont1 cont2 acc1 acc2 next1 next2 a1 a2 b1 b2 c1 c2,
  cont1=cont2 -> acc1=acc2 -> next1=next2 ->
  mkmem cont1 acc1 next1 a1 b1 c1 = mkmem cont2 acc2 next2 a2 b2 c2.
Proof.
  intros. subst. f_equal; apply proof_irr.
Qed.

End CompCertSniper.