

(*** From lib/Map.v ***)

Definition elt  := positive.
(* Definition elt_eq := peq. *)

Inductive tree' (A: Type) : Type := 
  | Node001: tree' A -> tree' A
  | Node010: A -> tree' A
  | Node011: A -> tree' A -> tree' A
  | Node100: tree' A -> tree' A
  | Node101: tree' A -> tree' A ->tree' A
  | Node110: tree' A -> A -> tree' A
  | Node111: tree' A -> A -> tree' A -> tree' A.


  Inductive tree (A: Type) : Type := 
  | Empty : tree A
  | Nodes: tree' A -> tree A.



Definition empty (A: Type) : tree A := Empty A.

Definition init (A : Type) (x : A) :=
    (x, empty A).

Fixpoint get' {A} (p: positive) (m: tree' A) : option A :=
    match p, m with
    | xH, Node001 _ => None
    | xH, Node010 x => Some x
    | xH, Node011 x _ => Some x
    | xH, Node100 _ => None
    | xH, Node101 _ _ => None
    | xH, Node110 _ x => Some x
    | xH, Node111 _ x _ => Some x
    | xO q, Node001 _ => None
    | xO q, Node010 _ => None
    | xO q, Node011 _ _ => None
    | xO q, Node100 m' => get' q m'
    | xO q, Node101 m' _ => get' q m'
    | xO q, Node110 m' _ => get' q m'
    | xO q, Node111 m' _ _ => get' q m'
    | xI q, Node001 m' => get' q m'
    | xI q, Node010 _ => None
    | xI q, Node011 _ m' => get' q m'
    | xI q, Node100 m' => None
    | xI q, Node101 _ m' => get' q m'
    | xI q, Node110 _ _ => None
    | xI q, Node111 _ _ m' => get' q m'
    end.

  Definition treeget {A} (p: positive) (m: tree A) : option A :=
    match m with
    | Empty => None
    | Nodes m' => get' p m'
    end.

Definition PMapt (A : Type) : Type := (A * tree A)%type.

Definition get (A : Type) (i : positive) (m : PMapt A) :=
    match treeget i (snd m) with
    | Some x => x
    | None => fst m
    end.



(*** From common/Memory.v ***)


Local Notation "a # b" := (get b a) (at level 1).

Definition perm_order' (po: option permission) (p: permission) :=
  match po with
  | Some p' => perm_order p' p
  | None => False
 end.

Definition perm_order'' (po1 po2: option permission) :=
  match po1, po2 with
  | Some p1, Some p2 => perm_order p1 p2
  | _, None => True
  | None, Some _ => False
 end.

Record mem' : Type := mkmem {
  mem_contents: PMapt (ZMap.t memval);  (**r [block -> offset -> memval] *)
  mem_access: PMap.t (Z -> perm_kind -> option permission);
                                         (**r [block -> offset -> kind -> option permission] *)
  nextblock: block;
  access_max:
    forall b ofs, perm_order'' (mem_access#b ofs Max) (mem_access#b ofs Cur);
  nextblock_noaccess:
    forall b ofs k, ~(Plt b nextblock) -> mem_access#b ofs k = None;
  contents_default:
    forall b, fst mem_contents#b = Undef
}.

Definition mem := mem'.

(** [loadv] and [storev] are variants of [load] and [store] where
  the address being accessed is passed as a value (of the [Vptr] kind). *)

Definition loadv (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match addr with
  | Vptr b ofs => load chunk m b (Ptrofs.unsigned ofs)
  | _ => None
  end.

Definition storev (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs => store chunk m b (Ptrofs.unsigned ofs) v
  | _ => None
  end.

(** [loadbytes m b ofs n] reads and returns the byte-level representation of
  the values contained at offsets [ofs] to [ofs + n - 1] within block [b]
  in memory state [m].
  [None] is returned if the accessed addresses are not readable. *)
Parameter loadbytes: forall (m: mem) (b: block) (ofs n: Z), option (list memval).

(** [storebytes m b ofs bytes] stores the given list of bytes [bytes]
  starting at location [(b, ofs)].  Returns updated memory state
  or [None] if the accessed locations are not writable. *)
Parameter storebytes: forall (m: mem) (b: block) (ofs: Z) (bytes: list memval), option mem.

(** [free_list] frees all the given (block, lo, hi) triples. *)
Fixpoint free_list (m: mem) (l: list (block * Z * Z)) {struct l}: option mem :=
  match l with
  | nil => Some m
  | (b, lo, hi) :: l' =>
      match free m b lo hi with
      | None => None
      | Some m' => free_list m' l'
      end
  end.

(** [drop_perm m b lo hi p] sets the permissions of the byte range
    [(b, lo) ... (b, hi - 1)] to [p].  These bytes must have [Freeable] permissions
    in the initial memory state [m].
    Returns updated memory state, or [None] if insufficient permissions. *)

Parameter drop_perm: forall (m: mem) (b: block) (lo hi: Z) (p: permission), option mem.

(** * Permissions, block validity, access validity, and bounds *)

(** The next block of a memory state is the block identifier for the
  next allocation.  It increases by one at each allocation.
  Block identifiers below [nextblock] are said to be valid, meaning
  that they have been allocated previously.  Block identifiers above
  [nextblock] are fresh or invalid, i.e. not yet allocated.  Note that
  a block identifier remains valid after a [free] operation over this
  block. *)

Parameter nextblock: mem -> block.

Definition valid_block (m: mem) (b: block) := Plt b (nextblock m).

Axiom valid_not_valid_diff:
  forall m b b', valid_block m b -> ~(valid_block m b') -> b <> b'.

(** [perm m b ofs k p] holds if the address [b, ofs] in memory state [m]
  has permission [p]: one of freeable, writable, readable, and nonempty.
  If the address is empty, [perm m b ofs p] is false for all values of [p].
  [k] is the kind of permission we are interested in: either the current
  permissions or the maximal permissions. *)
Parameter perm: forall (m: mem) (b: block) (ofs: Z) (k: perm_kind) (p: permission), Prop.

(** Logical implications between permissions *)

Axiom perm_implies:
  forall m b ofs k p1 p2, perm m b ofs k p1 -> perm_order p1 p2 -> perm m b ofs k p2.

(** The current permission is always less than or equal to the maximal permission. *)

Axiom perm_cur_max:
  forall m b ofs p, perm m b ofs Cur p -> perm m b ofs Max p.
Axiom perm_cur:
  forall m b ofs k p, perm m b ofs Cur p -> perm m b ofs k p.
Axiom perm_max:
  forall m b ofs k p, perm m b ofs k p -> perm m b ofs Max p.

(** Having a (nonempty) permission implies that the block is valid.
  In other words, invalid blocks, not yet allocated, are all empty. *)
Axiom perm_valid_block:
  forall m b ofs k p, perm m b ofs k p -> valid_block m b.

(* Unused?
(** The [Mem.perm] predicate is decidable. *)
Axiom perm_dec:
  forall m b ofs k p, {perm m b ofs k p} + {~ perm m b ofs k p}.
*)

(** [range_perm m b lo hi p] holds iff the addresses [b, lo] to [b, hi-1]
  all have permission [p] of kind [k]. *)
Definition range_perm (m: mem) (b: block) (lo hi: Z) (k: perm_kind) (p: permission) : Prop :=
  forall ofs, lo <= ofs < hi -> perm m b ofs k p.

Axiom range_perm_implies:
  forall m b lo hi k p1 p2,
  range_perm m b lo hi k p1 -> perm_order p1 p2 -> range_perm m b lo hi k p2.

(** An access to a memory quantity [chunk] at address [b, ofs] with
  permission [p] is valid in [m] if the accessed addresses all have
  current permission [p] and moreover the offset is properly aligned. *)
Definition valid_access (m: mem) (chunk: memory_chunk) (b: block) (ofs: Z) (p: permission): Prop :=
  range_perm m b ofs (ofs + size_chunk chunk) Cur p
  /\ (align_chunk chunk | ofs).

Axiom valid_access_implies:
  forall m chunk b ofs p1 p2,
  valid_access m chunk b ofs p1 -> perm_order p1 p2 ->
  valid_access m chunk b ofs p2.

Axiom valid_access_valid_block:
  forall m chunk b ofs,
  valid_access m chunk b ofs Nonempty ->
  valid_block m b.

















