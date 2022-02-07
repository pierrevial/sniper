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



Require Export SMTCoq.SMTCoq.

Require Export utilities.
Require Export definitions.
Require Export elimination_fixpoints.
Require Export expand.
Require Export elimination_pattern_matching. 
Require Export elimination_polymorphism.
Require Export eliminators.
Require Export interpretation_algebraic_types.
Require Import ZArith.
Require Import PArith.BinPos.
Require Import SMTCoq.bva.BVList.
Require Import NArith.BinNatDef.

(* Tuple of symbols we do not want to unfold 
in the default tactic *)
Definition prod_of_symb := (unit,
         Zplus,
         Zminus, 
         Zmult,
         Z.eqb,
         Zlt_bool, 
         Zle_bool, 
         Zge_bool, 
         Zgt_bool,
         Z.lt,
         Z.le,
         Z.ge,
         Z.gt,
         Pos.lt, 
         Pos.le, 
         Pos.ge, 
         Pos.gt,
         Z.to_nat,
         Pos.mul,
         Pos.add,
         Pos.sub,
         Init.Nat.add,
         Init.Nat.mul,
         Nat.eqb,
         Nat.leb,
         Nat.ltb,
         Init.Peano.lt,
         Init.Peano.ge,
         Init.Peano.gt,
         N.add,
         N.mul,
         N.eqb,
         N.leb,
         N.ltb,
         Init.Peano.lt,
         Init.Peano.ge,
         Init.Peano.gt,
         negb,
         not,
         andb,
         orb,
         implb,
         xorb,
         Bool.eqb,
         iff,
         @BITVECTOR_LIST.bv_eq,
         @BITVECTOR_LIST.bv_and,
         @BITVECTOR_LIST.bv_or,
         @BITVECTOR_LIST.bv_xor,
         @BITVECTOR_LIST.bv_add,
         @BITVECTOR_LIST.bv_mult,
         @BITVECTOR_LIST.bv_ult,
         @BITVECTOR_LIST.bv_slt,
         @BITVECTOR_LIST.bv_concat,
         @BITVECTOR_LIST.bv_shl,
         @BITVECTOR_LIST.bv_shr,
         @FArray.select,
         @FArray.diff,
         is_true,
         @eqb_of_compdec).

Definition prod_types := (Z, bool, True, False, positive, N, and, or, nat, Init.Peano.le).


Ltac def_and_pattern_matching p1 := let p1' := eval unfold p1 in p1 in
get_definitions_theories p1' ltac:(fun H => expand_hyp_cont H ltac:(fun H' => 
eliminate_dependent_pattern_matching H')).


Ltac def_fix_and_pattern_matching p1 := let p1' := eval unfold p1 in p1 in
get_definitions_theories p1' ltac:(fun H => expand_hyp_cont H ltac:(fun H' => 
eliminate_fix_ho H' ltac:(fun H'' =>
try (eliminate_dependent_pattern_matching H'')))).


Ltac def_and_pattern_matching_mono p1 :=
def_and_pattern_matching p1 ; inst.

Ltac def_and_pattern_matching_mono_param p1 t :=
def_and_pattern_matching p1 ; inst t.

Ltac def_fix_and_pattern_matching_mono_param p1 t :=
def_fix_and_pattern_matching p1 ; inst t.

Ltac scope_param_nat p1 p2 t := let p2' := eval unfold p2 in p2 in
try interp_alg_types_context_goal p2' ; try (def_fix_and_pattern_matching_mono_param p1 t ; try nat_convert) ;
get_eliminators_in_variables p2'.

Ltac scope_no_param_nat p1 p2 := let p2' := eval unfold p2 in p2 in
try interp_alg_types_context_goal p2' ; try (def_fix_and_pattern_matching p1 ; inst ; try nat_convert) ;
get_eliminators_in_variables p2'.

Ltac scope_param_no_nat_var p1 p2 t := let p2' := eval unfold p2 in p2 in
intros ; try interp_alg_types_context_goal p2' ; try (def_fix_and_pattern_matching_mono_param p1 t) ;
get_eliminators_in_variables p2'.

Ltac scope_no_param_no_nat_var p1 p2 := let p2' := eval unfold p2 in p2 in
intros ; try interp_alg_types_context_goal p2'; try (def_fix_and_pattern_matching p1 ; inst) ;
get_eliminators_in_variables p2'.

Ltac snipe_param_nat p1 p2 t := 
scope_param_nat p1 p2 t ; verit.

Ltac snipe_no_param_nat p1 p2 := 
scope_no_param_nat p1 p2 ; verit.

Ltac snipe_param_no_nat_no_check p1 p2 t :=
scope_param_no_nat_var p1 p2 t ; verit_no_check.

Ltac snipe_no_param_no_nat_no_check p1 p2 :=
scope_no_param_no_nat_var p1 p2 ; verit_no_check.

Ltac snipe_param_no_nat_var p1 p2 t :=
scope_param_no_nat_var p1 p2 t ; verit.

Ltac snipe_no_param_no_nat_var p1 p2 :=
scope_no_param_no_nat_var p1 p2 ; verit.

Tactic Notation "snipe_no_check" constr(t) := snipe_param_no_nat_no_check prod_of_symb prod_types t.
Tactic Notation "snipe_no_check" := snipe_no_param_no_nat_no_check prod_of_symb prod_types.

Tactic Notation "scope" constr(t) := scope_param_no_nat_var prod_of_symb prod_types t.
Tactic Notation "scope" := scope_no_param_no_nat_var prod_of_symb prod_types.

Tactic Notation "snipe" constr(t) := intros ; snipe_param_no_nat_var prod_of_symb prod_types t.
Tactic Notation "snipe" := intros ; snipe_no_param_no_nat_var prod_of_symb prod_types.

Tactic Notation "scope_nat" constr(t) := scope_param_nat prod_of_symb prod_types t.
Tactic Notation "scope_nat" := scope_no_param_nat prod_of_symb prod_types.

Tactic Notation "snipe_nat" constr(t) := intros ; snipe_param_nat prod_of_symb prod_types t.
Tactic Notation "snipe_nat" := intros ; snipe_no_param_nat prod_of_symb prod_types.
