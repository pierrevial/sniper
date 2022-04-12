From elpi Require Import elpi.
Require Import List.

Elpi Tactic elimination_polymorphism.
Elpi Accumulate File "utilities.elpi".
Elpi Accumulate File "instantiate.elpi".
Elpi Accumulate File "find_instances.elpi".
Elpi Accumulate File "subterms.elpi".
Elpi Accumulate File "construct_cuts.elpi".

(*  Elpi Accumulate lp:{{
   decl x {{nat}}, coq.say "x is" x.
}}. *)



Elpi Query lp:{{
   subterms {{fun (x : nat) => (x * x)%nat }} L,
  L = [T1 | [T2 | [T3 ] ]],
  coq.say "T1 = " T1, coq.say "T2 = " T2, coq.say "T3 =" T3,
  coq.say "T4 = " T4, coq.say "T5 = " T5
}}.

Elpi Accumulate lp:{{

 kind blut type.
  type a blut. 
  type b blut.

pred mylist i : term, o : (list blut). 
mylist (global G) [a].
mylist (fun N Ty F) [b | R] :- !, 
   mylist Ty R1, pi y\ decl x N Ty => mylist (F x) R2, coq.say "B= " B, 
   std.append R1 R2 R.

pred myotherlist i : term, o : (list blut). 
myotherlist (global G) [a].
myotherlist (fun N Ty F) [b | R] :- !, 
   mylist Ty R1,  decl x N Ty, myotherlist (F x) R2, 
   std.append R1 R2 R.
}}.

Elpi Query lp:{{
  mylist {{ fun (x: nat) => true }} R.
}}.

Fail Elpi Query lp:{{
  myotherlist {{ fun (x: nat) => true }} R.
}}.



Definition x:= 2.

Fail Elpi Query lp:{{
  coq.typecheck 2 nat ok.

}}.

Elpi Query lp:{{
  coq.typecheck {{x}} {{nat}} ok, coq.say "ok = " ok.
}}.





Fail Elpi Query lp:{{
  coq.typecheck {{ 0 }} {{(@list nat)}} ok, coq.say "ok = " ok.
}}.


Elpi Accumulate lp:{{

 pred instances_param_indu_strategy_list i: list (pair term term), i: list (pair term (list instance)), i: goal, o: list sealed-goal.
    instances_param_indu_strategy_list [P | XS] Inst (goal Ctx _ TyG _ _ as G) GS :- std.rev Ctx Ctx',
      subst_in_instances Ctx' Inst Inst',
      snd P HPoly,
      instances_param_indu_strategy_aux HPoly Inst' [{{unit}}] LInst, !,
      % unit is a dumb default case to eliminate useless polymorphic premise
      construct_cuts LInst ProofTerm,
      refine ProofTerm G GL1, !,
      refine_by_instantiation GL1 P [G1|GL], !, 
      coq.ltac.open (instances_param_indu_strategy_list XS Inst) G1 GS.
    instances_param_indu_strategy_list [] _ G _.
    
  solve (goal Ctx _ TyG _ L as G) GL :- std.rev Ctx Ctx',
    collect_hypotheses_from_context Ctx HL HL1, polymorphic_hypotheses HL1 HL2, argument_to_term L LTerm, 
    append_nodup HL2 LTerm HPoly, !, find_instantiated_params_in_list Ctx' [TyG |HL] Inst, 
    instances_param_indu_strategy_list HPoly Inst G GL.
 

}}.
Elpi Typecheck.

Ltac clear_prenex_poly_hyps_in_context := repeat match goal with 
| H : forall (A : ?T), _ |- _ => first [ constr_eq T Set | constr_eq T Type] ; try (clear H)
end.

Tactic Notation "elimination_polymorphism" uconstr_list_sep(l, ",") :=
  elpi elimination_polymorphism ltac_term_list:(l) ; clear_prenex_poly_hyps_in_context.

Goal forall (l : list nat) (p: bool * nat), l = l.
Proof. intros. elpi elimination_polymorphism (app_length) (pair_equal_spec) (app_cons_not_nil). 
intros. elpi elimination_polymorphism (pair_equal_spec).
Abort.

Goal (forall (A : Type) (l : list A), A = A) -> (forall (B: Type), B = B) ->
(1 + 1 = 2) -> (forall (A : Type)
(l: list A) (p : A *A), l= l /\ p =p).
intros H H1 H2 A l p. elimination_polymorphism. Abort. 

Goal (forall (A : Type), 1 = 1) -> 1=1.
Proof. intros. elimination_polymorphism. Abort.




Lemma test_clever_instances : forall (A B C D E : Type) (l : list A) (l' : list B)
(p : C * D) (p' : D*E), l = l -> l' = l' -> p = p -> (forall (A : Type) (x : A), x= x)
-> (forall (A : Type) (l : list A), l = l) -> (forall (A B : Type) (p : A *B), p =p ) ->
p' = p'.
intros. elimination_polymorphism app_length. reflexivity. Qed. 

(* Test polymorphism *) 
Goal (forall (A B : Type) (x1 x2 : A) (y1 y2 : B), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) -> ((forall (x1 x2 : bool) (y1 y2 : nat), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ (forall (x1 x2 : nat) (y1 y2 : bool), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2)) /\ (forall (x1 x2 : bool) (y1 y2 : bool), 
(x1, y1) = (x2, y2) -> (x1 = x2 /\ y1 = y2))).
intro H. elimination_polymorphism. split. assumption. split. assumption. assumption.
Qed. 



