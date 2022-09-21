
Require Import utilities. 
Require Import elimination_polymorphism.
Require Export clearbodies.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import List.
Require Import ZArith.
Require Import interpretation_algebraic_types. 
Require Import case_analysis. 
Require Import SMTCoq.SMTCoq.

From elpi Require Import elpi.

Ltac asserteq x := let blut := fresh in assert (blut := x).
Ltac myassert x := assert x.
Ltac assertna na x := assert ( na := x).

Goal False.
assertna kik 2. 
Abort.

Elpi Command kikooo.


Elpi Accumulate lp:{{ 
  pred decllist i : term, o : list prop.
    decllist (fun Na Ty Fu0) [ decl X Na Ty | L] :- pi x\decl x Na Ty =>  (decllist (Fu0 x)  L). 
    decllist _ [].
  
}}.

Elpi Query lp:{{
  decllist {{fun (a b : nat) => a}} L.

}}.

Elpi Query lp:{{
  global (indt I)  = {{ nat }},
  coq.env.indt I _ _ P Ty Ks KTs,
  coq.say Ks.
}}.

Elpi Query lp:{{
  coq.say {{fun (f : nat -> nat) ( x : nat) => f x }}.


}}.


(* ctors_list I LCtors if I is an inductive type and LCtors is the list of the constructors of I.
(* Warning: for now, ctors_list works only with non-mutual inductive types *)
*)

(* app_holos Te p [ T1 , ... , Tn] := 
    app [ Te , _ , ... , _ , T1 , .... , Tn ]
        where there is p holes  
*)
Elpi Accumulate lp:{{
  pred ctors_list i : term, o : list term.
    aux I LCtors :- global (indt Indu)  = I,
    coq.env.indt Indu _ _ P Ty Ks KTs,
    std.map Ks (x\ y\ y = global (indc x)) LCtors.

  % \TODO unifier le nom
  pred holes_p i : int, o : list term.
    holes_p 0 [].
    holes_p (S P) [ _ | L ] :- holes_n P L.

  %pred app_holes_p i : term, i : int, o : term.
  %  app_holes_p Te p (app [Te | H]) :- holes_p p H.
  
  %pred holos_p i : int, i : list term, o : list term.
  %  holes_p 0 L L.
  %  holes_p (1 + p) [ _ | H ] :- holes_n p H.

  %pred app_holos_p i: term, i : int, i : list term, o : term.
  %  app_holos_p Te p L app [Te | H] :- holos_p p L H. 
}}.

(* Warning: for now, get_ctors_lpi works only with *non-mutual* inductive types *)
(* Elpi Tactic get_ctors_lpi.
Elpi Accumulate lp:{{
    solve (goal _ _ _ _ [trm L] as G) GL :-   
      ctors_list L LCtors.
}}.
Elpi Typecheck. *)

(* Elpi Query lp:{{
  % coq.s lp:{{}}
%  M = lp:{{app [ {{cons}}, X0, {{1}} , app [ {{nil}}, X0]  ] }}.
}}. *)





(* Elpi Tactic rettac. *)
(* Elpi Accumulate lp:{{
  solve (goal _ _ _ _ [trm L] as G) GL :-   
      coq.say "how do I get an lpi tactic returning something?".
}}. *)

Elpi Accumulate lp:{{

% Q: a-t-on besoin de stocker les types ou sont ils inférables ?
  %pred arg_typ i : term, o : list term.  
  %  arg_typ (fun Na Ty Fu) [Ty | L]:- pi x\decl x Na Ty => arg_typ (Fu x) L. 
  %  arg_typ Te [Te].  

%  pred mfe i : list term, i : term, i : term 

% utile (pass from something elpi universally bound to the coq fun binder)
%pred refun i : term, o : term.
%  refun (pi x\decl _ _ _ => Fu x) F.


% pred stackX i : term, i : term, i : int, o : list term. 
%  stackX T1 T2 (1 + k) [T1' X , T2' X] :- stackX T1 T2 k [T1' , T2'].
%  stackX T1 T2 0 [T2' , T3' ].



%pred make_fun_eq i : int, i : term i : list term, i : term, i : term, o : term.
%  make_fun_eq p C ([A1 | A2 | L ] as [A1 | L0]) E M T :-
  %make_fun_eq p C [ Te ] E M (prod _  (app [ {{@eq}} , _ , E , C ] ) (app [ {{@eq}} , _ , M , Te]) )

  

  
}}.
    
Elpi Tactic saveterm. (* \TMP: remove when it works *)
Elpi Accumulate lp:{{
    solve (goal _ _ _ _ [str Na, trm M] as G) GL :- coq.say M,
      coq.ltac.call "assertna" [str Na, trm M] G GL.
}}.
Elpi Typecheck.

Tactic Notation "saveterm"  string(s) constr(l) := elpi saveterm ltac_string:(s) (l). 

Goal False.
Fail saveterm "kik" 2.
Fail elpi saveterm ("fjk") (2).
Abort.


Goal forall (n : nat) (k : nat),
 n =  S k -> ((match n with
 | 0 => true
 | S k0 => false 
 end) = false)
.
intro n. intro k. intro H. inversion H. reflexivity.
Qed.


Goal forall (A : Type) (l : list A) (def : A) (a : A) (l0 : list A),
 l =  a :: l0 -> ((match l with
 | [] => def 
 | a :: l0 => a 
 end) = a).
intro A. intro l. intro def. 
intro a. intro l0. intro H.
inversion H. reflexivity.
Qed.

(* blut_tac H k proves H when H has the form
   forall (x1 : A1) ... (xk : Ak), e = Ci x1 .... xk 
   -> (match e with
        ....
        | Ci x1' .... Ci xk' => fi  
        ....
        end ) = fi
  Tactic blut_tac is useful to prove the output of \TODO???   
*)
Ltac blut_tac H k := (intros until k ; let HProd := fresh "H" in
intro HProd ; inversion HProd ; reflexivity).


(* 
Elpi Query lp:{{
F = fun _ X0 c0\ fun _ (X1 c0) c1\ {{ true}},
M = match   (app
    [{{ @cons }}, {{nat}}, 
   app [{{S}}, {{0}}], 
     app
      [{{@cons}}, {{nat}}, 
       app
        [{{S}}, app [{{S}}, {{0}}]], 
       app [{{@nil}}, {{nat}}]]]) (fun _ (app [{{@list}}, X2]) c0 \ X3 c0) 
       [{{false}}, 
        (fun _ X0 c0 \ fun _ (X1 c0) c1 \ {{true}})].  }}.
%E = app
%[{{@cons}}, {{nat}}, 
% app [{{S}}, {{0}}], 
% app
%  [{{@cons}}, {{nat}}, 
%   app [{{S}}, app [{{S}}, {{0}}]], 
%   app [{{@nil}}, {{nat}}]]] ,
%C = 
%   {{@cons}} .
%  essai F [] M E C P.
%}}. *)

Elpi Tactic print_args.
Elpi Accumulate lp:{{
  solve (goal _ _ _ _ Args) _ :- coq.say Args.
}}.
Elpi Typecheck.

Lemma test_print_args : True.
elpi print_args 1 x "a b" (1 = 0).
Abort.


Elpi Tactic useint.
Elpi Accumulate lp:{{
  solve (goal _ _ _ _ [int N | Args] as G) GL :- 
    std.nth N Args Blut, coq.say Blut.

}}.
Elpi Typecheck.

Goal False.
elpi useint 1 2 "3" (1 =0).
elpi useint 0 2 "3" (1 =0).
elpi useint 2 2 "3" (1 =0).
Abort.



Elpi Tactic useint2.
Elpi Accumulate lp:{{
  solve (goal _ _ _ _ [int N,  Args] as G) GL :- 
     coq.say Args.

}}.
Elpi Typecheck.


Goal False.
elpi useint2 1 L.
(* elpi useint2 (0) ( [2 , 3] ).  
elpi useint2 2  ([2 , "3"]). *)
Abort.


(* Tactic Notation "useint" . *)

Ltac poseas0 t na := pose t as na.
Ltac poseas t na := let na_t := fresh na in poseas0 t na_t.


Goal False.
poseas0 2 kik.
poseas 3 kik.
let na := fresh kik in idtac na.
Abort.



Elpi Query lp:{{
  {{ nat }} = global (indt I). % indc donne une erreur plus haut


}}.

Elpi Tactic binga.
Elpi Accumulate lp:{{
  pred bingo i : int.
    bingo (S N) :- coq.say "bingo rec",
    solve (goal _ _ _ _ _ as G) GL, coq.ltac.call "myassert" [trm True] G GL,
    bingo N.

  solve (goal  _ _ _ _  _ as GA) GB :- coq.say "entree binga", bingo 3.
}}.
Elpi Typecheck.

Goal False.
Fail elpi binga 3.
Abort.



Elpi Tactic printos.
Elpi Accumulate lp:{{
  pred scos i : term, i : list term, i : term, i : term, i : term, o : term.
     scos (fun X Ty F) L M E C  (prod X Ty Re) :- !, pi x\ decl x _ Ty => 
          scos (F x) [x | L ] M E C  (Re x).
      scos F L M E C (prod _ (app [{{ @eq }}, _ , E , app [C | L] ]) (c\ app [{{@eq}}, _ , M , F ]) ). 
      
    %scos F L M E C F . 


  solve (goal _ _ _ _ [trm M, int N] as G) GL :- coq.say M,
  M  = (match E _ LCases), 
  coq.say "M is" M,
  coq.typecheck E Ty ok,
  (global (indt I)  = Ty ; app [global (indt I) | _ ] = Ty),  
  coq.say "\n\nI is" I, 
  coq.env.indt I _ _ P _ Ks _, coq.say "\n\nKs is" Ks,
  std.map Ks (x\ y\ y = global (indc x)) LCtors, 
  coq.say "\n\nLCtors is" LCtors,
  std.nth N LCtors C, 
  std.nth N LCases F, coq.say "kikoo",
  coq.mk-n-holes P H, 
  coq.say "\n\nTy is" Ty "\n\nF is " F  "\n\nM is" M  "\n\nE is" E "\n\nC is" C,
  scos F [] M E (app [C | H]) Re, coq.say "Re est" Re.
 % coq.ltac.call "myassert" [trm Re] G GL. 
}}.
Elpi Typecheck.


Tactic Notation "printos" constr(l) integer(n) := elpi printos ltac_term:(l) ltac_int:(n).

Elpi Tactic mytac.
Elpi Accumulate lp:{{
  pred essai i : term, i : list term, i : term, i : term, i : term, o : term.
     essai (fun X Ty F) L M E C  (prod X Ty Re) :- !, coq.say "fun", pi x\ decl x _ Ty => coq.say "branche 1", coq.say " M is" M,
          essai (F x) [x | L ] M E C  (Re x).
      essai F L M E C (prod _ (app [{{ @eq }}, _ , E , app [C | L] ]) (c\ app [{{@eq}}, _ , M , F ]) ) :- 
      coq.say "for essai, M is" M, coq.say "branche 2".
    %essai F L M E C F . 


% LCases : list of cases
% LCtors : list of constructors


% \TODO :l'argument devrait être Ks, pas LCtors (pour éviter de relire la liste Ks)
% [list trm LCases, trm M, trm E, trm Ty, trm I, int P, trm LCtors, list trm H] 
%% PROBLEME : I est dans doute un 'inductive' de Elpi

% on doit unsealer GA
  pred blutoz i : list term, i : term, i: term, i: term, i: int, i : list constructor, i : list term.
  blutoz LCases M E Ty P Ks H 
   :- !, %coq.say "branche 1", 
   %coq.typecheck E Ty ok,
   %(global (indt I)  = Ty ; app [global (indt I) | _ ] = Ty),  
   %coq.env.indt I _ _ P _ Ks _,
  %%%%% N is std.length Ks, % \Q is there a more efficient way to get N? 
  %%%%% std.map Ks (x\ y\ y = global (indc x)) LCtors, 
  %%%% coq.mk-n-holes P H, 
  LCases = [ F | LCa0 ], Ks = [ K | Ks0], C = global (indc K),
  essai F [] M E (app [C | H]) Re,
% coq.ltac.call "myassert" [trm Re] _ [GA | GL], GA = seal GAu, coq.ltac.call "admit" [] GAu _. 
  blutoz [] M E Ty P Ks H 
   :- !, coq.say "branche 0". 
  %% PROBLEME, c'est à GL, pas à GA qu'on veut appliquer l'appel récursif
   %% PROBLEME : mélange de prédicat et de tactique


 % solve (goal _ _ _ _ [trm M, int N] as G) GL :- coq.say M,
 % M  = (match E _ LCases), 
  %%%% coq.ltac.call "poseas" [trm M, str]
  %coq.typecheck E Ty ok,
  %(global (indt I)  = Ty ; app [global (indt I) | _ ] = Ty),  
  %coq.env.indt I _ _ P _ Ks _,
  %%%%% N is std.length Ks, % \Q is there a more efficient way to get N? 
  %%%%% std.map Ks (x\ y\ y = global (indc x)) LCtors, 
  %coq.mk-n-holes P H, 
  %blutoz.
}}.
Elpi Typecheck.

Goal False.
  printos  (match 2 with 
  | 0 => true 
  | S k => false
  end) 1.
Abort.

Elpi Query lp:{{ coq.say "KIKOOOOO". }}.

Elpi Query lp:{{global (indt I)  = {{ nat }} , 
coq.mk-n-holes 1 H,
coq.env.indt I _ _ P _ Ks _  ,
  blutoz % {{L M E Ty P Ks H. }} .
 [{{0}} , {{S}}]
{{(match 2 with 
  | 0 => true 
  | S k => false
  end) }} {{2}}  {{nat}}
   0 Ks H.
}}.

(* pred blutoz i : list term, i : term, i: term, i: inductive, i: int, i :term, i : list constructor, i : list term.
  blutoz LCases M E Ty I P Ks H  *)


(*     
Elpi Query lp:{{
  coq.say "SDFDFDFSklmdfskfdsmlksfdlfsdklmdfksdflmsfdklmsml",
 % coq.say {{ (fun (a b : nat) => a )}},
 % {{fun (a b : nat) => a + 2 * b  }} = fun _ Ty F,   
 % pi x \decl x _ Ty => whd1 (F x) T. %coq.say T.
  % whd1 {{ (fun (a b : nat) => a ) (2+ 3)}} T, 
  %coq.mk-n-holes 2 L, 
  essai {{fun (a : nat) => true }}  [] {{false }} {{0}} {{S}} P, coq.say P.
 % essai {{fun (a : nat) ( b : bool)=> a }} [] {{true}} {{0}} {{S}} P.
}}. *)


Elpi Query lp:{{
  essai (fun _ X0 c0\ fun _ (X1 c0) c1\ {{ true}}) []  
  {{(match 2 with 
  | 0 => true 
  | S k => false
  end) }} 
  {{2}} {{S}} P.    
}}.

Elpi Query lp:{{
 coq.say "KIKOOOOOOOOOOOOO".}}.

Tactic Notation "mytac" constr(l) integer(n) := elpi mytac ltac_term:(l) ltac_int:(n).



Goal forall (n : nat), n = 3 -> 2 +2 = 5.
intros n.
mytac
     (match 2 with 
  | 0 => true 
  | S k => false
  end) 1. intros. reflexivity. clear H. 
mytac
     (match (n + 2) with 
  | 0 => true 
  | S k => false
  end) 0.
Fail idtac  "KIKOOOOOOOOOOOOO" ; sarace.
  mytac (match [1 ; 2] with
   | [] => false
   | _ :: _ => true
   end
  ) 0.
Abort.


(*
Elpi Query lp:{{
  appk [ {{0}} , {{2}} ] {{fun (a b : nat) => a + b}} T.
  appk [X0 , X1 ] {{fun (a b : nat) => a + b}} T.
}}.*)


Elpi Tactic pmgoal.
Elpi Accumulate lp:{{



}}.

Elpi Tactic essai.
Elpi Accumulate lp:{{

solve (goal _ _ _ _ [int p, term M, trm E, trm C] as G) GL :-   
  essai F [] M E (app [C, holes_p p]) P, coq.ltac.call "myassert" [trm P] G GL. 
}}.
Elpi Typecheck.


Elpi Tactic blutas.  
Elpi Accumulate lp:{{  %  pred blut4 i : term.  % \Q ???? nécessaire de changer le 'goal' ? chercher G et GL
% probablement ---> c'est les extra arguments

% blut3 i i0 convers a Coq nat into an elpi int    % probably useless
  pred blut3 i : term, o : int.
    blut3 n k :- (trm n) is (int k).

%(* funtoprod Co Te i Re outputs
%      Re := forall (x1 : A1) ... (xn : An). Te = Bo 
%      when Co has the form fun (x1 : A1) ... (xn : An) . Bo         
% *)

 % pred funtoprod i : term, i : term, i : term, o : term.   
  %  funtoprod (fun Na Ty Fu1) Ex Ma (prod Na Ty Fu2) :-   coq.say "entree funtoprod 1",
  %  pi x\ decl x Na Ty => funtoprod (Fu1 x) Ex Ma (Fu2 x).
  %  funtoprod Fu Ex Ma Re :-  % (app [{{ @eq }}, _ , Fu , Bo]) = Re.
  %    coq.unify-eq (app [{{ @eq }}, _ , Fu , Ex]) Re ok .%  coq.say "entree funtoprod 2".
    % funtoprod _ _ _ :- coq.say "Error funtoprod".

    pred blutin i : term, i : list term, i : term, i : term, o : term.   
    blutin (fun Na Ty Fu0) ArgCRev Ex Ma (prod Na Ty Re0) :-   % coq.say "1 entree blutin",
    pi x\ decl x Na Ty => blutin (Fu0 x) (x\ [x | ArgCRev]) Ex Ma (Re0 x).
    blutin Fu CArgRev Ex Ma Re :-  std.rev ArgCRev ArgC,  
      coq.unify-eq (app [{{ @eq }}, _ , Ma , Fu]) Re ok .%  coq.say "entree funtoprod 2".
    % funtoprod _ _ _ :- coq.say "Error funtoprod".


  pred funtoprodass i : term, i : term. 
    funtoprodass Te1 Te2 :- coq.say "entree funtoprodass", funtoprod Te1  Te2 Re, coq.ltac.call "assert" [trm Te2] G GL.
      % probleme: G et GL pas définis



  
  pred blut5 i : list term, i : term.
    blut5 [Ca0 | LCases] Te :- coq.say "entree blut5", funtoprod Ca0 Te Eq0, coq.ltac.call "assert" [trm Eq0] G GL, blut5 LCases Te .
    blut5 [] Te :- coq.say "fini".



%    blut4 T :- blut1 T [ Ca0 | LCases], blut0 Ca0, blut5


   pred isconjj i : term.
    isconjj Lo :- ( coq.unify-eq (app [ {{@and}} , L , L]) Lo Kk, coq.say "c'est une conjonction" ; coq.say "pas une conj").


  solve (goal _ _ _ _ [trm L] as G) GL :-   
 %  funtoprod L ( {{1}}) Re,  coq.say Re %, coq.ltac.call "assert" [trm Re] G GL,
    blut0 L Te, 
    blut1 L [L0 | LCases],  funtoprod L0 Te Re, coq.ltac.call "myassert" [trm Re] G GL . % , coq.say Re,   
  %  coq.say "koo". % blut1 L _. % blut1 L GL.
}}.
Elpi Typecheck.

Tactic Notation "blutas" constr(l) := elpi blutas (l).

Elpi Query lp:{{  coq.say {{ (fun (a b : nat) => 0)}}  }}.



Goal forall (x y : nat) (b1 b2 : bool), True.
Proof. intros. 
Elpi Query lp:{{coq.say "kikooo".}}.
blutas (match (x + y) with 
| 0 => true 
| S k => false
end).
let kik := constr:((match (x + y) with 
| 0 => true 
| S k => false
end))  in blutas kik.
blutas (match 1 +2 with 
)
blutas 0.  
blutas (fun (a : nat) => a ). 
blutas (fun (a b : nat) => 0) .
blutas (True /\ True).
blutas 2 . 
blutas (fun (a b : nat) => 0) .

let kik := eval hnf in (fun (a b : nat) => 0)  in blublut kik.

let kik := constr:((match (x + y) with 
| 0 => true 
| S k => false
end))  in blublut kik.





Elpi Tactic mytac.
Elpi Accumulate lp:{{
  pred essai i : term, i : list term, i : term, i : term, i : term, o : term.
     essai (fun X Ty F) L M E C  (prod X Ty Re) :- !, coq.say "fun", pi x\ decl x _ Ty => coq.say "branche 1", 
          essai (F x) [x | L ] M E C  (Re x).
      essai F L M E C (prod _ (app [{{ @eq }}, _ , E , app [C | L] ]) (c\ app [{{@eq}}, _ , M , F ]) ) :- 
      coq.say "branche 2".
    %essai F L M E C F . 


  solve (goal _ _ _ _ [trm M] as G) GL :- coq.say M,
  M  = (match E _ LCases), coq.typecheck E Ty ok,
  (global (indt I)  = Ty ; app [global (indt I) | _ ] = Ty),  
  coq.env.indt I _ _ P TyI Ks KTs, 
  std.map Ks (x\ y\ y = global (indc x)) LCtors, %coq.say LCtors,  % PB: if this line is commented, an error appear about LCases
  std.nth 1 LCtors C, % !!!!!!! test pour le ctor de rang 1 %%% Elpi does say anything if one just write nth instead of std.nth
  std.nth 1 LCases F, 
  coq.mk-n-holes P H, %coq.say H,
  coq.say "Ty is" Ty "\n\nF is " F  "\n\nM is" M  "\n\nE is" E "\n\nC is" C,
  %essai (fun _ X0 c0\ fun _ (X1 c0) c1\ {{ true}}) []  
  %{{(match 2%nat with 
  %| 0 => true 
  %| S k => false
  %end) }} 
  %{{2%nat}} {{S}} Pouet, coq.say Pouet, coq.ltac.call "myassert" [trm {{True}}] G GL.   
  % essai F [] M E  C Re, coq.say Re, 
 essai F [] M E (app [C | H]) Re,% coq.say Pouet.
  coq.ltac.call "myassert" [trm Re] G GL. 
}}.
Elpi Typecheck.




Elpi Tactic mytac.
Elpi Accumulate lp:{{
  pred essai i : term, i : list term, i : term, i : term, i : term, o : term.
     essai (fun X Ty F) L M E C  (prod X Ty Re) :- !, coq.say "fun", pi x\ decl x _ Ty => coq.say "branche 1", coq.say " M is" M,
          essai (F x) [x | L ] M E C  (Re x).
      essai F L M E C (prod _ (app [{{ @eq }}, _ , E , app [C | L] ]) (c\ app [{{@eq}}, _ , M , F ]) ) :- 
      coq.say "for essai, M is" M, coq.say "branche 2".
    %essai F L M E C F . 


  solve (goal _ _ _ _ [trm M, int N] as G) GL :- coq.say M,
  M  = (match E _ LCases), 
  % coq.ltac.call "poseas" [trm M, str]
  coq.typecheck E Ty ok,
  (global (indt I)  = Ty ; app [global (indt I) | _ ] = Ty),  
  coq.env.indt I _ _ P TyI Ks KTs, 
  std.map Ks (x\ y\ y = global (indc x)) LCtors, 
  std.nth N LCtors C, 
  std.nth N LCases F, coq.say "kikoo",
  coq.mk-n-holes P H, 
  coq.say "Ty is" Ty "\n\nF is " F  "\n\nM is" M  "\n\nE is" E "\n\nC is" C,
  essai F [] M E (app [C | H]) Re, coq.say "Re est" Re,
  coq.ltac.call "myassert" [trm Re] G GL. 
}}.
Elpi Typecheck.



(*     
Elpi Query lp:{{
  coq.say "SDFDFDFSklmdfskfdsmlksfdlfsdklmdfksdflmsfdklmsml",
 % coq.say {{ (fun (a b : nat) => a )}},
 % {{fun (a b : nat) => a + 2 * b  }} = fun _ Ty F,   
 % pi x \decl x _ Ty => whd1 (F x) T. %coq.say T.
  % whd1 {{ (fun (a b : nat) => a ) (2+ 3)}} T, 
  %coq.mk-n-holes 2 L, 
  essai {{fun (a : nat) => true }}  [] {{false }} {{0}} {{S}} P, coq.say P.
 % essai {{fun (a : nat) ( b : bool)=> a }} [] {{true}} {{0}} {{S}} P.
}}. *)

Elpi Query lp:{{
  essai (fun _ X0 c0\ fun _ (X1 c0) c1\ {{ true}}) []  
  {{(match 2 with 
  | 0 => true 
  | S k => false
  end) }} 
  {{2}} {{S}} P.    
}}.

Elpi Query lp:{{
 coq.say "KIKOOOOOOOOOOOOO".}}.

Tactic Notation "mytac" constr(l) integer(n) := elpi mytac ltac_term:(l) ltac_int:(n).



Goal forall (n : nat), n = 3 -> 2 +2 = 5.
intros n.
mytac
     (match 2 with 
  | 0 => true 
  | S k => false
  end) 1. intros. reflexivity. clear H. 
mytac
     (match (n + 2) with 
  | 0 => true 
  | S k => false
  end) 0.
  mytac (match [1 ; 2] with
   | [] => false
   | _ :: _ => true
   end
  ) 0.
Abort.