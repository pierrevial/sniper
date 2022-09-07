
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


Elpi Command tutorial_HOAS. 

Elpi Query lp:{{
  % the ":coq" flag is optional
  coq.say {{:coq 1 + 2 }} "=" {{ 1 + 2 }}
}}.

Section Lol.


Goal forall (x y : nat) (b1 b2 : bool), True.
Proof.
    intros x y b1 b2.
    Elpi Query lp:{{
        coq.say {{(fun (x: nat) => x)}},
        coq.say "intermede",
        coq.say 
    {{ (fun (A : Type) (x : A) (y : A) => y) }}
    }}.
    (* Elpi Query lp:{{
      coq.say {{ }}

    }}. *)

  Abort.


Goal forall (x y : nat) (b1 b2 : bool), True.
Proof.
    intros x y b1 b2.
let b3 := fresh "b3" in let t := eval cbv in 
  (match (x + y) with 
     | 0 => true 
     | S k => false
     end) 
in pose_quote_term t b3.
Print mfixpoint. Print def. clear b3.
Abort.

Goal forall (x y : nat) (b1 b2 : bool), True.
Proof.
    intros x y b1 b2.
Elpi Query lp:{{
  % coq.say {{x}},
  % coq.say "intermede",
  % the ":coq" flag is optional
  coq.say {{  (match 2 with 
  | 0 => true 
  | S k => false
  end) }}
}}.
Abort.

Definition m (h : 0 = 1 ) P : P 0 -> P 1 :=
  match h as e in eq _ x return P 0 -> P x
  with eq_refl => fun (p : P 0) => p end.

Elpi Query lp:{{

coq.locate "m" (const C),
coq.env.const C (some (fun _ _ h\ fun _ _ p\ match _ (RT h p) _)) _,
coq.say "The return type of m is:" RT

}}.




End Lol.

Inductive Option : Set :=
| Fail : Option
| Ok : bool -> Option.

Print Ltac absurd.

Definition get : forall x:Option, x <> Fail -> bool.
refine
    (fun x:Option =>
      match x return x <> Fail -> bool with
      | Fail => _
      | Ok b => fun _ => b
      end).
      intros.  exact true. Qed.

Definition kik : forall (A B C: Prop) (a : A) (H1 : A -> B) (H2 : B -> C), C. 
intros.
Fail refine (H1 _).
Fail refine H2.
refine (H2 _). refine (H1 _). refine a. Qed.
Reset kik.

Definition kik : forall (A B C: Prop) (a : A) (H1 : A -> B) (H2 : B -> C), C. 
intros.
refine (H2 (H1 _)). exact a.
Qed. Reset kik.


 

Elpi Tactic refine.
Elpi Accumulate lp:{{
  solve (goal _ _ Ty _ [trm S] as G) GL :-
    % check S elaborates to T of type Ty (the goal)
    coq.elaborate-skeleton S Ty T ok,

    coq.say "Using" {coq.term->string T}
            "of type" {coq.term->string Ty},

    % since T is already checked, we don't check it again
    refine.no_check T G GL.

  solve (goal _ _ _ _ [trm S]) _ :-
    Msg is {coq.term->string S} ^ " does not fit",
    coq.ltac.fail _ Msg.
}}.
Elpi Typecheck.

Lemma test_refine (P Q : Prop) (H : P -> Q) : Q.
Proof.
  intros.
Fail elpi refine (H).
elpi refine (H _). 
Abort.

Ltac asserteq x := let blut := fresh in assert (blut := x).
Ltac myassert x := assert x.

Elpi Query lp:{{
  coq.say "kikoooooo",
  coq.say {{and True True }}, coq.say {{True /\ True }}, 
  coq.say  {{@and}}.
}}.

Elpi Tactic assertos.
Elpi Accumulate lp:{{    
  solve (goal _ _ _ _ [trm L] as G) GL :-  
  coq.unify-eq (app [ {{@and}} , L , L]) Lo Kk, 
  coq.ltac.call "myassert" [trm Lo] G GL, coq.say "assertos".
}}.
Elpi Typecheck.


Tactic Notation "assertos" constr(l) := elpi assertos (l).


Goal 2 +2 = 5.
myassert True.
assert (A := True).
Print conj.
assert (x := 2 + 5).
pose (2 + 5 ) as y.
assert (B := and A A). 
assert (and A A).
assertos (True).
Abort.




Elpi Tactic assconj.
Elpi Accumulate lp:{{    
  solve (goal _ _ _ _ [trm L] as G) GL :-  
  ( coq.unify-eq (app [ {{@and}}, A , B])  L ok, 
  coq.ltac.call "myassert" [trm L] G GL, coq.say "is and" ; coq.say "pas and !").
}}.
Elpi Typecheck. 


Tactic Notation "assconj" constr(l) := elpi assconj (l).


Goal forall (x y : nat) (b1 b2 : bool), 2 + 2 = 5.
Proof. intros.
assconj (True /\ True).
assconj False.  
Abort.
 


Elpi Tactic isfun.
Elpi Accumulate lp:{{    
  solve (goal _ _ _ _ [trm L] as G) GL :-  
  (coq.unify-eq (fun Na Ty Fu ) L ok, 
  coq.ltac.call "asserteq" [trm L] G GL, coq.say "isfun" ; coq.say "pas fun").
}}.
Elpi Typecheck. 



Tactic Notation "isfun" constr(l) := elpi isfun (l).

Goal forall (x y : nat) (b1 b2 : bool), 2 + 2 = 5.
Proof. intros.
isfun (fun (a b: nat) => a +2 ).
isfun (2 +3).
isfun ((fun (a b : nat) => a + 2) 3).
Abort.



Elpi Tactic asseqrefl.
Elpi Accumulate lp:{{    
  solve (goal _ _ _ _ [trm L] as G) GL :-   
  coq.unify-eq (app [{{ @eq }}, _ , L , L ])  Eqq ok ,
  coq.ltac.call "myassert" [trm Eqq] G GL.
}}.
Elpi Typecheck.


Goal forall (x y : nat) (b1 b2 : bool), 2 + 2 = 5.
Proof. intros.
elpi asseqrefl (2).
elpi asseqrefl (fun (a b : nat) => 0).

Abort.


Elpi Query lp:{{

    T = {{ _ }},
    coq.say "raw T =" T,
    coq.sigma.print,
    coq.say "--------------------------------",
    coq.typecheck T {{ nat }} ok,
    coq.sigma.print

}}.

Elpi Tactic tryftp.  
Elpi Accumulate lp:{{  %  pred blut4 i : term.  % \Q ???? nécessaire de changer le 'goal' ? chercher G et GL
% probablement ---> c'est les extra arguments

% blut3 i i0 convers a Coq nat into an elpi int    % probably useless
  pred blut3 i : term, o : int.
    blut3 n k :- (trm n) is (int k).

%(* funtoprod Co Te i Re outputs
%      Re := forall (x1 : A1) ... (xn : An). Te = Bo 
%      when Co has the form fun (x1 : A1) ... (xn : An) . Bo         
% *)

  pred funtoprod i : term, i : term, o : term.   
    funtoprod (fun Na Ty Fu1) Te (prod Na Ty Fu2) :-   coq.say "entree funtoprod 1",
    pi x\ decl x Na Ty => funtoprod (Fu1 x) Te (Fu2 x).
    funtoprod Fu Bo Re :-  (app [{{ @eq }}, _ , Fu , Bo]) = Re.
     % coq.unify-eq (app [{{ @eq }}, _ , Fu , Bo]) Re ok ,  coq.say "entree funtoprod 2".
    % funtoprod _ _ _ :- coq.say "Error funtoprod".


  pred funtoprodass i : term, i : term. 
    funtoprodass Te1 Te2 :- coq.say "entree funtoprodass", funtoprod Te1  Te2 Re, coq.ltac.call "assert" [trm Te2] G GL.
      % probleme: G et GL pas définis


% blut1 takes a term of the form 'match e with | ... end' and 
% outputs the (elpi) list of the cases of the match.
% Each case is of the form (fun _ Ty1 (c1 \ fun _ Ty2 (c2 \... (fun _ Tyn (cn\ Bo ))... )))
% \TODO vérifier et corriger

  pred blut1 i : term, o : list term.
    blut1 (match Te Ty LCases) LCases :- coq.say "blut1 a été appelé".
    % blut1 _ _ : coq.say "Error blut1".  % \! rq: Typecheck marche pas si deux wildcards
       % \! et error FULLSTOP si blut1 _ []
 

  
  pred blut5 i : list term, i : term.
    blut5 [Ca0 | LCases] Te :- coq.say "entree blut5", funtoprod Ca0 Te Eq0, coq.ltac.call "assert" [trm Eq0] G GL, blut5 LCases Te .
    blut5 [] Te :- coq.say "fini".



%    blut4 T :- blut1 T [ Ca0 | LCases], blut0 Ca0, blut5


   pred isconjj i : term.
    isconjj Lo :- ( coq.unify-eq (app [ {{@and}} , L , L]) Lo Kk, coq.say "c'est une conjonction" ; coq.say "pas une conj").


  solve (goal _ _ _ _ [trm L] as G) GL :-  
  %    blut5 T To. 
  % coq.say "entree tactique" ,
  %  isconjj L. 
   funtoprod L ( {{1}}) Re,  coq.say Re, %, coq.ltac.call "assert" [trm Re] G GL,   
    coq.say "koo". % blut1 L _. % blut1 L GL.
}}.
Elpi Typecheck.

Tactic Notation "tryftp" constr(l) := elpi tryftp (l).

Elpi Query lp:{{  coq.say {{ (fun (a b : nat) => 0)}}  }}.



Goal forall (x y : nat) (b1 b2 : bool), True.
Proof. intros. 
Elpi Query lp:{{coq.say "kikooo".}}.
tryftp 0.  
tryftp (fun (a : nat) => a ). 
tryftp (fun (a b : nat) => 0) .
tryftp (True /\ True).
tryftp 2 . 
tryftp (fun (a b : nat) => 0) .

let kik := eval hnf in (fun (a b : nat) => 0)  in blublut kik.

let kik := constr:((match (x + y) with 
| 0 => true 
| S k => false
end))  in blublut kik.
