Require Import SMTCoq.SMTCoq.

From MetaCoq Require Import All.
Require Import BinInt.
Require Import Coq.Arith.PeanoNat.
Require Import MetaCoq.Template.All.
Require Import MetaCoq.Template.All.
Require Import List.
Require Import utilities.
Require Import definitions.
Require Import expand.
Require Import elimination_fixpoints.
Require Import elimination_pattern_matching.
Import ListNotations.
Require Import String.


Section ilist.
  Variable A : Set.

  Inductive ilist : nat -> Set :=
  | Nil : ilist O
  | Cons : forall n, A -> ilist n -> ilist (S n).

Fixpoint app n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) : ilist (n1 + n2) :=
    match ls1 in (ilist n1) return (ilist (n1 + n2)) with
      | Nil => ls2
      | Cons _ x ls1' => Cons _ x (app _ ls1' _ ls2)
    end.

Print app.

Variable x : A.


Compute app 0 Nil 2 (Cons 1 x (Cons 0 x Nil)).



  Fixpoint inject (ls : list A) : ilist (Datatypes.length ls) :=
    match ls in (list _) return (ilist (Datatypes.length ls)) with
      | nil => Nil
      | h :: t => Cons _ h (inject t)
    end.


  Fixpoint unject n (ls : ilist n) : list A :=
    match ls with
      | Nil => nil
      | Cons _ h t => h :: unject _ t
    end.



MetaCoq Quote Definition app_reif := 

(fun n1 (ls1 : ilist n1) n2 (ls2 : ilist n2) =>
    match ls1 in (ilist n1) return (ilist (n1 + n2)) with
      | Nil => ls2
      | Cons _ x ls1' => Cons _ x (app _ ls1' _ ls2)
    end).


Ltac eliminate_pattern_matching_test H :=

  let n := fresh "n" in 
  epose (n := ?[n_evar] : nat);
  let T := type of H in
  let H' := fresh in
  assert (H' : False -> T);
  [ let HFalse := fresh in
    intro HFalse;
    let rec tac_rec m x :=
        match goal with
      | |- context C[match x with _ => _ end] =>  match constr:(m) with
                                    | 0 => fail
                                    | S ?p => instantiate (n_evar := p) 
                                        end
      | |- forall _, _ => let y := fresh in intro y; tac_rec (S m) y 
      | _ => fail
    end 
in
    tac_rec 0 ltac:(fresh) ;
    destruct HFalse
  | clear H' ;
run_template_program (tmQuoteRec T) (fun Env => 
let T := eval cbv in Env.2 in
let e := eval cbv in Env.1 in
let prod := eval cbv in (get_env T n) in clear n ;
let E := eval cbv in prod.1.2 in
let l := eval cbv in prod.1.1 in 
let A := eval cbv in prod.2 in
let l_ty_ctors := eval cbv in (list_types_of_each_constructor (e, A)) in
let n := eval cbv in (Datatypes.length l_ty_ctors) in
let l_ctors := eval cbv in (get_list_ctors_tConstruct A n) in
let list_of_hyp := eval cbv in (get_equalities E l_ctors l_ty_ctors l) in
 pose list_of_hyp) ].

MetaCoq Quote Definition foo := (forall (H : nat) (H0 : ilist H) (H1 : nat) (H2 : ilist H1),
     app H H0 H1 H2 =
     match H0 in (ilist n1) return (ilist (n1 + H1)) with
     | Nil => H2
     | Cons n x ls1' => Cons (n + H1) x (app n ls1' H1 H2)
     end).

MetaCoq Quote Definition foo1 := (forall (H0 : ilist 0) (H1 : nat) (H2 : ilist H1),
     app 0 Nil H1 H2 = H2). (* on substitue les indices dans la variable sur laquelle on matche 
dans le corps de la fonction? *)


Definition foo2 := (forall (n : nat) (x : A) (ls1' : ilist n) (H1 : nat) (H2 : ilist H1),
     app _ (Cons n x ls1') H1 H2 = Cons (n + H1) x (app n ls1' H1 H2)).

MetaCoq Quote Definition foo2_reif:= 
(forall (n : nat) (x : A) (ls1' : ilist _) (H1 : nat) (H2 : ilist H1),
     app _ (Cons n x ls1') H1 H2 = Cons (n + H1) x (app n ls1' H1 H2)).

MetaCoq Quote Recursively Definition ilist_reif := ilist.

MetaCoq Quote Definition S_reif := S.

Print ilist_reif.

Print foo2.

Print foo.
Print foo2_reif.

Definition wrong_term := (tApp
                       (tInd
                          {|
                          inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string],
                                            "eq"%string);
                          inductive_ind := 0 |} [])
                       [tApp
                          (tInd
                             {|
                             inductive_mind := (MPfile
                                                  ["dependent_pattern_matching"%string;
                                                  "Sniper"%string], "ilist"%string);
                             inductive_ind := 0 |} [])
                          [tApp
                             (tConst
                                (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string)
                                []) [tRel 4; tRel 1]];
                       tApp
                         (tConst
                            (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                            "app"%string) [])
                         [tRel 4;
                         tApp
                           (tApp
                              (tConstruct
                                 {|
                                 inductive_mind := (MPfile
                                                      ["dependent_pattern_matching"%string;
                                                      "Sniper"%string], "ilist"%string);
                                 inductive_ind := 0 |} 1 []) [tRel 4]) [tRel 3; tRel 2]; 
                         tRel 1; tRel 0];
                       tCase
                         ({|
                          inductive_mind := (MPfile
                                               ["dependent_pattern_matching"%string;
                                               "Sniper"%string], "ilist"%string);
                          inductive_ind := 0 |}, 0, Relevant)
                         (tLambda
                            {| binder_name := nNamed "n1"%string; binder_relevance := Relevant |}
                            (tInd
                               {|
                               inductive_mind := (MPfile
                                                    ["Datatypes"%string; "Init"%string;
                                                    "Coq"%string], "nat"%string);
                               inductive_ind := 0 |} [])
                            (tLambda
                               {|
                               binder_name := nNamed "ls1"%string;
                               binder_relevance := Relevant |}
                               (tApp
                                  (tInd
                                     {|
                                     inductive_mind := (MPfile
                                                          ["dependent_pattern_matching"%string;
                                                          "Sniper"%string], "ilist"%string);
                                     inductive_ind := 0 |} []) [tRel 0])
                               (tApp
                                  (tInd
                                     {|
                                     inductive_mind := (MPfile
                                                          ["dependent_pattern_matching"%string;
                                                          "Sniper"%string], "ilist"%string);
                                     inductive_ind := 0 |} [])
                                  [tApp
                                     (tConst
                                        (MPfile ["Nat"%string; "Init"%string; "Coq"%string],
                                        "add"%string) []) [tRel 1; tRel 3]])))
                         (tApp
                            (tApp
                               (tConstruct
                                  {|
                                  inductive_mind := (MPfile
                                                       ["dependent_pattern_matching"%string;
                                                       "Sniper"%string], "ilist"%string);
                                  inductive_ind := 0 |} 1 []) [tRel 4]) 
                            [tRel 3; tRel 2])
                         [(0, tRel 0);
                         (3,
                         tLambda
                           {| binder_name := nNamed "n"%string; binder_relevance := Relevant |}
                           (tInd
                              {|
                              inductive_mind := (MPfile
                                                   ["Datatypes"%string; "Init"%string; "Coq"%string],
                                                "nat"%string);
                              inductive_ind := 0 |} [])
                           (tLambda
                              {| binder_name := nNamed "x"%string; binder_relevance := Relevant |}
                              (tVar "A"%string)
                              (tLambda
                                 {|
                                 binder_name := nNamed "ls1'"%string;
                                 binder_relevance := Relevant |}
                                 (tApp
                                    (tInd
                                       {|
                                       inductive_mind := (MPfile
                                                            ["dependent_pattern_matching"%string;
                                                            "Sniper"%string], "ilist"%string);
                                       inductive_ind := 0 |} []) [tRel 1])
                                 (tApp
                                    (tConstruct
                                       {|
                                       inductive_mind := (MPfile
                                                            ["dependent_pattern_matching"%string;
                                                            "Sniper"%string], "ilist"%string);
                                       inductive_ind := 0 |} 1 [])
                                    [tApp
                                       (tConst
                                          (MPfile ["Nat"%string; "Init"%string; "Coq"%string],
                                          "add"%string) []) [tRel 2; tRel 4]; 
                                    tRel 1;
                                    tApp
                                      (tConst
                                         (MPfile
                                            ["dependent_pattern_matching"%string; "Sniper"%string],
                                         "app"%string) []) [tRel 2; tRel 0; tRel 4; tRel 3]]))))]]).

Compute subst1 (tApp S_reif [tRel 0]) 0 wrong_term.


Notation foo4 := (tApp
         (tInd
            {|
            inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string], "eq"%string);
            inductive_ind := 0 |} [])
         [tApp
            (tInd
               {|
               inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                 "ilist"%string);
               inductive_ind := 0 |} [])
            [tApp (tConst (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string) [])
               [tRel 3; tRel 0]];
         tApp
           (tConst (MPfile ["dependent_pattern_matching"%string; "Sniper"%string], "app"%string) [])
           [tRel 3;
           tApp
             (tConstruct
                {|
                inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                  "ilist"%string);
                inductive_ind := 0 |} 1 []) [tRel 3; tRel 2; tRel 1]; tRel 0;
           tApp
             (tConstruct
                {|
                inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                  "nat"%string);
                inductive_ind := 0 |} 1 []) [tRel 0]];
         tCase
           ({|
            inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                              "ilist"%string);
            inductive_ind := 0 |}, 0, Relevant)
           (tLambda {| binder_name := nNamed "n1"%string; binder_relevance := Relevant |}
              (tInd
                 {|
                 inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                   "nat"%string);
                 inductive_ind := 0 |} [])
              (tLambda {| binder_name := nNamed "ls1"%string; binder_relevance := Relevant |}
                 (tApp
                    (tInd
                       {|
                       inductive_mind := (MPfile
                                            ["dependent_pattern_matching"%string; "Sniper"%string],
                                         "ilist"%string);
                       inductive_ind := 0 |} []) [tRel 0])
                 (tApp
                    (tInd
                       {|
                       inductive_mind := (MPfile
                                            ["dependent_pattern_matching"%string; "Sniper"%string],
                                         "ilist"%string);
                       inductive_ind := 0 |} [])
                    [tApp
                       (tConst (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string) [])
                       [tRel 1; tRel 2]])))
           (tApp
              (tConstruct
                 {|
                 inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                   "ilist"%string);
                 inductive_ind := 0 |} 1 []) [tRel 3; tRel 2; tRel 1])
           [(0,
            tApp
              (tConstruct
                 {|
                 inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                   "nat"%string);
                 inductive_ind := 0 |} 1 []) [tRel 0]);
           (3,
           tLambda {| binder_name := nNamed "n"%string; binder_relevance := Relevant |}
             (tInd
                {|
                inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                  "nat"%string);
                inductive_ind := 0 |} [])
             (tLambda {| binder_name := nNamed "x"%string; binder_relevance := Relevant |}
                (tVar "A"%string)
                (tLambda {| binder_name := nNamed "ls1'"%string; binder_relevance := Relevant |}
                   (tApp
                      (tInd
                         {|
                         inductive_mind := (MPfile
                                              ["dependent_pattern_matching"%string; "Sniper"%string],
                                           "ilist"%string);
                         inductive_ind := 0 |} []) [tRel 1])
                   (tApp
                      (tConstruct
                         {|
                         inductive_mind := (MPfile
                                              ["dependent_pattern_matching"%string; "Sniper"%string],
                                           "ilist"%string);
                         inductive_ind := 0 |} 1 [])
                      [tApp
                         (tConst (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string)
                            []) [tRel 2; tRel 3]; tRel 1;
                      tApp
                        (tConst
                           (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                           "app"%string) [])
                        [tRel 2; tRel 0; tRel 3;
                        tApp
                          (tConstruct
                             {|
                             inductive_mind := (MPfile
                                                  ["Datatypes"%string; "Init"%string; "Coq"%string],
                                               "nat"%string);
                             inductive_ind := 0 |} 1 []) [tRel 3]]]))))]]).




Notation foo3 := (tApp
         (tInd
            {|
            inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string], "eq"%string);
            inductive_ind := 0 |} [])
         [tApp
            (tInd
               {|
               inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                 "ilist"%string);
               inductive_ind := 0 |} [])
            [tApp (tConst (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string) [])
               [tApp
                  (tConstruct
                     {|
                     inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                       "nat"%string);
                     inductive_ind := 0 |} 1 []) [tRel 4]; tRel 1]];
         tApp
           (tConst (MPfile ["dependent_pattern_matching"%string; "Sniper"%string], "app"%string) [])
           [tApp
              (tConstruct
                 {|
                 inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                   "nat"%string);
                 inductive_ind := 0 |} 1 []) [tRel 4];
           tApp
             (tConstruct
                {|
                inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                  "ilist"%string);
                inductive_ind := 0 |} 1 [])
             [tRel 4; tRel 3; tRel 2]; 
           tRel 1; tRel 0];
         tCase
           ({|
            inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                              "ilist"%string);
            inductive_ind := 0 |}, 0, Relevant)
           (tLambda {| binder_name := nNamed "n1"%string; binder_relevance := Relevant |}
              (tInd
                 {|
                 inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                   "nat"%string);
                 inductive_ind := 0 |} [])
              (tLambda {| binder_name := nNamed "ls1"%string; binder_relevance := Relevant |}
                 (tApp
                    (tInd
                       {|
                       inductive_mind := (MPfile
                                            ["dependent_pattern_matching"%string; "Sniper"%string],
                                         "ilist"%string);
                       inductive_ind := 0 |} []) [tRel 0])
                 (tApp
                    (tInd
                       {|
                       inductive_mind := (MPfile
                                            ["dependent_pattern_matching"%string; "Sniper"%string],
                                         "ilist"%string);
                       inductive_ind := 0 |} [])
                    [tApp
                       (tConst (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string) [])
                       [tRel 1; tRel 3]])))
           (tApp
              (tConstruct
                 {|
                 inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                   "ilist"%string);
                 inductive_ind := 0 |} 1 [])
              [tRel 4; tRel 3; tRel 2])
           [(0, tRel 0);
           (3,
           tLambda {| binder_name := nNamed "n"%string; binder_relevance := Relevant |}
             (tInd
                {|
                inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                  "nat"%string);
                inductive_ind := 0 |} [])
             (tLambda {| binder_name := nNamed "x"%string; binder_relevance := Relevant |}
                (tVar "A"%string)
                (tLambda {| binder_name := nNamed "ls1'"%string; binder_relevance := Relevant |}
                   (tApp
                      (tInd
                         {|
                         inductive_mind := (MPfile
                                              ["dependent_pattern_matching"%string; "Sniper"%string],
                                           "ilist"%string);
                         inductive_ind := 0 |} []) [tRel 1])
                   (tApp
                      (tConstruct
                         {|
                         inductive_mind := (MPfile
                                              ["dependent_pattern_matching"%string; "Sniper"%string],
                                           "ilist"%string);
                         inductive_ind := 0 |} 1 [])
                      [tApp
                         (tConst (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string)
                            []) [tRel 2; tRel 4]; tRel 1;
                      tApp
                        (tConst
                           (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                           "app"%string) []) [tRel 2; tRel 0; tRel 4; tRel 3]]))))]]).

Definition new_term := (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
        (tInd
           {|
           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                             "nat"%string);
           inductive_ind := 0 |} [])
        (tProd {| binder_name := nAnon; binder_relevance := Relevant |} 
           (tVar "A"%string)
           (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
              (tApp
                 (tInd
                    {|
                    inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                      "ilist"%string);
                    inductive_ind := 0 |} []) [tRel 1])
              (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                 (tInd
                    {|
                    inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                      "nat"%string);
                    inductive_ind := 0 |} [])
                 (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                    (tApp
                       (tInd
                          {|
                          inductive_mind := (MPfile
                                               ["dependent_pattern_matching"%string;
                                               "Sniper"%string], "ilist"%string);
                          inductive_ind := 0 |} []) [tRel 0]) foo3))))).

Eval compute in new_term.

Print term.

(* TODO : question ? est-ce possible de remplacer par des evars pour que Coq infère le type tout seul ? *)

MetaCoq Unquote Definition essai := new_term.

Print essai.

(*TODO : ouvrir tous les binders de l'énoncé faux, substituer les indices bindés n1 ... nk par 
la fonction dans le type de retour du constructeur sur ces indices SAUF dans le tConstruct correspondant *)

Goal False.
get_def app.
expand_hyp app_def.
eliminate_fix_hyp H.
eliminate_pattern_matching_test H0.
assert (test1 : forall (H0 : ilist 0) (H1 : nat) (H2 : ilist H1),
     app 0 Nil H1 H2 = H2) by (intros ; reflexivity).

Fail eliminate_pattern_matching H0.
unquote_term (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
        (tInd
           {|
           inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                             "nat"%string);
           inductive_ind := 0 |} [])
        (tProd {| binder_name := nAnon; binder_relevance := Relevant |} 
           (tVar "A"%string)
           (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
              (tApp
                 (tInd
                    {|
                    inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                      "ilist"%string);
                    inductive_ind := 0 |} []) [tRel 1])
              (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                 (tInd
                    {|
                    inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                      "nat"%string);
                    inductive_ind := 0 |} [])
                 (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                    (tApp
                       (tInd
                          {|
                          inductive_mind := (MPfile
                                               ["dependent_pattern_matching"%string;
                                               "Sniper"%string], "ilist"%string);
                          inductive_ind := 0 |} []) [tRel 0])
                    (tApp
                       (tInd
                          {|
                          inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string],
                                            "eq"%string);
                          inductive_ind := 0 |} [])
                       [tApp
                          (tInd
                             {|
                             inductive_mind := (MPfile
                                                  ["dependent_pattern_matching"%string;
                                                  "Sniper"%string], "ilist"%string);
                             inductive_ind := 0 |} [])
                          [tApp
                             (tConst
                                (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string)
                                []) [tApp
                          (tConstruct
                             {|
                             inductive_mind := (MPfile
                                                  ["Datatypes"%string; "Init"%string; "Coq"%string],
                                               "nat"%string);
                             inductive_ind := 0 |} 1 []) [tRel 4]; tRel 1]];
                       tApp
                         (tConst
                            (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                            "app"%string) [])
                         [ tApp S_reif [tRel 4];
                         tApp
                           (tApp
                              (tConstruct
                                 {|
                                 inductive_mind := (MPfile
                                                      ["dependent_pattern_matching"%string;
                                                      "Sniper"%string], "ilist"%string);
                                 inductive_ind := 0 |} 1 []) [tRel 4]) [tRel 3; tRel 2]; 
                         tRel 1; tRel 0];
                       tCase
                         ({|
                          inductive_mind := (MPfile
                                               ["dependent_pattern_matching"%string;
                                               "Sniper"%string], "ilist"%string);
                          inductive_ind := 0 |}, 0, Relevant)
                         (tLambda
                            {| binder_name := nNamed "n1"%string; binder_relevance := Relevant |}
                            (tInd
                               {|
                               inductive_mind := (MPfile
                                                    ["Datatypes"%string; "Init"%string;
                                                    "Coq"%string], "nat"%string);
                               inductive_ind := 0 |} [])
                            (tLambda
                               {|
                               binder_name := nNamed "ls1"%string;
                               binder_relevance := Relevant |}
                               (tApp
                                  (tInd
                                     {|
                                     inductive_mind := (MPfile
                                                          ["dependent_pattern_matching"%string;
                                                          "Sniper"%string], "ilist"%string);
                                     inductive_ind := 0 |} []) [tRel 0])
                               (tApp
                                  (tInd
                                     {|
                                     inductive_mind := (MPfile
                                                          ["dependent_pattern_matching"%string;
                                                          "Sniper"%string], "ilist"%string);
                                     inductive_ind := 0 |} [])
                                  [tApp
                                     (tConst
                                        (MPfile ["Nat"%string; "Init"%string; "Coq"%string],
                                        "add"%string) []) [tRel 1; tRel 3]])))
                         (tApp
                            (tApp
                               (tConstruct
                                  {|
                                  inductive_mind := (MPfile
                                                       ["dependent_pattern_matching"%string;
                                                       "Sniper"%string], "ilist"%string);
                                  inductive_ind := 0 |} 1 []) [tRel 4]) 
                            [tRel 3; tRel 2])
                         [(0, tRel 0);
                         (3,
                         tLambda
                           {| binder_name := nNamed "n"%string; binder_relevance := Relevant |}
                           (tInd
                              {|
                              inductive_mind := (MPfile
                                                   ["Datatypes"%string; "Init"%string; "Coq"%string],
                                                "nat"%string);
                              inductive_ind := 0 |} [])
                           (tLambda
                              {| binder_name := nNamed "x"%string; binder_relevance := Relevant |}
                              (tVar "A"%string)
                              (tLambda
                                 {|
                                 binder_name := nNamed "ls1'"%string;
                                 binder_relevance := Relevant |}
                                 (tApp
                                    (tInd
                                       {|
                                       inductive_mind := (MPfile
                                                            ["dependent_pattern_matching"%string;
                                                            "Sniper"%string], "ilist"%string);
                                       inductive_ind := 0 |} []) [tRel 1])
                                 (tApp
                                    (tConstruct
                                       {|
                                       inductive_mind := (MPfile
                                                            ["dependent_pattern_matching"%string;
                                                            "Sniper"%string], "ilist"%string);
                                       inductive_ind := 0 |} 1 [])
                                    [tApp
                                       (tConst
                                          (MPfile ["Nat"%string; "Init"%string; "Coq"%string],
                                          "add"%string) []) [tRel 2; tRel 4]; 
                                    tRel 1;
                                    tApp
                                      (tConst
                                         (MPfile
                                            ["dependent_pattern_matching"%string; "Sniper"%string],
                                         "app"%string) []) [ tRel 2; tRel 0; tRel 4; tRel 3]]))))]])))))).


Print app_reif.
Abort.

End ilist.




MetaCoq Quote Recursively Definition ilist_reif' := ilist.

Print ilist_reif'.

Fixpoint get_indexes_term (t: term) (n : nat) :=
        match t with
            | tProd _ _ u => get_indexes_term u n
            | tApp u v => (remove_elem n v)
            | _ => nil 
end.

Fixpoint get_indexes_in_return_type_aux (l : list term) (acc : list (list term)) (n : nat) {struct l} :=
(* l is the list of the types of the constructors of an inductive type, n the number of parameters *)
match l with
| nil => nil
| t :: l' =>(get_indexes_term t n):: (get_indexes_in_return_type_aux l' acc n)
end.

Definition get_indexes_in_return_type l n := get_indexes_in_return_type_aux l nil n.

Definition test_index := list_types_of_each_constructor ilist_reif'.

Compute get_indexes_in_return_type test_index 1.

Fixpoint lift_list (n : nat) (l : list term) := match l with
| nil => nil
| cons x xs => (lift n 0 x) :: lift_list n xs
end.

Fixpoint lift_list_of_list (n : nat) (l : list (list term)) := match l with
| nil => nil
| cons x xs => (lift_list n x) :: lift_list_of_list n xs
end.

Fixpoint subst_list (n : nat) (l : list term) := match l with
| nil => nil
| cons x xs => (subst1 (tRel 0) n x) :: lift_list n xs
end.

Fixpoint subst_list_of_list (n : nat) (l : list (list term)) := match l with
| nil => nil
| cons x xs => (subst_list n x) :: subst_list_of_list n xs
end.

Compute lift_list_of_list 2 (get_indexes_in_return_type test_index 1).

Fixpoint not_t_construct_subst  (l : list term) (n : nat) (t  : term) := match t with
| tApp u l' => match u with 
        | tConstruct _ _ _  => t 
        | _ => tApp (subst l n u) (List.map (not_t_construct_subst l n) l')
end
| _ => subst l n t
end.



Fixpoint find_eq_and_subst_aux (E : term) (l_idx : list term) (n : nat) := 
(* ad hoc patch, works only if E is of the form forall x1, ... xn, tApp eq (f x1 ... xn) (foo) *)
match E with
| tProd na Ty U => tProd na Ty (find_eq_and_subst_aux U l_idx (n +1))
| tApp u l => match l with 
      | nil | [_] | [_ ; _] => E
      | x1:: x2 :: x3 :: l' => tApp u (subst l_idx n x1 :: (not_t_construct_subst l_idx n x2) :: x3 :: l')
      end
| _ => E
end.

Definition find_eq_and_subst E l_idx := find_eq_and_subst_aux E l_idx 0.

Compute subst_list_of_list 0 (get_indexes_in_return_type test_index 1).

Compute subst_list_of_list 0 (subst_list_of_list 0 (get_indexes_in_return_type test_index 1)).

Definition bar := subst_list_of_list 0 (subst_list_of_list 0 (get_indexes_in_return_type test_index 1)).

Print subst.

Ltac eliminate_pattern_matching_test H :=

  let n := fresh "n" in 
  epose (n := ?[n_evar] : nat);
  let T := type of H in
  let H' := fresh in
  assert (H' : False -> T);
  [ let HFalse := fresh in
    intro HFalse;
    let rec tac_rec m x :=
        match goal with
      | |- context C[match x with _ => _ end] =>  match constr:(m) with
                                    | 0 => fail
                                    | S ?p => instantiate (n_evar := p) 
                                        end
      | |- forall _, _ => let y := fresh in intro y; tac_rec (S m) y 
      | _ => fail
    end 
in
    tac_rec 0 ltac:(fresh) ;
    destruct HFalse
  | clear H' ;
run_template_program (tmQuoteRec T) (fun Env => 
let T := eval cbv in Env.2 in
let e := eval cbv in Env.1 in
let prod := eval cbv in (get_env T n) in clear n ;
let E := eval cbv in prod.1.2 in
let l := eval cbv in prod.1.1 in 
let A := eval cbv in prod.2 in
let l_ty_ctors := eval cbv in (list_types_of_each_constructor (e, A)) in
let n := eval cbv in (Datatypes.length l_ty_ctors) in
let l_ctors := eval cbv in (get_list_ctors_tConstruct A n) in
let list_of_hyp := eval cbv in (get_equalities E l_ctors l_ty_ctors l) in
 pose list_of_hyp) ].

Goal False.
get_def app.
expand_hyp app_def.
eliminate_fix_hyp H.
eliminate_pattern_matching_test H0.

Definition foo4 := (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
        (tSort
           {|
           Universe.t_set := {|
                             UnivExprSet.this := [(Level.lSet, 0)];
                             UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok (Level.lSet, 0) |};
           Universe.t_ne := Logic.eq_refl |})
        (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
           (tInd
              {|
              inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                "nat"%string);
              inductive_ind := 0 |} [])
           (tProd {| binder_name := nAnon; binder_relevance := Relevant |} 
              (tRel 1)
              (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                 (tApp
                    (tInd
                       {|
                       inductive_mind := (MPfile
                                            ["dependent_pattern_matching"%string; "Sniper"%string],
                                         "ilist"%string);
                       inductive_ind := 0 |} []) [tRel 2; tRel 1])
                 (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                    (tInd
                       {|
                       inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                         "nat"%string);
                       inductive_ind := 0 |} [])
                    (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                       (tApp
                          (tInd
                             {|
                             inductive_mind := (MPfile
                                                  ["dependent_pattern_matching"%string;
                                                  "Sniper"%string], "ilist"%string);
                             inductive_ind := 0 |} []) [tRel 4; tRel 0])
                       (tApp
                          (tInd
                             {|
                             inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string],
                                               "eq"%string);
                             inductive_ind := 0 |} [])
                          [tApp
                             (tInd
                                {|
                                inductive_mind := (MPfile
                                                     ["dependent_pattern_matching"%string;
                                                     "Sniper"%string], "ilist"%string);
                                inductive_ind := 0 |} [])
                             [tRel 5;
                             tApp
                               (tConst
                                  (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string)
                                  []) [tRel 4; tRel 1]];
                          tApp
                            (tConst
                               (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                               "app"%string) [])
                            [tRel 5; tRel 4;
                            tApp
                              (tApp
                                 (tConstruct
                                    {|
                                    inductive_mind := (MPfile
                                                         ["dependent_pattern_matching"%string;
                                                         "Sniper"%string], "ilist"%string);
                                    inductive_ind := 0 |} 1 []) [tRel 5; tRel 4]) 
                              [tRel 3; tRel 2]; tRel 1; tRel 0];
                          tCase
                            ({|
                             inductive_mind := (MPfile
                                                  ["dependent_pattern_matching"%string;
                                                  "Sniper"%string], "ilist"%string);
                             inductive_ind := 0 |}, 1, Relevant)
                            (tLambda
                               {| binder_name := nNamed "n1"%string; binder_relevance := Relevant |}
                               (tInd
                                  {|
                                  inductive_mind := (MPfile
                                                       ["Datatypes"%string; "Init"%string;
                                                       "Coq"%string], "nat"%string);
                                  inductive_ind := 0 |} [])
                               (tLambda
                                  {|
                                  binder_name := nNamed "ls1"%string;
                                  binder_relevance := Relevant |}
                                  (tApp
                                     (tInd
                                        {|
                                        inductive_mind := (MPfile
                                                             ["dependent_pattern_matching"%string;
                                                             "Sniper"%string], "ilist"%string);
                                        inductive_ind := 0 |} []) [tRel 6; tRel 0])
                                  (tApp
                                     (tInd
                                        {|
                                        inductive_mind := (MPfile
                                                             ["dependent_pattern_matching"%string;
                                                             "Sniper"%string], "ilist"%string);
                                        inductive_ind := 0 |} [])
                                     [tRel 7;
                                     tApp
                                       (tConst
                                          (MPfile ["Nat"%string; "Init"%string; "Coq"%string],
                                          "add"%string) []) [tRel 1; tRel 3]])))
                            (tApp
                               (tApp
                                  (tConstruct
                                     {|
                                     inductive_mind := (MPfile
                                                          ["dependent_pattern_matching"%string;
                                                          "Sniper"%string], "ilist"%string);
                                     inductive_ind := 0 |} 1 []) [tRel 5; tRel 4]) 
                               [tRel 3; tRel 2])
                            [(0, tRel 0);
                            (3,
                            tLambda
                              {| binder_name := nNamed "n"%string; binder_relevance := Relevant |}
                              (tInd
                                 {|
                                 inductive_mind := (MPfile
                                                      ["Datatypes"%string; "Init"%string;
                                                      "Coq"%string], "nat"%string);
                                 inductive_ind := 0 |} [])
                              (tLambda
                                 {| binder_name := nNamed "x"%string; binder_relevance := Relevant |}
                                 (tRel 6)
                                 (tLambda
                                    {|
                                    binder_name := nNamed "ls1'"%string;
                                    binder_relevance := Relevant |}
                                    (tApp
                                       (tInd
                                          {|
                                          inductive_mind := (MPfile
                                                               ["dependent_pattern_matching"%string;
                                                               "Sniper"%string], "ilist"%string);
                                          inductive_ind := 0 |} []) [tRel 7; tRel 1])
                                    (tApp
                                       (tConstruct
                                          {|
                                          inductive_mind := (MPfile
                                                               ["dependent_pattern_matching"%string;
                                                               "Sniper"%string], "ilist"%string);
                                          inductive_ind := 0 |} 1 [])
                                       [tRel 8;
                                       tApp
                                         (tConst
                                            (MPfile ["Nat"%string; "Init"%string; "Coq"%string],
                                            "add"%string) []) [tRel 2; tRel 4]; 
                                       tRel 1;
                                       tApp
                                         (tConst
                                            (MPfile
                                               ["dependent_pattern_matching"%string; "Sniper"%string],
                                            "app"%string) [])
                                         [tRel 8; tRel 2; tRel 0; tRel 4; tRel 3]]))))]]))))))).

Definition test3 := 

find_eq_and_subst_aux wrong_term (hd [foo] (tl bar)) 4.

Eval compute in test3.

Definition test4 := (tApp
         (tInd
            {|
            inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string], "eq"%string);
            inductive_ind := 0 |} [])
         [tApp
            (tInd
               {|
               inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                 "ilist"%string);
               inductive_ind := 0 |} [])
            [tApp (tConst (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string) [])
               [tApp
                  (tConstruct
                     {|
                     inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                       "nat"%string);
                     inductive_ind := 0 |} 1 []) [tRel 4]; tRel 1]];
         tApp (tConst (MPfile ["dependent_pattern_matching"%string; "Sniper"%string], "app"%string) [])
           [tApp
              (tConstruct
                 {|
                 inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                   "nat"%string);
                 inductive_ind := 0 |} 1 []) [tRel 4];
           tApp
             (tConstruct
                {|
                inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                  "ilist"%string);
                inductive_ind := 0 |} 1 [])
             [tApp
                (tConstruct
                   {|
                   inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                     "nat"%string);
                   inductive_ind := 0 |} 1 []) [tRel 4]; tRel 3; tRel 2]; tRel 1; 
           tRel 0];
         tCase
           ({|
            inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                              "ilist"%string);
            inductive_ind := 0 |}, 0, Relevant)
           (tLambda {| binder_name := nNamed "n1"%string; binder_relevance := Relevant |}
              (tInd
                 {|
                 inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                   "nat"%string);
                 inductive_ind := 0 |} [])
              (tLambda {| binder_name := nNamed "ls1"%string; binder_relevance := Relevant |}
                 (tApp
                    (tInd
                       {|
                       inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                         "ilist"%string);
                       inductive_ind := 0 |} []) [tRel 0])
                 (tApp
                    (tInd
                       {|
                       inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                         "ilist"%string);
                       inductive_ind := 0 |} [])
                    [tApp (tConst (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string) [])
                       [tRel 1; tRel 3]])))
           (tApp
              (tApp
                 (tConstruct
                    {|
                    inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                      "ilist"%string);
                    inductive_ind := 0 |} 1 []) [tRel 4]) [tRel 3; tRel 2])
           [(0, tRel 0);
           (3,
           tLambda {| binder_name := nNamed "n"%string; binder_relevance := Relevant |}
             (tInd
                {|
                inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                  "nat"%string);
                inductive_ind := 0 |} [])
             (tLambda {| binder_name := nNamed "x"%string; binder_relevance := Relevant |}
                (tVar "A"%string)
                (tLambda {| binder_name := nNamed "ls1'"%string; binder_relevance := Relevant |}
                   (tApp
                      (tInd
                         {|
                         inductive_mind := (MPfile
                                              ["dependent_pattern_matching"%string; "Sniper"%string],
                                           "ilist"%string);
                         inductive_ind := 0 |} []) [tRel 1])
                   (tApp
                      (tConstruct
                         {|
                         inductive_mind := (MPfile
                                              ["dependent_pattern_matching"%string; "Sniper"%string],
                                           "ilist"%string);
                         inductive_ind := 0 |} 1 [])
                      [tApp
                         (tConst (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string) [])
                         [tRel 2; tRel 4]; tRel 1;
                      tApp
                        (tConst
                           (MPfile ["dependent_pattern_matching"%string; "Sniper"%string], "app"%string)
                           []) [tRel 2; tRel 0; tRel 4; tRel 3]]))))]]).

Definition test5 := (tApp
         (tInd
            {|
            inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string], "eq"%string);
            inductive_ind := 0 |} [])
         [tApp
            (tInd
               {|
               inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                 "ilist"%string);
               inductive_ind := 0 |} [])
            [tApp (tConst (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string) [])
               [tApp
                  (tConstruct
                     {|
                     inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                       "nat"%string);
                     inductive_ind := 0 |} 1 []) [tRel 4]; tRel 1]];
         tApp (tConst (MPfile ["dependent_pattern_matching"%string; "Sniper"%string], "app"%string) [])
           [tRel 4;
           tApp
             (tApp
                (tConstruct
                   {|
                   inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                     "ilist"%string);
                   inductive_ind := 0 |} 1 []) [tRel 4]) [tRel 3; tRel 2]; tRel 1; 
           tRel 0];
         tCase
           ({|
            inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                              "ilist"%string);
            inductive_ind := 0 |}, 0, Relevant)
           (tLambda {| binder_name := nNamed "n1"%string; binder_relevance := Relevant |}
              (tInd
                 {|
                 inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                   "nat"%string);
                 inductive_ind := 0 |} [])
              (tLambda {| binder_name := nNamed "ls1"%string; binder_relevance := Relevant |}
                 (tApp
                    (tInd
                       {|
                       inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                         "ilist"%string);
                       inductive_ind := 0 |} []) [tRel 0])
                 (tApp
                    (tInd
                       {|
                       inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                         "ilist"%string);
                       inductive_ind := 0 |} [])
                    [tApp (tConst (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string) [])
                       [tRel 1; tRel 3]])))
           (tApp
              (tApp
                 (tConstruct
                    {|
                    inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                      "ilist"%string);
                    inductive_ind := 0 |} 1 []) [tRel 4]) [tRel 3; tRel 2])
           [(0, tRel 0);
           (3,
           tLambda {| binder_name := nNamed "n"%string; binder_relevance := Relevant |}
             (tInd
                {|
                inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                  "nat"%string);
                inductive_ind := 0 |} [])
             (tLambda {| binder_name := nNamed "x"%string; binder_relevance := Relevant |}
                (tVar "A"%string)
                (tLambda {| binder_name := nNamed "ls1'"%string; binder_relevance := Relevant |}
                   (tApp
                      (tInd
                         {|
                         inductive_mind := (MPfile
                                              ["dependent_pattern_matching"%string; "Sniper"%string],
                                           "ilist"%string);
                         inductive_ind := 0 |} []) [tRel 1])
                   (tApp
                      (tConstruct
                         {|
                         inductive_mind := (MPfile
                                              ["dependent_pattern_matching"%string; "Sniper"%string],
                                           "ilist"%string);
                         inductive_ind := 0 |} 1 [])
                      [tApp
                         (tConst (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string) [])
                         [tRel 2; tRel 4]; tRel 1;
                      tApp
                        (tConst
                           (MPfile ["dependent_pattern_matching"%string; "Sniper"%string], "app"%string)
                           []) [tRel 2; tRel 0; tRel 4; tRel 3]]))))]]).

Definition test6 := (tApp
         (tInd
            {|
            inductive_mind := (MPfile ["Logic"%string; "Init"%string; "Coq"%string], "eq"%string);
            inductive_ind := 0 |} [])
         [tApp
            (tInd
               {|
               inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                 "ilist"%string);
               inductive_ind := 0 |} [])
            [tApp (tConst (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string) [])
               [tApp
                  (tConstruct
                     {|
                     inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                       "nat"%string);
                     inductive_ind := 0 |} 1 []) [tRel 4]; tRel 1]];
         tApp (tConst (MPfile ["dependent_pattern_matching"%string; "Sniper"%string], "app"%string) [])
           [tApp
              (tConstruct
                 {|
                 inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                   "nat"%string);
                 inductive_ind := 0 |} 1 []) [tRel 4];
           tApp
             (tApp
                (tConstruct
                   {|
                   inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                     "ilist"%string);
                   inductive_ind := 0 |} 1 [])
                [ tRel 4]) [tRel 3; tRel 2]; 
           tRel 1; tRel 0];
         tCase
           ({|
            inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                              "ilist"%string);
            inductive_ind := 0 |}, 0, Relevant)
           (tLambda {| binder_name := nNamed "n1"%string; binder_relevance := Relevant |}
              (tInd
                 {|
                 inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                   "nat"%string);
                 inductive_ind := 0 |} [])
              (tLambda {| binder_name := nNamed "ls1"%string; binder_relevance := Relevant |}
                 (tApp
                    (tInd
                       {|
                       inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                         "ilist"%string);
                       inductive_ind := 0 |} []) [tRel 0])
                 (tApp
                    (tInd
                       {|
                       inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                         "ilist"%string);
                       inductive_ind := 0 |} [])
                    [tApp (tConst (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string) [])
                       [tRel 1; tRel 3]])))
           (tApp
              (tApp
                 (tConstruct
                    {|
                    inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                      "ilist"%string);
                    inductive_ind := 0 |} 1 []) [tRel 4]) [tRel 3; tRel 2])
           [(0, tRel 0);
           (3,
           tLambda {| binder_name := nNamed "n"%string; binder_relevance := Relevant |}
             (tInd
                {|
                inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                  "nat"%string);
                inductive_ind := 0 |} [])
             (tLambda {| binder_name := nNamed "x"%string; binder_relevance := Relevant |}
                (tVar "A"%string)
                (tLambda {| binder_name := nNamed "ls1'"%string; binder_relevance := Relevant |}
                   (tApp
                      (tInd
                         {|
                         inductive_mind := (MPfile
                                              ["dependent_pattern_matching"%string; "Sniper"%string],
                                           "ilist"%string);
                         inductive_ind := 0 |} []) [tRel 1])
                   (tApp
                      (tConstruct
                         {|
                         inductive_mind := (MPfile
                                              ["dependent_pattern_matching"%string; "Sniper"%string],
                                           "ilist"%string);
                         inductive_ind := 0 |} 1 [])
                      [tApp
                         (tConst (MPfile ["Nat"%string; "Init"%string; "Coq"%string], "add"%string) [])
                         [tRel 2; tRel 4]; tRel 1;
                      tApp
                        (tConst
                           (MPfile ["dependent_pattern_matching"%string; "Sniper"%string], "app"%string)
                           []) [tRel 2; tRel 0; tRel 4; tRel 3]]))))]]).


Definition new_term2 := tProd {| binder_name := nAnon; binder_relevance := Relevant |}
        (tSort
           {|
           Universe.t_set := {|
                             UnivExprSet.this := [(Level.lSet, 0)];
                             UnivExprSet.is_ok := UnivExprSet.Raw.singleton_ok (Level.lSet, 0) |};
           Universe.t_ne := Logic.eq_refl |})
        (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
           (tInd
              {|
              inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string], "nat"%string);
              inductive_ind := 0 |} [])
           (tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tRel 1)
              (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                 (tApp
                    (tInd
                       {|
                       inductive_mind := (MPfile ["dependent_pattern_matching"%string; "Sniper"%string],
                                         "ilist"%string);
                       inductive_ind := 0 |} []) [tRel 2; tRel 1])
                 (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                    (tInd
                       {|
                       inductive_mind := (MPfile ["Datatypes"%string; "Init"%string; "Coq"%string],
                                         "nat"%string);
                       inductive_ind := 0 |} [])
                    (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                       (tApp
                          (tInd
                             {|
                             inductive_mind := (MPfile
                                                  ["dependent_pattern_matching"%string; "Sniper"%string],
                                               "ilist"%string);
                             inductive_ind := 0 |} []) [tRel 4; tRel 0]) test6))))).



Fail MetaCoq Unquote Definition test3_unquote := new_term2.







(* TODO : comment trouver le 2 ??? il se trouve dans le nombre de pour tout présents avant 
dans la formule *)




