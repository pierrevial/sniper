From MetaCoq Require Import All. 
Require Import String.
Open Scope string_scope.
From elpi Require Import elpi.

Inductive my_idents :=
  one_id (s : string ) : my_idents.

Ltac myclearbody x := clearbody x.

Print term.
Print ident.

Elpi Tactic clearbody_list_tVar.
Elpi Accumulate lp:{{

  pred unwrap_ident i: term, o: term.
    unwrap_ident (app [{{tVar}}, ID]) ID.
    unwrap_ident _ _.

  pred unwrap_idents i: term, o: list term.
    unwrap_idents (app [{{@cons }}, _ , X, X'])  [ID | IDS] :- unwrap_ident X ID, unwrap_idents X' IDS.
    unwrap_idents (app [{{@nil}} | _])  [].
    unwrap_idents _ [] :- coq.say "error".
    

    
  pred unwrap_bis i: term, o: list term.
    unwrap_bis (app [{{@cons }}, _ , X, X']) L :- coq.say "kikoo",
     unwrap_idents X L1, coq.say "lol", unwrap_bis X' TL,  coq.say "hum", std.append L1 TL L.
    unwrap_bis (app [{{@nil}} | _])  [].
    unwrap_bis _ [] :- coq.say "error".

pred clearbody_metacoq i: list term, i: goal, o: list (sealed-goal).
    clearbody_metacoq [Str | Strs] ((goal Ctx _ _ _ _) as G) GL :- coq.term->string Str SQ,  rex.split "\"" SQ [S], 
    (std.mem Ctx (def X N _ _), coq.name->id N S), coq.ltac.call "myclearbody" [trm X] G [G'|_GL1], 
    coq.ltac.open (clearbody_metacoq Strs) G' GL.
    clearbody_metacoq [] _G _GL.
  
  solve (goal _ _ _ _ [trm L] as G) GL :-
    unwrap_bis L Strs, clearbody_metacoq Strs G GL.


}}.
Elpi Typecheck.

Lemma test2 : forall (n : nat) (b := n + 1) (r := b) (k := b * r), nat.
Proof.
  intros n b r k.
Fail elpi clearbody_list_tVar n b r k.
Abort. 

Lemma test3 : forall (n : nat) (b := n + 1) (r := b) (k := b * r), nat.
Proof.
intros n b r k.
Fail elpi clearbody_list_tVar ( [ [tVar "b"; tVar "r"] ; [tVar "k" ]]).
exact b.
Show Proof.
Qed.

