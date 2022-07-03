

(*** Metavariables conventions ***)
(* indu : inductive  (the 1st argument of the constructor tInd )*)
(* mind: mutual_inductive_body *)
(* ooind : one_inductive_body *)
(* p : number of parameters of an inductive *)
(* roind : rank of an oind in a mind/rank of a projection *) 
(* noind : number of oind's in a mind *) (* no *)
(* nc : number of constructors of a oind *) (* k *)
(* k : rank of a constructor in a oind *)    (* i *)
(* n : number of arguments of a constructor *)
(* j : rank of an argument of a constructor *)
(* j: rank of case in a pattern-matching (constructor tCase): starts from 1 *)
(* REMPLACER : cela devrait être nc*)   

Require Import utilities. 
Require Import interpretation_algebraic_types.
Require Import elimination_polymorphism.
Require Import case_analysis.
Require Import MetaCoq.Template.All.
Require Import String.
Require Import List.
Require Import ZArith.

(* function to comment :  pose_inductive_tac *)

Open Scope string_scope.  

Import ListNotations MonadNotation. 




(* reified term selectors in lists and lists of lists *)
Definition sel_lterm (i : nat) (l : list term) := nth i l impossible_term_reif.

Definition sel_llterm (k : nat) (i : nat) (l : list (list term)) := 
  sel_lterm i (nth k l []).

Inductive nelist {A : Type} : Type :=
	sing :  A -> nelist    | necons : A -> nelist -> nelist .
      
Inductive biclist {A B : Type} : Type :=
(*  sing1 : A -> biclist  
  | sing2 : B -> biclist *)
  | bicnil : biclist
  | cons1 : A -> biclist -> biclist
  | cons2 : B -> biclist -> biclist. 



(*

Ltac proj k n x :=
   let k0 := n - k 
   match k with
   | 0 => match 

let x := fresh in pose constr:(k - 1) constr:(n -1) 
*)


Definition get_ind_ident (kerna : kername) := let (mdp , idind) := kerna in idind.





MetaCoq Quote Definition Type_reif := Eval hnf in Type.
MetaCoq Quote Definition Prop_reif := Eval hnf in Prop.
MetaCoq Quote Definition Set_reif := Eval hnf in Set.
MetaCoq Quote Definition eq_reif := Eval hnf in @eq. 

MetaCoq Quote Definition nat_reif := nat.
MetaCoq Quote Recursively Definition nat_env_reif := nat.



Definition list_nat := @list nat.
MetaCoq Quote Definition list_nat_reif :=  (@list nat).
MetaCoq Quote Recursively Definition list_nat_env_reif := list_nat.             
MetaCoq Quote Definition cons_nat_type_reif := (nat -> list_nat -> list_nat).
MetaCoq Quote Definition nil_type_reif := (forall (A : Type), list A).
(* \Q nil_type_reif and cons_nat_reif do not work because do not
currently have  the right universes levels *)


MetaCoq Quote Definition cons_reif := cons.
MetaCoq Quote Definition sing_reif := sing.
MetaCoq Quote Definition necons_reif := necons.


MetaCoq Quote Definition bicnil_reif := bicnil.
MetaCoq Quote Definition cons1_reif := cons1.
MetaCoq Quote Definition cons2_reif := cons2.





MetaCoq Quote Definition zero_reif := 0.
MetaCoq Quote Definition one_reif := 1.
MetaCoq Quote Definition two_reif := 2.


MetaCoq Quote Definition nil_nat_reif := Eval cbn in (@nil nat).
MetaCoq Quote Definition list_one_two_reif := Eval cbn in [1 ; 2].
MetaCoq Quote Definition list_one_two_two_reif := Eval cbn in [1 ; 2 ; 2].

MetaCoq Quote Definition list_one_two_two_reif' := (List.app [1] [2 ; 2]).



(** Reified objects functions *)
 
Definition cons_nat := @cons nat.


MetaCoq Quote Definition eq_nat_reif := Eval cbn in (@eq nat).


MetaCoq Quote Definition eq_term_reif := Eval cbn in (@eq term).

MetaCoq Quote Definition length_reif := @List.length.
MetaCoq Quote Definition le_reif := le.
MetaCoq Quote Definition S_reif := Eval cbn in S.
MetaCoq Quote Recursively Definition S_env_reif := S.

Print S_reif. 
Print S_env_reif.

MetaCoq Quote Definition O_reif := O.
MetaCoq Quote Definition add_reif := Eval cbn in Nat.add.
MetaCoq Quote Definition nil_reif := nil.
MetaCoq Quote Recursively Definition nil_env_reif := nil.
MetaCoq Quote Recursively Definition cons_env_reif := cons.
MetaCoq Quote Recursively Definition cons_nat_env_reif := cons_nat.
MetaCoq Quote Definition cons_nat_reif := cons_nat.
MetaCoq Quote Definition list_reif := @list.
MetaCoq Quote Recursively Definition list_env_reif := @list.

MetaCoq Quote Definition nelist_reif := @nelist.
MetaCoq Quote Recursively Definition nelist_env_reif := @nelist.

MetaCoq Quote Definition biclist_reif := @biclist.

Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_S : forall n, odd n -> even (S n)
with odd : nat -> Prop :=
    odd_S : forall n, even n -> odd (S n).

MetaCoq Quote Definition even_reif := even.
MetaCoq Quote Definition odd_reif := odd.




MetaCoq Quote Definition cons_typ_reif := (forall (A: Type), A -> list A -> list A).

Print list_env_reif.

Definition nat_indu := ltac:(let s := fresh in  pose_inductive_tac nat s ; exact s).
Definition list_indu := ltac:(let s := fresh in  pose_inductive_tac list s ; exact s).
Definition list_nat_indu := ltac:(let s := fresh in  pose_inductive_tac list s ; exact s).


(* \TODO eliminate the "let in" which currently appear in list_mind *)
Definition nat_mind :=  ltac:(let x := fresh in pose_mind_tac nat x ; cbn in x ; exact x).
Definition list_mind :=  ltac:(let x := fresh in pose_mind_tac list x ; cbn in x ; exact x).
Definition nelist_mind :=  ltac:(let x := fresh in pose_mind_tac @nelist x ; cbn in x ; exact x).
Definition biclist_mind :=  ltac:(let x := fresh in pose_mind_tac @biclist x ; cbn in x ; exact x).
Print biclist_mind.


MetaCoq Quote Definition bclist_reif := biclist.

Goal False.
Print bclist_reif.

let x := constr:(cutEvar bclist_reif) in pose x as kik ; compute in kik.
Abort.

Goal False.
let x:= constr:(get_params_from_mind biclist_mind) in pose x as biclist_params ; compute in biclist_params.
Abort.


Definition nat_oind := {|
ind_name := "nat"%string;
ind_type := tSort (Universe.of_levels (inr Level.lSet));
ind_kelim := IntoAny;
ind_ctors := [("O"%string, tRel 0, 0);
             ("S"%string,
             tProd
               {|
               binder_name := nAnon;
               binder_relevance := Relevant |}
               (tRel 0) (tRel 1), 1)];
ind_projs := [];
ind_relevance := Relevant |}.




Ltac pose_oind_tac t i idn := let s := fresh "s" in pose_mind_tac t s ; pose (nth i s.(ind_bodies)  nat_oind) as idn; simpl in idn ; clear s.
(* pose_oind take an (unreified) inductive  I and outputs the i-th one_inductive_block of I *) 
(* when I is not a mutual inductive, i should be equal to 0 *)
(* the tactic uses nat_oind as the defaut value for nth *)

Definition list_oind := ltac:(let s := fresh in pose_oind_tac list 0 s ; compute in s ; exact s).


(* pose_list_ctor_oind t i idn computes the lists of types of the constructors of i-th one inductive block of t and poses it as idn.
   Then, idn has type list term
*)
Ltac pose_list_ctor_oind t i idn := let x := fresh  in  pose_oind_tac t i x ; let lctor := constr:(list_ctor_oind x) in pose lctor as idn ; compute in idn ; clear x.

Goal False.
pose_list_ctor_oind list 0 kik.
clear.
pose_list_ctor_oind even 0 evenctor.
pose_list_ctor_oind even 1 oddctor.
let x := constr:(debruijn0 list_indu 2) in pose x as kik ; unfold debruijn0 in kik ; unfold utilities.switch_inductive in kik ; simpl in kik.

Abort.

(*testing get_ctors_and_types *)
Goal False. 
let x := constr:(get_ctors_and_types_i list_indu 1 1 0 [] list_oind) in pose x as gttlist ; compute in gttlist.
Abort.

(* \TMP
Definition get_ctors_and_types_i (indu : inductive) (p :nat) (n: nat) (i : nat) (u : Instance.t) (oind : one_inductive_body ) *)
             
Goal False. 
let x := constr:(hd (list_mind.(ind_bodies))) in pose x as kik ; compute in kik.
Abort.

Ltac kooooo t na :=
   constr:((4,5)).


(* Temporary: obtaining tVar list*)   

Inductive my_idents :=
  | one_id {A : Type} (a : A) : my_idents.


From elpi Require Import elpi.

Elpi Program function lp:{{

pred make-palindrome i:list A, o:list A.

make-palindrome L Result :-
  std.rev L TMP,
  std.append L TMP Result.

}}.

Elpi Query lp:{{

  make-palindrome [1,2,3] A

}}.


(* Query assignments:
  A = [1, 2, 3, 3, 2, 1] *)

Definition m (h : 0 = 1 ) P : P 0 -> P 1 :=
  match h as e in eq _ x return P 0 -> P x
  with eq_refl => fun (p : P 0) => p end.

Check m.



(* From elpi Require Export elpi. *)

Elpi Tactic clear.
Elpi Accumulate lp:{{
  pred not-hyp i:term, i:prop, o:term.
  not-hyp X (decl Y _ Ty) Y :- not (occurs X Ty), not (X = Y).
  not-hyp X (def Y _ Ty Bo) Y :- not (occurs X Ty ; occurs X Bo), not (X = Y).

  solve (goal Ctx R T E [trm X]) [seal (goal Ctx R T E [])] :- name X, !, std.do! [
    std.map-filter Ctx (not-hyp X) VisibleRev,
    prune E1 {std.rev VisibleRev}, % preserve the order
    std.assert-ok! (coq.typecheck E1 T) "cannot clear",
    E = E1
  ].
  solve (goal _ _ _ _ Args) _ :- coq.error "clear expects 1 name, you passed:" Args.
}}.
Elpi Typecheck.
Tactic Notation "eltac.clear" constr(V) := elpi clear (V).

Elpi Query lp:{{

coq.locate "m" (const C),
coq.env.const C (some (fun _ _ h\ fun _ _ p\ match _ (RT h p) _)) _,
coq.say "The return type of m is:" RT

}}.


(* Elpi Command clead_bod_id.
Elpi Accumùulate lp:{{
  main (T : term).
  
}} . *)

Definition f := [1 ; 2].

Elpi Query lp:{{

  coq.locate "f" (const C),
  coq.env.const C (some Bo) _
}}.



Elpi Accumulate lp:{{ std.spy-do![
  pred stringtoident  SQ S.
  stringtoindent SQ S :- coq.term->string Str SQ, rex.split "\"" SQ [S]]. 
  }}.




Elpi Tactic clear_body_list.
Elpi Accumulate lp:{{

  pred drop-body i:list argument, i:prop, o:prop.
  drop-body ToBeCleared (def V Name Ty _Bo) (decl V Name Ty) :- std.mem ToBeCleared (trm V), !.
  drop-body _ (decl _ _ _ as X) X.
  drop-body _ (def _ _ _ _ as X) X.

  msolve [nabla G] [nabla G1] :- pi x\ msolve [G x] [G1 x].
  msolve [seal  (goal Ctx _ T E ToBeCleared)] [seal (goal Ctx1 _ T E1 [])] :-
    std.map Ctx (drop-body ToBeCleared) Ctx1,
    @ltacfail! 0 => % this failure can be catch by ltac
      Ctx1 => % in the new context, do...
        std.assert-ok! (coq.typecheck-ty T _) "cannot clear since the goal does not typecheck in the new context",
    Ctx1 => std.assert-ok! (coq.typecheck E1 T) "should not happen", % E1 see all the proof variables (the pi x in the nabla case) and T is OK in Ctx1
    E = E1. % we make progress by saying that the old goal/evar is solved by the new one (which has the same type thanks to the line above)

}}.
Elpi Typecheck.






Tactic Notation "clear_body_list" hyp_list(l) := (* ltac1 will check that all arguments are names corresponding to existing proof variables *)
  elpi clear_body_list ltac_term_list:(l).

Elpi Command clear_body_list.
Elpi Accumulate lp:{{
  main [trm L] :-
  coq.unify-eq L (app [ {{ @cons }}, X , T , L0 ]) ok,
  % coq.ltac.call "idtac"  T, 
  main [trm L0].  
}}.
Elpi Typecheck.






Goal forall (n1 n2 : nat) (b1 b2 : bool), False.
Proof.
intros. 
pose (one_id "n2") as k. 
pose [ one_id "n1" ; one_id "b2"] as l0.
Fail Elpi clear_body_list [ one_id "n1" ; one_id "b2"].
pose [[ one_id "n1" ; one_id "b2"] ; [] ; [one_id "b1"]] as l. 
Abort.

(* Section  Clearbod.


From Ltac2 Require Ltac2.
From Coq Require Import Strings.String.
From Coq Require Import Init.Byte.


Import List.ListNotations.
Local Open Scope list.

Import Ltac2.


Ltac2 Type exn ::= [ NotStringLiteral(constr) | InvalidIdent(string) ].

Ltac2 coq_byte_to_int b :=
    (match! b with
     (* generate this line with python3 -c 'print(" ".join([\'| x%02x => %d\' % (x,x) for x in range(256)]))' *)
     | x00 => 0 | x01 => 1 | x02 => 2 | x03 => 3 | x04 => 4 | x05 => 5 | x06 => 6 | x07 => 7 | x08 => 8 | x09 => 9 | x0a => 10 | x0b => 11 | x0c => 12 | x0d => 13 | x0e => 14 | x0f => 15 | x10 => 16 | x11 => 17 | x12 => 18 | x13 => 19 | x14 => 20 | x15 => 21 | x16 => 22 | x17 => 23 | x18 => 24 | x19 => 25 | x1a => 26 | x1b => 27 | x1c => 28 | x1d => 29 | x1e => 30 | x1f => 31 | x20 => 32 | x21 => 33 | x22 => 34 | x23 => 35 | x24 => 36 | x25 => 37 | x26 => 38 | x27 => 39 | x28 => 40 | x29 => 41 | x2a => 42 | x2b => 43 | x2c => 44 | x2d => 45 | x2e => 46 | x2f => 47 | x30 => 48 | x31 => 49 | x32 => 50 | x33 => 51 | x34 => 52 | x35 => 53 | x36 => 54 | x37 => 55 | x38 => 56 | x39 => 57 | x3a => 58 | x3b => 59 | x3c => 60 | x3d => 61 | x3e => 62 | x3f => 63 | x40 => 64 | x41 => 65 | x42 => 66 | x43 => 67 | x44 => 68 | x45 => 69 | x46 => 70 | x47 => 71 | x48 => 72 | x49 => 73 | x4a => 74 | x4b => 75 | x4c => 76 | x4d => 77 | x4e => 78 | x4f => 79 | x50 => 80 | x51 => 81 | x52 => 82 | x53 => 83 | x54 => 84 | x55 => 85 | x56 => 86 | x57 => 87 | x58 => 88 | x59 => 89 | x5a => 90 | x5b => 91 | x5c => 92 | x5d => 93 | x5e => 94 | x5f => 95 | x60 => 96 | x61 => 97 | x62 => 98 | x63 => 99 | x64 => 100 | x65 => 101 | x66 => 102 | x67 => 103 | x68 => 104 | x69 => 105 | x6a => 106 | x6b => 107 | x6c => 108 | x6d => 109 | x6e => 110 | x6f => 111 | x70 => 112 | x71 => 113 | x72 => 114 | x73 => 115 | x74 => 116 | x75 => 117 | x76 => 118 | x77 => 119 | x78 => 120 | x79 => 121 | x7a => 122 | x7b => 123 | x7c => 124 | x7d => 125 | x7e => 126 | x7f => 127 | x80 => 128 | x81 => 129 | x82 => 130 | x83 => 131 | x84 => 132 | x85 => 133 | x86 => 134 | x87 => 135 | x88 => 136 | x89 => 137 | x8a => 138 | x8b => 139 | x8c => 140 | x8d => 141 | x8e => 142 | x8f => 143 | x90 => 144 | x91 => 145 | x92 => 146 | x93 => 147 | x94 => 148 | x95 => 149 | x96 => 150 | x97 => 151 | x98 => 152 | x99 => 153 | x9a => 154 | x9b => 155 | x9c => 156 | x9d => 157 | x9e => 158 | x9f => 159 | xa0 => 160 | xa1 => 161 | xa2 => 162 | xa3 => 163 | xa4 => 164 | xa5 => 165 | xa6 => 166 | xa7 => 167 | xa8 => 168 | xa9 => 169 | xaa => 170 | xab => 171 | xac => 172 | xad => 173 | xae => 174 | xaf => 175 | xb0 => 176 | xb1 => 177 | xb2 => 178 | xb3 => 179 | xb4 => 180 | xb5 => 181 | xb6 => 182 | xb7 => 183 | xb8 => 184 | xb9 => 185 | xba => 186 | xbb => 187 | xbc => 188 | xbd => 189 | xbe => 190 | xbf => 191 | xc0 => 192 | xc1 => 193 | xc2 => 194 | xc3 => 195 | xc4 => 196 | xc5 => 197 | xc6 => 198 | xc7 => 199 | xc8 => 200 | xc9 => 201 | xca => 202 | xcb => 203 | xcc => 204 | xcd => 205 | xce => 206 | xcf => 207 | xd0 => 208 | xd1 => 209 | xd2 => 210 | xd3 => 211 | xd4 => 212 | xd5 => 213 | xd6 => 214 | xd7 => 215 | xd8 => 216 | xd9 => 217 | xda => 218 | xdb => 219 | xdc => 220 | xdd => 221 | xde => 222 | xdf => 223 | xe0 => 224 | xe1 => 225 | xe2 => 226 | xe3 => 227 | xe4 => 228 | xe5 => 229 | xe6 => 230 | xe7 => 231 | xe8 => 232 | xe9 => 233 | xea => 234 | xeb => 235 | xec => 236 | xed => 237 | xee => 238 | xef => 239 | xf0 => 240 | xf1 => 241 | xf2 => 242 | xf3 => 243 | xf4 => 244 | xf5 => 245 | xf6 => 246 | xf7 => 247 | xf8 => 248 | xf9 => 249 | xfa => 250 | xfb => 251 | xfc => 252 | xfd => 253 | xfe => 254 | xff => 255
     end).


Ltac2 coq_byte_to_char b :=
    Char.of_int (coq_byte_to_int b).

Fixpoint coq_string_to_list_byte (s : string) : list byte :=
  match s with
  | EmptyString => []
  | String c s => Ascii.byte_of_ascii c :: coq_string_to_list_byte s
   end.

  (** copy a list of Coq byte constrs into a string (already of the right length) *)
  Ltac2 rec coq_byte_list_blit_list (pos : int) (ls : constr) (str : string) :=
    match! ls with
    | nil => ()
    | ?c :: ?ls =>
      let b := coq_byte_to_char c in
      String.set str pos b; coq_byte_list_blit_list (Int.add pos 1) ls str
  end.

  Ltac2 rec coq_string_length (s : constr) :=
    match! s with
    | EmptyString => 0
    | String _ ?s' => Int.add 1 (coq_string_length s')
    | _ => Control.throw (NotStringLiteral(s))
    end.

  Ltac2 compute c :=
    Std.eval_vm None c.

  (** [coq_string_to_string] converts a Gallina string in a constr to an Ltac2
  native string *)
  Ltac2 coq_string_to_string (s : constr) :=
    let l := coq_string_length s in
    let str := String.make l (Char.of_int 0) in
    let bytes := compute constr:(coq_string_to_list_byte $s) in
    let _ := coq_byte_list_blit_list 0 bytes str in
    str.

  Ltac2 ident_from_string (s : string) :=
    match Ident.of_string s with
    | Some id => id
    | None => Control.throw (InvalidIdent s)
    end.

    Ltac2 coq_string_to_ident (s : constr) := ident_from_string (coq_string_to_string s).

    Ltac2 get_opt o := match o with None => Control.throw Not_found | Some x => x end.

 


(* 
Ltac2 clearbody_id (t : constr)  :=  
       match! t with
       | one_id ?idn => let x := ident_from_string (coq_string_to_string idn) in  
        ltac1:(x |- clearbody x) 
   end. *)


(*
Ltac2 rec clearbody_id_list (l : constr)  :=  
   match! l with
  | [] => () 
  | ?ctor :: ?l0 => match! ctor with
    | one_id ?idn => let x := coq_string_to_string (idn) in 
     ltac1:(x |- clearbody x) ; clearbody_id_list l0
end
end. *)
Ltac2 cleabody2 s := ltac1:(s |- clearbody s).

Fail Ltac clearbody_id s := ltac2:(s1 |- let s := get_opt (Ltac1.to_constr s1) in
let ident := coq_string_to_ident s in
clearbody2 ident).

(* Ltac clearbody_id s := ltac2:(s1 |- let s2 := get_opt (Ltac1.to_constr s1) in
let ident := coq_string_to_ident s2 in
clearbody2 s2). *)


Goal forall (n1 n2 : nat) (b1 b2 : bool), False.
Proof.
intros. 
pose (one_id "n2") as k. 
Fail clearbody_id k.
pose [ one_id "n1" ; one_id "b2"] as l0.
Fail clearbody_id_list l0.
pose [[ one_id "n1" ; one_id "b2"] ; [] ; [one_id "b1"]] as l. 
Fail clearbody_id_llist l.
Abort.



From Coq Require Import List.
Import ListNotations.



Ltac clearbody_id_ctor ctor :=
  match eval hnf in ctor with
  | one_id ?idn =>
    clearbody idn
  end.

Ltac clearbody_id_list l :=
  match eval hnf in l with
  | [] => idtac
  | ?ctor :: ?l0 =>
    clearbody_id_ctor ctor ;
    clearbody_id_list l0
end.

Ltac clearbody_id_llist l :=
  match eval hnf in l with
  | [] => idtac
  | ?l0 :: ?tl0 => clearbody_id_list l0 ; clearbody_id_llist tl0
end.


Goal False.
pose (n3 := 0). 
Fail clearbody_id_ctor (one_id n3).
Abort. 

From Coq Require Import List.
Import ListNotations.

End Clearbod. *)


Ltac clearbody_id_list l :=  
  lazymatch eval hnf in l with
  | [] => idtac 
  | [?ctor ] => lazymatch eval hnf in ctor with 
    | one_id ?idn => clearbody idn end   
  | ?ctor :: ?l0 => lazymatch eval hnf in ctor with
    | one_id ?idn => let x := constr:(idn) in 
    let _ := match goal with _ => clearbody x end in clearbody_id_list l0
end
end. 


Ltac clearbody_id_llist l :=
  match eval hnf in l with
  | [] => idtac
  | ?l0 :: ?tl0 => clearbody_id_list l0 ; clearbody_id_llist tl0
end. 



Goal forall (n1 n2 : nat) (b1 b2 : bool), False.
Proof.
intros.
pose [[ one_id "n1" ; one_id "b2"] ; [] ; [one_id "b1"]] as l. 
pose [ one_id "n1" ; one_id "b2"] as l0.
Fail clearbody_id_list l0.
Fail clearbody_id_llist l.
Abort.



Ltac clearbody_id_ctor ctor :=
  match eval hnf in ctor with
  | one_id ?idn =>
    clearbody idn
  end.


  Goal False.
  pose (n3 := 0).
 clearbody_id_ctor (one_id n3).
  Abort. 

(***********************************)

(***** tests Pierre  (à transférer)      *********)

(***********************************)

(* i : numéro de la projection *)
(* exemple: cons est le 2ème constructeur de list 
 - pour elim_{1,0}, i est 0, ty_default est nat et pour elim_{1,1}, c'est 1 et list nat 
- nb_construct 2 ou 1.
- total_arg c'est 2 ou 3 (compte-t-on les paramètres ?)
*)
(* ty_default *)



Goal False.
let x := constr:(bind_def_val_in_gen [[tRel 0 ] ; [tRel 0 ; tApp list_reif [tRel 0] ; tApp list_reif [tRel 0]]; [tRel 0 ; tApp nat_reif [tRel 1]]  ] [1 ; 3 ; 2]) in pose x as kik ; compute in kik.
Abort.
(* list_args := val compute in (split (list_args0)).1   *)



(**** Old info function. To sort *)


Ltac pose_quote_term c idn :=
  let X :=  c in  quote_term X ltac:(fun Xast => pose Xast as idn).


Ltac get_ind_param t idn := 
    let tq := fresh "t_q" in pose_quote_term t tq ;
    lazymatch eval hnf in tq with
     | tInd ?indu ?u =>  pose (indu,u) as idn  ; clear tq
     end.




(**** Before producing the projections *)
 

Goal False. (* \TMP *)
let x := constr:(mkCase_list_param [2 ; 3 ; 1] 2 2) in pose x as mklistparamex ; compute in mklistparamex.
Abort.




(******* Producing the projections *)

Goal False.
(* \TODO commenter les exemples*)
let x := constr:(proj_ij 0 [] nat_reif nat_indu 1 0 [[]; [tRel 0]] [0 ; 1]
(nat_reif)) in pose x as pS_reif ; compute in pS_reif.
pose_unquote_term_hnf pS_reif pS.
clear.
let x := constr:(proj_ij 1 [Set_reif] list_reif list_indu 1 1 [[]; [tRel 0 ; tApp list_reif [tRel 0]]] [0 ; 2]
(tApp list_reif [tRel 0])) in pose x as proj_list11_reif ; compute in proj_list11_reif.
pose_unquote_term_hnf proj_list11_reif proj_list_11.
let x := constr:(proj_ij 1 [Set_reif] list_reif list_indu 1 0 [[]; [tRel 0 ; tApp list_reif [tRel 0]]] [0 ; 2]
(tRel 0)) in pose x as proj_list10_reif ; compute in proj_list10_reif.
pose_unquote_term_hnf proj_list10_reif proj_list_10. clear -proj_list_10 proj_list_11.
Abort.


Goal False. 
let x := constr:(collect_projs 1 [Set_reif] list_reif list_indu [[]; [tRel 0 ; tApp list_reif [tRel 0]]] [0 ; 2] 2) in pose x as list_projs ; compute in list_projs. 

let x := constr:(sel_llterm 1 0 list_projs)  
in pose x as p10_reif ; compute in p10_reif.
pose_unquote_term_hnf p10_reif p10.
let x := constr:(sel_llterm 1 1 list_projs) in pose x as p11_reif ; compute in p11_reif.
pose_unquote_term_hnf p11_reif p11.
Abort.






Goal False. 
let x := declare_projs_ctor_i na 1  [Set_reif]   list_reif list_indu [[]; [tRel 0 ; tApp list_reif [tRel 0]]] [0 ; 2]  1 [tRel 0 ; tApp list_reif [tRel 0]] 2 in pose x as tVars_list ;  compute in tVars_list .
pose_unquote_term_hnf (sel_lterm 0 tVars_list) p10_reif.
pose_unquote_term_hnf (sel_lterm 1 tVars_list) p11_reif.
Abort.


Goal False.
let x := declare_projs list  1 [Set_reif] list_reif list_indu [[]; [tRel 0 ; tApp list_reif [tRel 0]]] [0 ; 2] 2 in pose  x as tVars_list.
Abort.


Ltac declare_projs1 na p lA_rev  I  indu llAunlift  ln nc 
:= idtac "debut" ; 
let llAu_rev := constr:(tr_rev llAunlift) in let ln_rev := 
constr:(tr_rev ln) in idtac "let rec aux1" ; 
 let rec aux1 k  i  lAk' acc := 
 idtac "blut 0";  let x := constr:((i,lAk'))   in (* idtac "kikoo" ; *)
  match eval hnf in x with
   | (?i,?lAk') => match eval hnf in i with
     | 0 => constr:(acc) 
     | S ?i => match eval hnf in lAk' with
       | ?Akiu :: ?lAk' => idtac "res1" ; let pki := constr:(proj_ij p lA_rev I indu k i llAunlift ln (Akiu)) in 
       let name :=  fresh "proj_" na in let _ := match goal with _ => pose (name := pki ) end  in let y := metacoq_get_value (tmQuote name)  in let acc0 := constr:(y :: acc) in let res1 := aux1 k i lAk'  acc0 in constr:(res1)
       end end
   (* | _ => idtac "error declare_projs 1" *)
  end 
  in 
 let rec aux2 llAu' ln' k  acc :=
let y := constr:(((k,llAu'),ln')) 
in (* idtac "loool" ;*) match eval hnf in y with
| (?y0 , ?ln0') => (* idtac "blut 1" ; *)
  match eval cbv in ln0' with
  | (@nil nat) =>  (* idtac "blut 3 0" ; *) constr:(acc) 
  | ?i :: ?ln1' => (*  idtac "blut 3" ;*)
    match eval hnf in y0 with 
    | (?k, ?lAu') => lazymatch eval hnf in k with
      | S ?k => (* idtac "blut 5" ; *) match eval hnf in lAu' with
        | ?lAk :: ?lAu'=> let res2 := aux2 llAu' ln' k constr:((aux1 k i (tr_rev lAk) (@nil term)) :: acc) in constr:(res2)
  end 
  end   
  end
  end 
  (* |_ => idtac "error declare_projs 1" *)
end
in 
let res := aux2 llAu_rev ln_rev nc (@nil term)  in constr:(res)
. 


Goal False.
let x := declare_projs list  1 [Set_reif] list_reif list_indu [[]; [tRel 0 ; tApp list_reif [tRel 0]]] [0 ; 2] 2 in pose x as dp_list.
Abort.

(**** producing the generation statement *)




Goal false.
let x := constr:(get_eq_x_ctor_projs 3 (S_reif) [tRel 0; tRel 25; tRel 49] 
8) in pose x as gexcpex ; compute in gexcpex.
Abort.


Goal False.
let x:= constr:(get_generation_disjunction 3 nat_reif  100 [S_reif ; O_reif ; O_reif ]
  [[tRel 13 ; tRel 15 ; tRel 8] ; [tRel 33 ; tRel 45] ; [tRel 60 ; tRel 70 ; tRel 72]] [3 ; 2 ; 3]) in pose x as ggdex ; compute in ggdex.  clear.
Abort.

Goal False.
let x := constr:(args_of_projs_in_disj [3 ; 8 ; 2]) in pose x as kik ; compute in kik.
Abort.
  
Goal False.
Proof.
pose (2,3) as x. pose x.1 as y. Eval compute in y.
Abort.





Goal False. (* \TMP *)
let x := kooooo list blut in pose x as kik.
Abort.




Goal False. 

pose_gen_statement list. 
pose_gen_statement @nat.
pose_gen_statement @biclist.
pose_quote_term (fun (A : Type) (x x0 : list A) =>
match x0 with
| [] => x
| _ :: x1 => x1
end ) pl1.
pose_quote_term (fun (A : Type) (x : A) (x0 : list A) =>
match x0 with
| [] => x
| x1 :: _ => x1
end ) pl0.
Abort.


Goal False.
 pose_quote_term
(fun (l : list nat) => match l with
| [] => 0
| x  :: l0 => x end
  ) p1.
  pose_quote_term
  (fun (l : @biclist nat bool) => match l with
  | bicnil => 0
  | cons1 x l0 => x 
  | cons2 _ _ => 1 end 
    ) p2.
clear.
pose_quote_term (fun (A : Type)  ( l : @nelist A)  => match l with
| sing a => a 
| necons  x l0 => x 
end
  ) p3.
Abort.

Goal False.
pose_gen_statement  list. 
pose_gen_statement  nat.
pose_quote_term  (forall (A : Type) (d : A) (d0 x : list A), x = [] \/ x = proj_list0 A d x :: proj_list A d0 x) gen_stat_reif. 
pose_quote_term (fun (A : Type) (x x0 : list A) => match x0 with
| [] => x
| _ :: x1 => x1
end ) pl1.
pose_quote_term (fun (A : Type) (x : A) (x0 : list A) => match x0 with
| [] => x
| x1 :: _ => x1
end ) pl0.
pose_quote_term (fun x x0 : nat => match x0 with
| 0 => x
| S x1 => x1
end ) pn0.
Abort.


(***********************************************)
(* Tests on utilities.v                        *)
(***********************************************)


Goal False.
let x := constr:(mkProd_rec [tRel 3 ; tRel 5 ; tRel 8] (tRel 13)) in pose x as mprex ; compute in mprex.
Abort.


Goal False. 
info_indu nat nat_info_indu.
info_indu list list_info_indu.
Abort.


Goal False.
let x := constr:(Rel_list 8 4) in pose x as kik ; compute in kik.
Abort.





(***********************************************)
(* Tests on interpretation_algebraic_types.v   *)
(***********************************************)

Goal False.
info_indu nat natoblut.
info_indu list listoblut.
Abort.



Goal False.
let x := constr:(is_inj (tApp list_reif [tRel 2]) cons_reif [Set_reif ; tRel 0 ; tApp list_reif [tRel 1]] 1) in pose x as is_inj_cons ; compute in is_inj_cons.
pose_unquote_term_hnf is_inj_cons is_inj_cons_blut.
Abort.



Goal forall (n m k: nat), exists (x y z: nat), x = n /\ y = m /\ z = k .
Proof. intros_exist_aux  3 ltac:(idtac).  let x := fresh "x" in let x:= fresh "x" in idtac. repeat split.
Abort.

(***********************************************)
(* Tests on eliminators.v                      *)
(***********************************************)

(* meaning of the metavariables *)
(* nbproj : rank of a projection e.g. *)
(* exemple: cons est le 2ème constructeur de list 
 - pour elim_{1,0}, nbproj est 0, ty_default est nat et pour elim_{1,1}, c'est 1 et list nat 
- nb_construct 2 ou 1.
- total_arg c'est 2 ou 3 (compte-t-on les paramètres ?)
*)


(* _app : the inductive applied to its possible de Bruijn indices
* nat_app = nat_reif
* list_app = list_reif [Rel 0]
* nelist_app = nelist_reif [Rel0]
*)


(* _total_args or _tot_args is equal to the total number of parameters of the constructors:
   is equal to 1 for nat
   is equal to 2 for list, 
   is equal to 3 for nelist
*)

(* _lpars :
 nat_lpars = []
 list_lpars = [Rel 3]
 nelist_pars = [Rel 4]
*)

(* list_args := (split list_args_len).1 :
* nat_list_args = [ [] ; nat_reif ]
* list_list_args = [ [] ; [Rel 0 ; list_reif [Rel 0]]]
* nelist_list_args =  [ [Rel 0] ; [Rel 0 ; nelist_reif [Rel 0] ] ]
*)

(* list_ty 
* nat_list_ty = [nat_reif ; Prod _ nat_reif nat_reif]
* list_list_ty = [ tProd "A" Set_reif. list_reif [Rel 0] ;
   tProd "A" Set_reif. tProd _ (Rel 0). tProd _ (list_reif [Rel 1]). list_reif Rel 2  ]
* nelist_list_ty = [ tProd "A" Set_reif. tProd _ (Rel 0). nelist_reif [Rel 1] ; 
   tProd "A" Set_reif. tProd _ (Rel 0). tProd _ (nelist_reif [Rel 1]). nelist_reif Rel 2  ]
   *)

(* list_pars 
* nat_list_pars = []
* list_list_pars = [Set_reif]
* nelist_list_pars = [Set_reif].
*)

(* npars
nat_npars = 0
list_npars = 1
nelist_npars =
*)

Goal False.
split_info1 nat "nat". clear.
split_info1 list "list".  (* the second arg seems useless*)
clear. split_info1 @nelist  "nelist".
Abort.


Goal False.
split_info1 list "list". 
Print get_nbproj_nbargprevcons.
let res :=  (get_nbproj_nbargprevcons n I list_ty_pars list_app list_indu list_npars list_list_args list_tot_args list_lpars list_constructors_reif nb (@nil term)) in pose res as blut. Eval compute in blut.


Ltac get_nbproj_nbargprevcons n I ty_pars I_app I_indu npars list_args total_args lpars list_constructors_reif nb list_eq :=
match n with
Abort.


Ltac get_nbproj_nbargprevcons n I ty_pars I_app I_indu npars list_args total_args lpars list_constructors_reif nb list_eq :=


(**** eliminators.v ****)

Goal False.

Print nil_type_reif.
pose (tProd
  (mkNamed "A")
  (tSort
     (Universe.of_levels
        (inr
           (Level.Level
              "Sniper.aux_fun_tests.465"))))
  (tApp
    list_reif [tRel 0]))
as blut0.
pose (tProd
  (mkNamed "A")
  (tSort
     (Universe.of_levels
        (inr
           (Level.Level
              "Sniper.aux_fun_tests.387"))))
  (tProd
     {|
       binder_name := nAnon;
       binder_relevance := Relevant
     |} (tRel 0)
     (tProd
        {|
          binder_name := nAnon;
          binder_relevance := Relevant
        |}
        (tApp
           list_reif [tRel 1])
        (tApp list_reif [tRel 2])))) as blut1.
(* let list_info := fresh "list_info" in get_info_quote list list_info. *)
(* let '(list_indu, list_I_app, list_lpars, list_total_args, list_lists_args, list_list_ty, list_ty_pars, list_npars) := ????? *)



split_info1 list "list".

get_list_args_len_quote list list_lal.
get_ty_arg_constr list list_tarc.

pose ((tApp (* en mettant un idtac dans eliminators.v *)
   (tInd
      {|
        inductive_mind :=
          (MPfile
             ["Datatypes"; "Init";
             "Coq"], "list");
        inductive_ind := 0
      |} []) [tRel 0])) as list_ty_default.
(* on aussi tRel 0 qui doit correspondent à un autre ty_default *)

(* pour ty_default avec un idtac *)



pose (tLambda
   {|
     binder_name := nNamed "x";
     binder_relevance := Relevant
   |}
   (tApp
      (tInd
         {|
           inductive_mind :=
             (MPfile
                ["Datatypes"; "Init";
                "Coq"], "list");
           inductive_ind := 0
         |} []) [tRel 2])
   (tApp
      (tInd
         {|
           inductive_mind :=
             (MPfile
                ["Datatypes"; "Init";
                "Coq"], "list");
           inductive_ind := 0
         |} []) [tRel 3])) as rtyp1. 
pose 
(tLambda
   {|
     binder_name := nNamed "x";
     binder_relevance := Relevant
   |}
   (tApp
      (tInd
         {|
           inductive_mind :=
             (MPfile
                ["Datatypes"; "Init";
                "Coq"], "list");
           inductive_ind := 0
         |} []) [tRel 2]) 
   (tRel 3)) as rtyp0.


(* proj_one_constructor_default_var (i : term) (ty_default : term)
 (I : inductive) (npars : nat) (nbproj : nat) (nbconstruct : nat)
(ty_arg_constr : list (list term)) (return_type : term) *) 
clear list_info.
let x := constr:(proj_one_constructor_default_var  (tApp list_reif [tRel 0]) 
 (tApp list_reif [tRel 0])  
list_indu 1 0 1 list_tarc rtyp1)
in pose x as y; compute in y.
Print tCase.
pose_unquote_term_hnf y projtruc.
Abort.
