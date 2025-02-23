/* Imports. */

%{

open Type
open Ast.AstSyntax
%}


%token <int> ENTIER
%token <string> ID
%token RETURN
%token VIRG
%token PV
%token AO
%token AF
%token PF
%token PO
%token EQUAL
%token CONST
%token PRINT
%token IF
%token ELSE
%token WHILE
%token BOOL
%token INT
%token RAT
%token CO
%token CF
%token SLASH
%token NUM
%token DENOM
%token TRUE
%token FALSE
%token PLUS
%token MULT
%token INF
%token EOF
%token NEW
%token ADRESSE
%token NULL
%token DEREF
%token STATIC

(* Type de l'attribut synthétisé des non-terminaux *)
%type <programme> prog
%type <instruction list> bloc
%type <fonction> fonc
%type <instruction> i
%type <typ> typ
%type <typ * string * expression option> param (* expression option : Some v si il y a une valeur par defaut rien si non*)
%type <expression> e
%type <var> var 


(* Type et définition de l'axiome *)
%start <Ast.AstSyntax.programme> main

%%
(* 1. PROG′ → PROG $ *)
main : lfi=prog EOF     {lfi}

(* 2. PROG → VAR⋆ FUN⋆ id BLOC *)
prog : lv=var* lf=fonc* ID li=bloc  {Programme (lv, lf,li)}

(*  3. VAR→static TYPE id = E ; *)
var : STATIC t=typ n=ID EQUAL e1=e PV {VarGlobal(t, n, e1)}

(*  4. FUN → TYPE id ( DP ) BLOC *)
fonc : t=typ n=ID PO lp=separated_list(VIRG,param) PF li=bloc {Fonction(t,n,lp,li)}

(*  TYPE id ⟨ D ⟩? : D c'est la valeur par defaut qui est optionnel*) 
param : t=typ n=ID d1=option(d)  {(t,n,d1)}

(*  18. D → =E *)
d : EQUAL e1=e {e1} (* Régle d'affectation de la valeur par defaut *)

(* 5. BLOC → {I⋆ } *)
bloc : AO li=i* AF {li}

i :
| t=typ n=ID EQUAL e1=e PV          {Declaration (t,n,e1)} (*  6. I → TYPE id = E ;*)
| STATIC t=typ n=ID EQUAL e1=e PV   {VarLStatic(t, n, e1)} (*  7. I → |static TY PE id = E ; *) (*Déclaration d'une varaible static locale*)
| a1=a EQUAL e1=e PV                 {Affectation (a1, e1)} (* 8. I -> | A = E; *) (* Affectation sur un affectable *)
| CONST n=ID EQUAL e=ENTIER PV      {Constante (n,e)} (* 9. I ->  | const id = entier ; *)
| PRINT e1=e PV                     {Affichage (e1)} (* 10. I -> print E ; *)
| IF e1=e li1=bloc ELSE li2=bloc   {Conditionnelle (e1,li1,li2)} (* I -> if E BLOC else BLOC *)
| WHILE e1=e li=bloc               {TantQue (e1,li)} (* I -> while E BLOC *)
| RETURN e1=e PV                   {Retour (e1)} (* 13. I -> return E ; *)


a :
| DEREF a1=a PF       { Deref a1 }  (* Déférencement *) (*  14. A → id *)
| n=ID               { Ident n }  (* Identifiant simple *) (*  15.A -> ( ∗ A )*)

typ :
| BOOL          { Bool } (* 19. TYPE → bool *)
| INT           { Int } (* 20.  TYPE -> int*)
| RAT           { Rat } (* 21. TYPE -> rat *)
| t=typ MULT { Pointeur t } (* 22. TYPE -> TYPE* *)



e : 
| n=ID PO lp=separated_list(VIRG,e) PF   {AppelFonction (n,lp)} (*  23. E → id ( CP ) *)
| CO e1=e SLASH e2=e CF                  {Binaire(Fraction,e1,e2)} (*  24. E → [ E / E ]*)
| TRUE                                   {Booleen true} (*  28. E → true *)
| FALSE                                  {Booleen false} (*  29. E → false *)
| e=ENTIER                               {Entier e} (*  30. E → entier *)
| NUM e1=e                               {Unaire(Numerateur,e1)} (*  25. E → num E*)
| DENOM e1=e                             {Unaire(Denominateur,e1)} (* 26 . E → denom E*)
| a1=a                                   {Affectable a1} (*  27. E → *) (* Affectable comme expression *)
| PO e1=e PLUS e2=e PF                   {Binaire (Plus,e1,e2)} (*  31. E → ( E + E) *)
| PO e1=e MULT e2=e PF                   {Binaire (Mult,e1,e2)} (*  32. E →  ( E ∗ E) *)
| PO e1=e EQUAL e2=e PF                  {Binaire (Equ,e1,e2)} (*  33. E → ( E = E) *)
| PO e1=e INF e2=e PF                    {Binaire (Inf,e1,e2)} (*  34. E → ( E < E) *)
| PO e1=e PF                             {e1} (*  35. E →  ( E ) *)
| NULL                                   { Null } (*  36. E → null *)
| NEW t=typ                              { New t } (*  37. E → ( new TYPE ) *)
| ADRESSE n=ID                           { Adresse n } (*  38. E →  & id *)



