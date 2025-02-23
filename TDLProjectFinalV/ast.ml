open Type

(* Interface des arbres abstraits *)
module type Ast =
sig
   type expression
   type instruction
   type fonction
   type programme
end


(* *************************************** *)
(* AST après la phase d'analyse syntaxique *)
(* *************************************** *)
module AstSyntax =
  struct
    (*Type affectable*)
    type affectable =
    | Ident of string
    | Deref of affectable

    (* Opérateurs unaires de Rat *)
    type unaire = Numerateur | Denominateur

    (* Opérateurs binaires de Rat *)
    type binaire = Fraction | Plus | Mult | Equ | Inf

    (* Expressions de Rat *)
    type expression =
      (* Appel de fonction représenté par le nom de la fonction et la liste des paramètres réels *)
      | AppelFonction of string * expression list
      (* Booléen *)
      | Booleen of bool
      (* Entier *)
      | Entier of int
      (* Opération unaire représentée par l'opérateur et l'opérande *)
      | Unaire of unaire * expression
      (* Opération binaire représentée par l'opérateur, l'opérande gauche et l'opérande droite *)
      | Binaire of binaire * expression * expression
      (*Expression qui est un affectable*)
      | Affectable of affectable (* E -> A *)
      (*Adresse d'un identifiant i.e une variable *)
      | Adresse of string
      (* Déclaration d'une nouvelle variable et récuperation d'un pointeur *)
      | New of typ
      (*Pointeur vide*)
      | Null
    
    (* type Déclaration varaibles globales *)
    type var = VarGlobal of typ * string * expression

    (* Instructions de Rat *)
    type bloc = instruction list
    and instruction =
      (* Déclaration de variable représentée par son type, son nom et l'expression d'initialisation *)
      | Declaration of typ * string * expression
      (*Déclaration de variable statique locale *)
      | VarLStatic of typ * string * expression
      (* Affectation d'une variable représentée par son nom et la nouvelle valeur affectée *)
      | Affectation of affectable * expression
      (* Déclaration d'une constante représentée par son nom et sa valeur (entier) *)
      | Constante of string * int
      (* Affichage d'une expression *)
      | Affichage of expression
      (* Conditionnelle représentée par la condition, le bloc then et le bloc else *)
      | Conditionnelle of expression * bloc * bloc
      (*Boucle TantQue représentée par la conditin d'arrêt de la boucle et le bloc d'instructions *)
      | TantQue of expression * bloc
      (* return d'une fonction *)
      | Retour of expression

    (* Structure des fonctions de Rat *)
    (* type de retour - nom - liste des paramètres (association type et nom et valeur par défaut ou Non) - corps de la fonction *)
    type fonction = Fonction of typ * string * (typ * string * expression option) list * bloc

    (* Structure d'un programme Rat *)
    (* liste de fonction - programme principal *)
    type programme = Programme of var list * fonction list * bloc

end


(* ********************************************* *)
(* AST après la phase d'analyse des identifiants *)
(* ********************************************* *)
module AstTds =
  struct
    (*Type affectable*)
    type affectable =
    | Ident of Tds.info_ast
    | Deref of affectable

    (* Expressions de Rat *)
    type expression =
      (* Appel de fonction représenté par le nom de la fonction et la liste des paramètres réels *)
      | AppelFonction of Tds.info_ast * expression list
      (* Booléen *)
      | Booleen of bool
      (* Entier *)
      | Entier of int
      (* Opération unaire représentée par l'opérateur et l'opérande *)
      | Unaire of AstSyntax.unaire * expression
      (* Opération binaire représentée par l'opérateur, l'opérande gauche et l'opérande droite *)
      | Binaire of AstSyntax.binaire * expression * expression
      (*Expression qui est un affectable*)
      | Affectable of affectable (* E -> A *)
      (*Adresse d'un identifiant i.e une variable *)
      | Adresse of Tds.info_ast
      (* Déclaration d'une nouvelle variable et récuperation d'un pointeur *)
      | New of typ
      (*Pointeur vide*)
      | Null

    (* type Déclaration varaibles statiques *)
    type var = VarGlobal of typ * Tds.info_ast * expression

    (* Instructions de Rat *)
    type bloc = instruction list
    and instruction =
      (* Déclaration de variable représentée par son type, son nom et l'expression d'initialisation *)
      | Declaration of typ * Tds.info_ast * expression
      (*Déclaration de variable statique locale *)
      | VarLStatic of typ * Tds.info_ast * expression
      (* Affectation d'une variable représentée par son nom et la nouvelle valeur affectée *)
      | Affectation of affectable * expression
      (* Affichage d'une expression *)
      | Affichage of expression
      (* Conditionnelle représentée par la condition, le bloc then et le bloc else *)
      | Conditionnelle of expression * bloc * bloc
      (*Boucle TantQue représentée par la conditin d'arrêt de la boucle et le bloc d'instructions *)
      | TantQue of expression * bloc
      (* return d'une fonction *)
      | Retour of expression * Tds.info_ast
      | Empty (* les nœuds ayant disparus: Const *)

    (* Structure des fonctions de Rat *)
    (* type de retour - nom - liste des paramètres (association type et nom et valeur par défaut ou Non) - corps de la fonction *)
    type fonction = Fonction of typ * Tds.info_ast * (typ * Tds.info_ast * expression option) list * bloc

    (* Structure d'un programme Rat *)
    (* liste de fonction - programme principal *)
    type programme = Programme of var list * fonction list * bloc

end


(* ******************************* *)
(* AST après la phase de typage *)
(* ******************************* *)
module AstType =
struct
  (*Type affectable*)
  type affectable =
  | Ident of Tds.info_ast
  | Deref of affectable * typ

  (* Opérateurs unaires de Rat *)
  type unaire = Numerateur | Denominateur

  (* Opérateurs binaires existants dans Rat - résolution de la surcharge *)
  type binaire = Fraction | PlusInt | PlusRat | MultInt | MultRat | EquInt | EquBool | Inf 

  (* Expressions de Rat *)
  type expression =
    (* Appel de fonction représenté par le nom de la fonction et la liste des paramètres réels *)
    | AppelFonction of Tds.info_ast * expression list
    (* Booléen *)
    | Booleen of bool
    (* Entier *)
    | Entier of int
    (* Opération unaire représentée par l'opérateur et l'opérande *)
    | Unaire of unaire * expression
    (* Opération binaire représentée par l'opérateur, l'opérande gauche et l'opérande droite *)
    | Binaire of binaire * expression * expression
    (*Expression qui est un affectable*)
    | Affectable of affectable (* E -> A *)
    (*Adresse d'un identifiant i.e une variable *)
    | Adresse of Tds.info_ast
    (* Déclaration d'une nouvelle variable et récuperation d'un pointeur *)
    | New of typ (* A faire il faut supprimer le type *)
    (*Pointeur vide*)
    | Null

  (* type Déclaration varaibles statiques *)
  type var = VarGlobal of Tds.info_ast * expression

  (* Instructions de Rat *)
  type bloc = instruction list
  and instruction =
    (* Déclaration de variable représentée par son type, son nom et l'expression d'initialisation *)
    | Declaration of Tds.info_ast * expression
    (*Déclaration de variable statique locale *)
    | VarLStatic of Tds.info_ast * expression
    (* Affectation d'une variable représentée par son nom et la nouvelle valeur affectée *)
    | Affectation of affectable * expression
    (* Affichage d'une expression *)
    | AffichageInt of expression
    | AffichageRat of expression
    | AffichageBool of expression
    (* Conditionnelle représentée par la condition, le bloc then et le bloc else *)
    | Conditionnelle of expression * bloc * bloc
    (*Boucle TantQue représentée par la conditin d'arrêt de la boucle et le bloc d'instructions *)
    | TantQue of expression * bloc
    (* return d'une fonction *)
    | Retour of expression * Tds.info_ast
    | Empty (* les nœuds ayant disparus: Const *)

  (* Structure des fonctions de Rat *)
  (* type de retour - nom - liste des paramètres (association type et nom et valeur par défaut ou Non) - corps de la fonction *)
  type fonction = Fonction of Tds.info_ast * (Tds.info_ast * expression option) list * bloc

  (* Structure d'un programme Rat *)
  (* liste de fonction - programme principal *)
  type programme = Programme of var list * fonction list * bloc

end


(* ******************************* *)
(* AST après la phase de placement *)
(* ******************************* *)
module AstPlacement =
struct
  type affectable = AstType.affectable

  (* Expressions existantes dans notre langage *)
  (* = expression de AstType  *)
  type expression = AstType.expression

  (* type Déclaration varaibles statiques *)
  type var = VarGlobal of Tds.info_ast * expression

  type bloc = instruction list * int (* taille du bloc *)
  and instruction =
  | Declaration of Tds.info_ast * expression
  (*Déclaration de variable statique locale *)
  | VarLStatic of Tds.info_ast * expression
  | Affectation of affectable * expression
  | AffichageInt of expression
  | AffichageRat of expression
  | AffichageBool of expression
  | Conditionnelle of expression * bloc * bloc
  | TantQue of expression * bloc
  | Retour of expression * int * int (* taille du retour et taille des paramètres *)
  | Empty

  (* informations associées à l'identificateur (dont son nom), liste de paramètres, corps, expression de retour *)
  (* Plus besoin de la liste des paramètres mais on la garde pour les tests du placements mémoire *)
  type fonction = Fonction of Tds.info_ast * (Tds.info_ast * expression option) list * bloc

  (* Structure d'un programme dans notre langage *)
  type programme = Programme of var list * fonction list * bloc
  
end
