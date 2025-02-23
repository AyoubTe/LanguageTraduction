(* Module de la passe de gestion du placement mémoire *)
(* doit être conforme à l'interface Passe *)

open Tds
open Ast
open Type
open Code
open Tam

type t1 = Ast.AstPlacement.programme
type t2 = string

(* Fonctions utilitaires pour extraire des infos de info_ast *)
let getNom info =
  match info with
  | InfoConst (nc, _) -> nc
  | InfoVar (nv, _, _, _) -> nv 
  | InfoFun (nf, _, _) -> nf
  | InfoVarSL(nvs,_,_,_,_) -> nvs

let getTypeInfo info =
  match info with 
  | InfoConst _ -> Int
  | InfoVar (_, t, _, _) -> t
  | InfoFun (_, tr, _) -> tr
  | InfoVarSL(_,tvs,_,_,_) -> tvs

let getDeplacement info =
  match info with 
  | InfoVar (_, _, d, _) -> d
  | InfoVarSL(_,_, dvs, _,_) -> dvs 
  | InfoConst _ | InfoFun _ -> failwith "Erreur: pas de déplacement"

let getRegistre info =
  match info with 
  | InfoVar (_, _, _, r) -> r
  | InfoVarSL(_,_,_,rvs,_) -> rvs
  | InfoConst _ | InfoFun _ -> failwith "Erreur: pas de registre"

let isInit info =
  match info with
  | InfoVarSL(_,_,_,_,b) -> b
  | _ -> failwith "C'est pas une variable locale statique"

(* Analyse d'un affectable pour LECTURE/ÉCRITURE, inspiré du snippet. *)
(* modifie = true si on veut écrire dans l'affectable, false si on veut lire *)
(* deref = indique si on est déjà dans un contexte de deref. *)
let rec analyse_code_affectable a modifie deref =
match a with
| AstType.Ident ia ->
  begin
    match info_ast_to_info ia with
    | InfoVar(_, t, dep, reg) ->
      if (deref || not modifie) then
        load (getTaille t) dep reg
      else
        store (getTaille t) dep reg
    | InfoConst (_, v) ->
      loadl_int v
    | _ -> failwith "analyse_code_affectable: Ident = Var ou Const attendu"
  end

| AstType.Deref (af, taf) -> 
  if (not modifie || deref) then
    (analyse_code_affectable af modifie true) ^ (loadi (getTaille taf))
  else
    (analyse_code_affectable af modifie true) ^ (storei (getTaille taf))

let rec analyse_code_expression e =
  match e with
  | AstType.AppelFonction (info, le) ->
      let cle = List.fold_right (fun x c -> (analyse_code_expression x) ^ c) le ""in
      let nf = getNom (info_ast_to_info info) in
      cle ^ call "SB" nf
  
  | AstType.Booleen b ->
      if b then loadl_int 1 else loadl_int 0

  | AstType.Entier i -> 
      loadl_int i

  | AstType.Null ->
      loadl_int 0

  | AstType.New typ ->
    push 1
    ^ loadl_int (getTaille typ)
    ^ subr "MAlloc"

  | AstType.Adresse ia ->
      let dep = getDeplacement (info_ast_to_info ia) in
      let reg = getRegistre (info_ast_to_info ia) in
      loada dep reg

  | AstType.Affectable a ->
    analyse_code_affectable a false false

  | AstType.Unaire (op, e1) ->
      let c1 = analyse_code_expression e1 in
      begin match op with
        | AstType.Numerateur   -> c1 ^ pop 0 1
        | AstType.Denominateur -> c1 ^ pop 1 1
      end

  | AstType.Binaire (op, e1, e2) ->
      let ce1 = analyse_code_expression e1 in
      let ce2 = analyse_code_expression e2 in
      match op with
      | AstType.PlusInt  -> ce1 ^ ce2 ^ subr "IAdd"
      | AstType.PlusRat  -> ce1 ^ ce2 ^ call "SB" "RAdd"
      | AstType.MultInt  -> ce1 ^ ce2 ^ subr "IMul"
      | AstType.MultRat  -> ce1 ^ ce2 ^ call "SB" "RMul"
      | AstType.EquInt   -> ce1 ^ ce2 ^ subr "IEq"
      | AstType.EquBool  -> ce1 ^ ce2 ^ subr "IEq"
      | AstType.Fraction -> ce1 ^ ce2 ^ call "SB" "norm"
      | AstType.Inf      -> ce1 ^ ce2 ^ subr "ILss"
      

let rec analyse_code_instruction i =
  match i with
  | AstPlacement.Declaration (info, e) ->
      let ce = analyse_code_expression e in
      let t = getTaille (getTypeInfo (info_ast_to_info info)) in
      let dep = getDeplacement (info_ast_to_info info) in
      let reg = getRegistre (info_ast_to_info info) in
      push t ^ ce ^ store t dep reg

  | AstPlacement.VarLStatic (info, e) ->
      (* if not (isInit (info_ast_to_info info) ) then *)
        let ce = analyse_code_expression e in
        let t  = getTaille (getTypeInfo (info_ast_to_info info)) in
        let dep = getDeplacement (info_ast_to_info info) in
        let reg = getRegistre (info_ast_to_info info) in
        setInit info;
        push t ^ ce ^ store t dep reg

  | AstPlacement.Affectation (a, e) ->
      let ce = analyse_code_expression e in
      let ca = analyse_code_affectable a true false in
      ce ^ ca

  | AstPlacement.AffichageInt e ->
      let ce = analyse_code_expression e in
      ce ^ subr "IOut"

  | AstPlacement.AffichageRat e ->
      let ce = analyse_code_expression e in
      ce ^ call "SB" "ROut"

  | AstPlacement.AffichageBool e ->
      let ce = analyse_code_expression e in
      ce ^ subr "BOut"

  | AstPlacement.Conditionnelle (c, bt, be) -> (* Cas d'une conditionnelle *)
    let ce = analyse_code_expression c in (* On recupere le code TAM d'c *)
    let etq = getEtiquette() in (* Generation d'une étiquette aleatoire *)
    let jmpif = (jumpif 0 etq) in (* Si la condition n'est pas vraie on bascule vers le bloc else *)
    let abt = analyse_code_bloc bt in (* analyse de bloc then => on recupere son code TAM *)
    let jmpfe = (jump (etq ^ "Fin")) in (* Si le bloc THEN est celui exécutée on passe a la fin de bloc *)
    let et = label etq in (* Etiquette *)
    let abe = analyse_code_bloc be in (* Analyse de bloc ELSE : On recuperse son code TAM *)
    let fet = label (etq ^ "Fin") in (* Etiquette de Fin de bloc *)
    (ce ^ jmpif ^ abt ^ jmpfe ^ et ^ abe ^ fet) (* Code TAM de conditionnelle *)

  | AstPlacement.TantQue (c, b) -> (* Cas de tantQue *)
    let ce = analyse_code_expression c in (* Analyse de condition (expression) => On recupere le code TAM *)
    let etq = getEtiquette() in (* Generation d'une etiquette *)
    let jmpf = (jumpif 0 (etq ^ "Fin")) in (* Sauter le code bloc TantQue et basculer vers la fin de code si la condition est fausse *)
    let et = label etq in (* Etiquette debut du code du bloc TantQue *)
    let ab = analyse_code_bloc b in (* Code TAM de Bloc TantQue *)
    let jet = (jumpif 1 etq) in (* Retester la condition *)
    let fet = label (etq ^ "Fin") in (* Etiquette de fin du bloc TantQue *)
    (ce ^ jmpf ^ et ^ ab ^ ce ^ jet ^ fet) (* Code TAM de TantQue *)

  | AstPlacement.Retour (e, tailleRet, tailleParam) -> (* Cas de Return *)
    let ce = analyse_code_expression e in (* Analyse de code d'expression *)
    (ce ^ (return tailleRet tailleParam)) (* Le code TAM de Retour*)

  | AstPlacement.Empty -> ""


and 
  analyse_code_bloc (li, taille) =
    let cli = List.fold_right (fun i c -> (analyse_code_instruction i)^c) li "" in
    (cli ^ (pop 0 taille)) (* On depile tous les elements et on l'ajoute a la pile dans la liste des instruction *) 

(* Fonction qui traite les valeurs des paramètres par defaut*)
let analyse_code_val_defaut p =
let (info, oe) = p in
match oe with
| None -> ""
| Some e -> 
  let dep = getDeplacement (info_ast_to_info info) in
  let reg = getRegistre (info_ast_to_info info) in
  let t = getTaille (getTypeInfo (info_ast_to_info info)) in
  let ce = analyse_code_expression e in
  ce ^ (store t dep reg) 

(* Analyse d’une fonction *)
let analyse_code_fonction (AstPlacement.Fonction(info, lp, (li, _))) = 
  let nf = getNom (info_ast_to_info info) in
  let cf = (label nf) in
  let cvd = (List.fold_right (fun v c -> (analyse_code_val_defaut v)^c) lp "") in 
  let cli = (List.fold_right (fun i c -> (analyse_code_instruction i)^c) li "") in
  let hc = (label "HALT") in
  cf ^ cvd ^ cli ^ hc

(* Analyse d’une variable globale (initialisation + store) *)
let analyse_code_var (AstPlacement.VarGlobal(info, e)) =
  let ce = analyse_code_expression e in
  let dep = getDeplacement (info_ast_to_info info) in
  let reg = getRegistre (info_ast_to_info info) in
  let t = getTaille (getTypeInfo(info_ast_to_info info)) in
  (push t ) ^ ce ^ (store t dep reg)

(* AstPlacement.programme -> string *)
let analyser (AstPlacement.Programme(vars, fonctions, prog)) =
  let entete = getEntete() in
  let mc = label "main" in
  let cvars = (List.fold_right (fun v c -> c^(analyse_code_var v)) vars "") in
  let cfs = (List.fold_right (fun f c -> c^(analyse_code_fonction f)) fonctions "") in
  let cp = analyse_code_bloc prog in
  let hc = label "HALT" in
  entete ^ cfs ^ mc ^ cvars ^ cp ^ hc