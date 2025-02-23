
(* Module de la passe de gestion des placement mémoire *)
(* doit être conforme à l'interface Passe *)

open Tds
open Ast
open Type
open Code
open Tam

type t1 = Ast.AstPlacement.programme
type t2 = string


(* Fonction qui recupère le nom a partir d'une info *)
(* info -> string *)
let getNom info =
  match (info_ast_to_info info) with
  | InfoConst (nc, _) -> nc
  | InfoVar (nv, _, _, _) -> nv 
  | InfoFun (nf, _, _) -> nf

(* Fonction qui renvoie le type à partir de l'information *)
(* info -> typ *)
let getType info =
  match (info_ast_to_info info) with 
  | InfoConst _ -> Int
  | InfoVar (_, t, _, _) -> t
  | InfoFun (_,tr, _) -> tr 

(* La fonction qui recupere le deplacement a partir de l'info *)
(* info -> int *)
let getDeplacement info =
  match (info_ast_to_info info) with 
  | InfoVar (_, _, d, _) -> d
  | _ -> failwith "Erreur"

(* La fonction qui recupere le registre a partir de l'info *)
(* info -> string *)
let getRegistre info =
  match (info_ast_to_info info) with 
  | InfoVar (_, _, _, r) -> r
  | _ -> failwith "Erreur"

(* Fonction d'anlyse code d'une expression *)
(* AstType.expression -> string *)
let rec analyse_code_expression e =
  match e with
  | AstType.AppelFonction (info, le) -> 
    begin
      (* charger toutes les expressions de le *)
      let cle = List.fold_right (fun x c -> (analyse_code_expression x) ^ c) le "" in
      let nf = getNom info in
      (cle ^ (call "SB" nf)) (* Appel de fonction nf => CALL (SB) nf *)
    end
    
  | AstType.Ident info -> (* Cas d'un identifiant *)
    let taille = getTaille (getType info) in (* On recupere la taille d'ident selon son type *)
    let dep = getDeplacement info in (* On recupere le deplacement de l'identifiant *)
    let reg = getRegistre info in (* On recupere le registre *)
    (load taille dep reg) (* Charger l'identifiant dans la pile *)
  
  | AstType.Booleen b -> (* Cas d'un boolean *)
    if b then
      (loadl_int 1) (* on charge la valeur 1 si le boolean est True *)
    else
      (loadl_int 0) (* On charge la valeur 0 si le boolean est False *)
    
  | AstType.Entier i -> 
    (loadl_int i) (* On charge la valeur d'entier dans la pile *)
  
  | AstType.Unaire (op, e1) ->
    begin
      let ae = analyse_code_expression e1 in (* On analyse le code d'expression puis recuprer ses instructions TAM *)
      match op with
      | Numerateur -> ae ^ (pop 0 1) (* On depile la premiere case de la pile *)
      | Denominateur -> ae ^ (pop 1 1) (* On depile la premiere case de la pile *)
    end

  | AstType.Binaire(op, e1, e2) -> 
    begin
      let ace1 = analyse_code_expression e1 in (* On analyse le code d'expression puis recuprer ses instructions TAM *)
      let ace2 = analyse_code_expression e2 in (* On analyse le code d'expression puis recuprer ses instructions TAM *)
      match op with
      | PlusInt -> ace1 ^ ace2 ^ (subr "IAdd") (* On retourne les instructions TAM d'addition des deux expression entiers *)
      | PlusRat -> ace1 ^ ace2 ^ (call "SB" "RAdd") (* On retourne les instructions TAM d'addition des deux expression rationnels *)
      | MultInt -> ace1 ^ ace2 ^ (subr "IMul") (* On retourne les instructions TAM de multiplication des deux expression entiers *)
      | MultRat -> ace1 ^ ace2 ^ (call "SB" "RMul") (* On retourne les instructions TAM de multiplication des deux expression rationnels *)
      | EquInt -> ace1 ^ ace2 ^ (subr "IEq") (* On retourne les instructions TAM d'egalité des deux expression entiers *)
      | EquBool -> ace1 ^ ace2 ^ (subr "IEq") (* On retourne les instructions TAM d'égalité des deux expression boolean *)
      | Fraction -> ace1 ^ ace2 ^ (call "SB" "norm") (* On retourne les instructions TAM de normalisation de rationnel *)
      | Inf -> ace1 ^ ace2 ^ (subr "ILss") (* On retourne les instructions TAM de comparaison des deux expression entiers *)
    end

(* analyse_code_instruction : Permet de recupere les code TAM des instructions *)
(* val analyse_code_expression : AstPlacement.Instruction -> string *)
let rec analyse_code_instruction i =
  match i with
  | AstPlacement.Declaration (info, e) -> (* cas de declaration *)
    let ce = analyse_code_expression e in (* on recupre le code tam d'anlyse d'expression *)
    let taille = getTaille (getType info) in (* On recupere la taille a partir d'info *)
    let dep = getDeplacement info in (* on recupere le deplacement a partir d'info *)
    let reg = getRegistre info in (* on recupere le registre a partir d'info *)
    let cp = (push taille) in (* On reserve taille case dans la pille *)
    (cp ^ ce ^(store taille dep reg)) (* On enregistre la valeur d'expression dans les cases reservees *)

  | AstPlacement.Affectation (info, e) -> (* Cas d'affectation *)
    let ce = analyse_code_expression e in (* On recupere le code TAM d'expression *)
    let taille = getTaille (getType info) in (*On recupere la taille d'e *)
    let dep = getDeplacement info in (* on recupere le deplacemenent d'e *)
    let reg = getRegistre info in (* on recupere le registre d'e *)
    (ce ^ (store taille dep reg)) (* On enregistre a la pile *)

  | AstPlacement.AffichageInt e ->
    let ce = analyse_code_expression e in (* On recupere le code TAM d'expression *)
    (ce ^ (subr "IOut")) (* Code d'affichage d'un entier : Appel de fonction d'iffichage d'un entier *)

  | AstPlacement.AffichageRat e ->
    let ce = analyse_code_expression e in (* On recupere le code TAM d'expression *)
    (ce ^ (call "SB" "ROut")) (* Code TAM d'affichage d'un rationnel *)

  | AstPlacement.AffichageBool e ->
    let ce = analyse_code_expression e in (* On recupre le code TAM d'expression *)
    (ce ^ (subr "BOut")) (* Code TAM d'affichage d'un boolean *)
  
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
      let cli = List.fold_right (fun i c -> (analyse_code_instruction i) ^ c) li "" in
      (cli ^ (pop 0 taille)) (* On depile tous les elements de ajouter a la pile dans la liste des instruction *) 

(* AstPlacement.fonction -> string *)
let analyse_code_fonction (AstPlacement.Fonction(info, _, (li, _))) = 
  let nf = getNom info in
  let cf = (label nf) in
  let cli = (List.fold_right (fun i c -> (analyse_code_instruction i) ^ c) li "") in
  let ch = (label "HALT") in
  cf ^ cli ^ ch

(* AstPlacement.programme -> string *)
let analyser (AstPlacement.Programme(fonctions, prog)) =
  let entete = getEntete() in
  let cm = label "main" in
  let cfs = (List.fold_right (fun f c -> c ^ (analyse_code_fonction f)) fonctions "") in
  let cp = analyse_code_bloc prog in
  let ch = label "HALT" in
  entete ^ cfs ^ cm ^ cp ^ ch

