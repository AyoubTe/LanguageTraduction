(* Module de la passe de gestion des placement mémoire *)
(* doit être conforme à l'interface Passe *)

open Tds
open Ast
open Type

type t1 = Ast.AstType.programme
type t2 = Ast.AstPlacement.programme


(* Fonction qui renvoie le type à partir de l'information *)
let getType info =
  match (info_ast_to_info info) with 
  | InfoConst _ -> Int
  | InfoVar (_, t, _, _) -> t
  | InfoFun (_,tr, _) -> tr 

 let getInfoFct info =
    match info with
    | InfoFun (_, tr, lp) -> (tr,lp)
    | _ -> failwith "info ne concerne pas une fonction"

let rec analyse_placement_instruction i depl reg =
  match i with
  | AstType.Declaration (ia, e) ->
    (*récuperer le type t dans l'info i*)
    let t = getType ia in
    modifier_adresse_variable depl reg ia;
    (AstPlacement.Declaration (ia, e), getTaille t)

  | AstType.Affectation (i, e) -> 
    (AstPlacement.Affectation(i, e), 0)

  | AstType.Conditionnelle(e, bt, be) ->
    let nbt = analyse_placement_bloc bt depl reg in
    let nbe = analyse_placement_bloc be depl reg in
    (AstPlacement.Conditionnelle (e, nbt, nbe), 0)

  | AstType.TantQue (c, b) -> 
    let nb = analyse_placement_bloc b depl reg in
    (AstPlacement.TantQue (c, nb), 0)

  | AstType.Retour (e, ia) ->
    (* on récupère le type de retour de la fonciton*)
    let (tr, lp) = getInfoFct (info_ast_to_info ia) in
    let sommeTaille = List.fold_right (fun x y -> y + (getTaille x)) lp 0 in
    (AstPlacement.Retour(e, getTaille tr, sommeTaille), 0)

  | AstType.AffichageInt e -> 
    (AstPlacement.AffichageInt e , 0)

  | AstType.AffichageRat e -> 
    (AstPlacement.AffichageRat e , 0)

  | AstType.AffichageBool e -> 
    (AstPlacement.AffichageBool e , 0)

  | AstType.Empty -> 
    (AstPlacement.Empty , 0)

  and
  (* analyse_placement_bloc : AstType.bloc -> int -> string -> AstPlacement.bloc * int *)
  analyse_placement_bloc li depl reg =
    match li with
    | [] -> ([], 0)
    | h :: t ->
        let (ni, ti) = analyse_placement_instruction h depl reg in
        let (nli, tb) = analyse_placement_bloc t (ti + depl) reg in
        (ni::nli, ti+tb)

(* Fonction qui insère les adresses dans info_ast des paramètres et retourne la liste des info_ast des paramètres avec leurs adresses dedant *)
(* Parametres :
  - lp : info_ast list, la liste des info_ast des paramètres 
  - depl : deplacemnt initiale à 0 par rapport a LB (Link Base
  - reg : le registre (LB) *)
(* Profil : val analyse_parametres : info_ast list -> int -> string -> info_ast list = <fun> *)
let analyse_parametres lp depl reg =
  let rec aux l d acc =
    match l with
    | [] -> acc
    | h::t -> 
      let tp = getType h in
        (modifier_adresse_variable (- d - getTaille(tp)) reg h);
        aux t (d + getTaille(tp)) (h::acc)
        
      in aux lp depl []

(* AstType.Fonction -> AstPlacement.Fonction *)
let analyse_placement_fonction (AstType.Fonction(info, lp, li)) =
  let nlp = analyse_parametres (List.rev lp) 0 "LB" in
  let nli = analyse_placement_bloc li 3 "LB" in
  AstPlacement.Fonction(info, nlp, nli)

(* AstType.Programme -> AstPlaccemnt.Programme *)
let analyser (AstType.Programme(fonctions, prog)) =
  let nfs = List.map analyse_placement_fonction fonctions in
  let nb = analyse_placement_bloc prog 0 "SB" in
  AstPlacement.Programme(nfs, nb)
  