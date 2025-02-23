
(* Module de la passe de gestion des placement mémoire *)
(* doit être conforme à l'interface Passe *)

open Tds
open Ast
open Type

type t1 = Ast.AstType.programme
type t2 = Ast.AstPlacement.programme


(* Déplacement global pour les variables locales statiques *)
let deplVL = ref 0


(* Fonction qui renvoie le type à partir de l'information *)
let getTypeInfo info =
  match info with 
  | InfoConst _ -> Int
  | InfoVar (_, t, _, _) -> t
  | InfoFun (_,tr, _) -> tr

let getInfoFct info =
  match info with
  | InfoFun (_, tr, lp) -> (tr, lp)
  | _ -> failwith "info ne concerne pas une fonction"


(* Fonction val: analyse_placement_affectable : AstType.affectable -> AstPlacement.affectable *)
let rec analyse_placement_affectable a depl reg =
  match a with
  | AstType.Ident ia ->
    let t = getTaille (getTypeInfo (info_ast_to_info ia)) in
    (AstType.Ident ia, t)


  | AstType.Deref (af, taf) -> 
      let (naf, t) = analyse_placement_affectable af depl reg in
      (AstType.Deref (naf, taf), t)

(* analyse_placement_var *)
let analyse_placement_var v depl reg =
  match v with 
  | AstType.VarGlobal(info, e) ->
    let t = getTaille(getTypeInfo(info_ast_to_info info)) in
    modifier_adresse_variable depl reg info;
    (AstPlacement.VarGlobal(info, e), t)


(* analyse_placemnt_instruction*)
let rec analyse_placement_instruction i depl reg =
  match i with
  | AstType.Declaration (ia, e) ->
      let t = getTypeInfo (info_ast_to_info ia) in
      modifier_adresse_variable depl reg ia;
      (AstPlacement.Declaration (ia, e), getTaille t)
  
  | AstType.VarLStatic(info, e) ->
    let t = getTypeInfo (info_ast_to_info info) in
    let taille = getTaille t in
    modifier_adresse_variable (!deplVL) "SB" info;
    deplVL := !deplVL + taille;
    (AstPlacement.VarLStatic(info, e), taille)
    

      
  | AstType.Affectation (a, e) ->
    let (na, _) = analyse_placement_affectable a depl reg in
    (AstPlacement.Affectation(na, e), 0) 
    

  | AstType.Conditionnelle(e, bt, be) ->
      let nbt = analyse_placement_bloc bt depl reg in
      let nbe = analyse_placement_bloc be depl reg in
      (AstPlacement.Conditionnelle (e, nbt, nbe), 0)

  | AstType.TantQue (c, b) -> 
      let nb = analyse_placement_bloc b depl reg in
      (AstPlacement.TantQue (c, nb), 0)

  | AstType.Retour (e, ia) ->
      let (tr, lp) = getInfoFct (info_ast_to_info ia) in
      let sommeTaille = List.fold_right (fun (x, _) y -> y + (getTaille x)) lp 0 in
      (AstPlacement.Retour(e, getTaille tr, sommeTaille), 0)

  | AstType.AffichageInt e -> 
      (AstPlacement.AffichageInt e , 0)

  | AstType.AffichageRat e -> 
      (AstPlacement.AffichageRat e , 0)

  | AstType.AffichageBool e -> 
      (AstPlacement.AffichageBool e , 0)

  | AstType.Empty -> 
      (AstPlacement.Empty , 0)
    
and analyse_placement_bloc li depl reg =
  match li with
  | [] -> ([], 0)
  | h :: t ->
      let (ni, ti) = analyse_placement_instruction h depl reg in
      let (nli, tb) = analyse_placement_bloc t (ti + depl) reg in
      (ni::nli, ti+tb)
      

(* Fonction qui ajoute les adresses a la liste des parametres *)
(* Parametres:
  - lp : info_ast list; la liste des parametres
  - depl : int ; deplacemnt 
  - reg : string ; registre
*)
(* Retour: la liste des info_ast des parametres dedant leurs adresses *)
(* Profil : val analyse_parametres : info_ast list -> int -> string -> info_ast list = <fun> *)

let analyse_parametres lp depl reg =
  let f (h, e) (d, acc) =
    let tp = getTypeInfo (info_ast_to_info h) in
    modifier_adresse_variable (- d - getTaille(tp)) reg h;
    (d + getTaille(tp), (h, e)::acc)
  in
  let (_, res) = List.fold_right f lp (depl, []) in
  res



(* AstType.Fonction -> AstPlacement.Fonction *)
let analyse_placement_fonction (AstType.Fonction(info, lp, li)) =
  let nlp = analyse_parametres (List.rev lp) 0 "LB" in
  let nli = analyse_placement_bloc li 3 "LB" in
  AstPlacement.Fonction(info, nlp, nli)

let analyse_vars vars depl reg =
    let f v (acc, d) =
      let (nv, taille) = analyse_placement_var v d reg in
      ((nv, taille) :: acc, d + taille)
    in
    let (res, _) = List.fold_right f vars ([], depl) in
    res
  

(* AstType.Programme -> AstPlaccemnt.Programme *)
let analyser (AstType.Programme(vars, fonctions, prog)) =
  deplVL := 0;
  let nvars = analyse_vars (List.rev vars) 0 "SB" in
  let tailleVG = List.fold_right (fun (_, t) tg -> tg+t) nvars 0 in
  let nvs = List.map (fun (nv, _) -> nv) nvars in
  let nfs = List.map analyse_placement_fonction fonctions in
  let nb = analyse_placement_bloc prog ((!deplVL) + tailleVG) "SB" in
  AstPlacement.Programme(nvs, nfs, nb)
