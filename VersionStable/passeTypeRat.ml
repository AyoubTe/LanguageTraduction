(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)

open Tds
open Exceptions
open Ast
open Type

type t1 = Ast.AstTds.programme
type t2 = Ast.AstType.programme


(* Une foncion qui renvoie le type de retour d'une fonctiona à partir son info *)
let getInfoFct info =
  match info with
  | InfoFun (_, tr, lp) -> (tr,lp)
  | _ -> failwith "info ne concerne pas une fonction"

(* Fonction qui permet de recuperer le type a partir d'info_ast *)
let getType info =
  match (info_ast_to_info info) with
  | InfoFun (_, t, _) -> t
  | InfoConst (_, _) -> Int
  | InfoVar (_, tp, _, _) -> tp

(* analyse_tds_expression : AstTds.expression -> (AstType.expression, typ) *)
let rec analyse_type_expression e =
  match e with
  | AstTds.AppelFonction (ia, le) ->
      (* On récupère le type de retour tr et les types des parametres ltp dans info *)
      let (tr, ltp) = getInfoFct (info_ast_to_info ia) in (* On récupère le type de retour de la fonction et On récupère la liste des types des paramètres de la fonction *)
      let nle = List.map analyse_type_expression le in (* on analyse la liste des expressions et a le format [(e1, t1), ..., (en, tn)]*)
      let tps = List.map (fun (_, t) -> t ) nle in (* récupère la liste des types des expressions te *)
      let lne = List.map (fun (e, _) -> e) nle in (* on récupère la liste des nouvelles expressions ne*)
      (* On vérifie qui l'ordre des types des paramètres effictifs de fonction est compatible avec l'ordre des types des paramètres formelles i.e lors de la déclaration *)
      if est_compatible_list ltp tps then
        (AstType.AppelFonction(ia, lne), tr)
      else
        raise (TypesParametresInattendus (tps, ltp)) (* Renvoie une erreur de appel à la fct par des paramètre incorrectes *)

  | AstTds.Ident ia -> 
    (* on récupere tid le type d'identifiant à partir d'info_ast *)
    let tid = getType ia in
    (AstType.Ident ia, tid) 

  | AstTds.Booleen b ->
    (AstType.Booleen b, Bool)

  | AstTds.Entier i ->
    (AstType.Entier i, Int)
    
  | AstTds.Unaire (op, e) ->
    (* analyse de e pour otenir ne et te*)
    let (ne, te) = analyse_type_expression e in
    (* si te != rat -> erreur *)
    if te = Rat then
      begin
        match op with
        | Numerateur -> (AstType.Unaire(AstType.Numerateur, ne), Int)
        | Denominateur -> (AstType.Unaire(AstType.Denominateur, ne), Int)
      end
    else
      raise (TypeInattendu (te, Rat))

  | AstTds.Binaire (op, e1, e2) ->
    let (ne1, te1) = analyse_type_expression e1 in
    let (ne2, te2) = analyse_type_expression e2 in
    match op, te1, te2 with
    | Plus, Int, Int -> (AstType.Binaire(PlusInt, ne1, ne2), Int)
    | Plus, Rat, Rat -> (AstType.Binaire(PlusRat, ne1, ne2), Rat)
    | Mult, Int, Int -> (AstType.Binaire(MultInt, ne1, ne2), Int)
    | Mult, Rat, Rat -> (AstType.Binaire(MultRat, ne1, ne2), Rat)
    | Equ, Int, Int -> (AstType.Binaire(EquInt, ne1, ne2), Bool)
    | Equ, Bool, Bool -> (AstType.Binaire(EquBool, ne1, ne2), Bool)
    | Fraction, Int, Int -> (AstType.Binaire(Fraction, ne1, ne2), Rat)
    | Inf, Int, Int -> (AstType.Binaire(Inf, ne1, ne2), Bool)
    | _ -> raise (TypeBinaireInattendu (op, te1, te2))
 

(* AstTds.instruction -> AstType.instruction *)
let rec analyse_type_instruction i =
  match i with 
  | AstTds.Declaration (t, info, e) ->
    (* analyse d'expression e pour récupérer la nouvelle expression et son type te *)
    let (ne, te) = analyse_type_expression e in
    modifier_type_variable t info;
    (* Comparaison des deux types t et te *)
    if te = t then
      (* ajout de type t à l'info *)
      AstType.Declaration(info, ne)
    (* Si te != t -> donc erreur *)
    else 
      raise (TypeInattendu (te, t)) (* levé une exception que le type actuelle te ne correspond pas au type attendu t *)

  | AstTds.Affectation (info, e) ->
    (* analyse d'expression e pour récupérer son type te et le nouveau expression ne *)
    let (ne, te) = analyse_type_expression e in
    (* Récupération du type d'identifiant tid de l'info *)
    let tid = getType info in
    (* On vérifie si les deux types sont compatibles par affectation *)
    if est_compatible te tid then
      AstType.Affectation (info, ne)
    else 
      raise (TypeInattendu (te, tid))

  | AstTds.Affichage e ->
    begin
      (* analyse de l'expression e et récuper son type et la nouvelle expréssion *)
      let (ne, te) = analyse_type_expression e in
      (* Résolution de la surcharge de type *)
      match te with
      | Int -> AstType.AffichageInt ne
      | Bool -> AstType.AffichageBool ne
      | Rat -> AstType.AffichageRat ne
      | _ -> failwith "Erreur interne"
    end
    
  | AstTds.Conditionnelle (e, bt, be) ->
    (* analyse de l'expression e pour obtenir ne et te *)
    let (ne, te) = analyse_type_expression e in
    (* L'expession d'une conditionnelle doit être obligatoirement de type booleen *)
    if te = Bool then
      (* analyse de bloc then *)
      let nbt = analyse_type_bloc bt in
      (* analyse de bloc else *)
      let nbe = analyse_type_bloc be in
      AstType.Conditionnelle (ne, nbt, nbe)
    else
      raise (TypeInattendu (te, Bool)) (* levé une exception que le type trouvé n'est pas booléen *)

  | AstTds.TantQue (e, b) ->
    (* analyse d'expression e pour obtenir le type te et la nouvelle expression ne *)
    let (ne, te) = analyse_type_expression e in
    (* analyse de bloc *)
    if te = Bool then
      let nb = analyse_type_bloc b in
      AstType.TantQue (ne, nb)
    else raise (TypeInattendu (te, Bool))

  | AstTds.Retour (e, ia) ->
    (* analyse d'expression e pour obtenir le type te et la nouvelle expression ne *)
    let (ne, te) = analyse_type_expression e in
    (* ontenir le type d'identifiant à partir de l'info *)
    let tid = getType ia in
    if te = tid then
      AstType.Retour(ne, ia)
    else
      raise (TypeInattendu (te, tid)) (* levé une exception dans le cas où type de retour ne pas compatible à type attendu *)

  | AstTds.Empty -> AstType.Empty (* Rien *)

  (* AstTds.instruction list -> AstType.instruction list *)
  and analyse_type_bloc li = List.map analyse_type_instruction li

(* Fonction qui ajoute les types a la liste des info des paramètres *)
let modifier_type_params lp =
  let rec aux l acc =
    match l with
    | [] -> acc
    | (t,i)::q -> (modifier_type_variable t i); aux q (i::acc)
  in aux lp []

(* AstTds.fonction -> AstType.Fonction *)
let analyse_type_fonction (AstTds.Fonction(t, info, lp, li)) =
  (* Ona lp = [(tp1, ip1), ..., (tpn, ipn)] *)
  (* on récupère la liste des types des paramètres *)
  let ltp = List.map (fun (tp, _) -> tp) lp in
  let lip = List.rev (modifier_type_params lp) in
  let nli = analyse_type_bloc li in
  modifier_type_fonction t ltp info;
  AstType.Fonction(info, lip, nli)

(* AstTdsFonction list -> AstType.Fonction list *)
let analyse_type_fonctions lf = List.map analyse_type_fonction lf

(* AstTds.programme -> AstType.programme *)
let analyser (AstTds.Programme (fonctions, prog)) =
  let nfs = analyse_type_fonctions fonctions in
  let np = analyse_type_bloc prog in
  AstType.Programme(nfs, np) 


