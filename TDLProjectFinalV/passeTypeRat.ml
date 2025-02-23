
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
  (*         string * typ * (typ * bool) list *)
  | InfoFun (_, tr, lp) -> (tr, lp)
  | _ -> failwith "info ne concerne pas une fonction"

(* Fonction qui renvoie le type à partir de l'information *)
let getTypeInfo info =
  match info with 
  | InfoConst _ -> Int
  | InfoVar (_, t, _, _) -> t
  | InfoFun (_,tr, _) -> tr

(* analyse_type_affectable : Foction qui verifie que l'affetable respecte les règles de typage *)
(* analyse_type_affectable : AstTds.affectable -> AstType.affectable * typ : <fun> *)
let rec analyse_type_affectable a =
  match a with
  | AstTds.Ident ia -> 
      let tid = getTypeInfo (info_ast_to_info ia) in
      (AstType.Ident ia, tid)
  
  | AstTds.Deref af ->
      let (naf, taf) = analyse_type_affectable af in
      match taf with
      | Pointeur t -> (AstType.Deref (naf, taf), t)
      | _ -> raise (TypeInattendu (taf, Pointeur Undefined))


(* analyse_tds_expression : AstTds.expression -> (AstType.expression, typ) *)
let rec analyse_type_expression e =
  match e with
  | AstTds.AppelFonction (ia, le) ->
      begin
        let (tr, lp) = getInfoFct (info_ast_to_info ia) in
        let nle = List.map analyse_type_expression le in
        let tpes = List.map snd nle in
        let lne = List.map fst nle in
        (* lp = [(t0, b0), ..., (tn, bn)] les b0, .., bn indiquent c'est-ce que le paramètre admet une valeur par défaut au non*)
        if est_compatible_list lp tpes then
          (AstType.AppelFonction(ia, lne), tr)
        else
          raise (TypesParametresInattendus (tpes, (List.map (fun (t, _) -> t) lp)))
      end

  | AstTds.Adresse ia -> 
    begin
      let tid = getTypeInfo (info_ast_to_info ia) in
      (AstType.Adresse ia, Pointeur tid)
    end

  | AstTds.Booleen b -> 
      (AstType.Booleen b, Bool)

  | AstTds.Entier i -> 
      (AstType.Entier i, Int)

  | AstTds.Unaire (op, e) ->
      begin
        let (ne, te) = analyse_type_expression e in
        if te = Rat then
          match op with
          | Numerateur -> (AstType.Unaire(AstType.Numerateur, ne), Int)
          | Denominateur -> (AstType.Unaire(AstType.Denominateur, ne), Int)
        else
          raise (TypeInattendu (te, Rat))
      end

  | AstTds.Binaire (op, e1, e2) ->
      begin
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
      end

  | AstTds.Null -> 
      (AstType.Null, Pointeur Undefined)

  | AstTds.New t -> 
      (AstType.New t, Pointeur t)

  | AstTds.Affectable a -> 
    let (na, ta) = analyse_type_affectable a in
    (AstType.Affectable na, ta)

(* La fonction qui verifie que la déclaration d'une variable globale respste le typage *)
(* val : aanalyse_type_var : AsTds.var -> AstType.var *)
let analyse_type_var v =
  match v with
  | AstTds.VarGlobal(t, ia, e) ->
    let (ne, te) = analyse_type_expression e in
    if not (est_compatible (t, false) te) then
      raise (TypeInattendu(te, t))
    else
      modifier_type_variable t ia;
      AstType.VarGlobal(ia, ne)

(* AstTds.instruction -> AstType.instruction *)
let rec analyse_type_instruction i =
  match i with 
  | AstTds.Declaration (t, info, e) ->
    (* Analyse de l'expression `e` pour obtenir son type `te` et la nouvelle expression `ne` *)
    let (ne, te) = analyse_type_expression e in
    modifier_type_variable t info; (* Mise à jour du type dans l'information *)
    (* Comparaison des types pour la déclaration *)
    if (est_compatible (t, false) te) then
      AstType.Declaration(info, ne)
    else
      raise (TypeInattendu (te, t)) (* Erreur si les types ne correspondent pas *)

  | AstTds.VarLStatic (t, info, e) ->
    (* Analyse de l'expression `e` pour obtenir son type `te` et la nouvelle expression `ne` *)
    let (ne, te) = analyse_type_expression e in
    modifier_type_variable t info; (* Mise à jour du type dans l'information *)
    (* Comparaison des types pour la déclaration *)
    if te = t then
      AstType.VarLStatic(info, ne)
    else
      raise (TypeInattendu (te, t)) (* Erreur si les types ne correspondent pas *)

  | AstTds.Affectation (a, e) ->
    (* Analyse de l'affectable `a` et de l'expression `e` *)
    let (na, ta) = analyse_type_affectable a in
    let (ne, te) = analyse_type_expression e in
    (* Vérifie la compatibilité des types pour l'affectation *)
    if est_compatible (te, false) ta then
      AstType.Affectation(na, ne)
    else
      raise (TypeInattendu (te, ta))

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
    let tid = getTypeInfo (info_ast_to_info ia) in
    if te = tid then
      AstType.Retour(ne, ia)
    else
      raise (TypeInattendu (te, tid)) (* levé une exception dans le cas où type de retour ne pas compatible à type attendu *)

  | AstTds.Empty -> AstType.Empty (* Rien *)

  (* AstTds.instruction list -> AstType.instruction list *)
  and analyse_type_bloc li = List.map analyse_type_instruction li


(* Fonction pour traiter les cas des paramètres avec valeur par defaut *)
let analyse_type_exp_opt e i =
  match e with 
  | None -> None
  | Some v ->
    let (ne, t) = analyse_type_expression v in
    let tid = getTypeInfo (info_ast_to_info i) in
    if est_compatible (t, false) tid then
      Some ne
    else
      raise (TypeInattendu (t, tid))

(* Fonction qui ajoute les types a la liste des info des paramètres *)
let modifier_type_params lp =
  List.fold_right 
    (fun (t, i, e) acc -> 
      modifier_type_variable t i;
      (i, (analyse_type_exp_opt e i)) :: acc
    ) lp []


(* AstTds.fonction -> AstType.Fonction *)
let analyse_type_fonction (AstTds.Fonction(t, info, lp, li)) =
  (* Ona lp = [(tp1, ip1, e1), ..., (tpn, ipn, en)] avec e1,.. en sont de type expression option*)
  (* on récupère la liste des types des paramètres *)
  let l = List.map (fun (t, _, e) -> 
    match e with
    | None -> (t, false) (*On indique que le paramètre n'a pas une valeur par défaut *)
    | Some _ -> (t, true) (* On indique le paramètre admet une valeur par defaut *)                          
  ) lp in 
  
  (* Recuperer la nouvelle liste des parametres *)
  let lip = List.rev (modifier_type_params lp) in
  
  let nli = analyse_type_bloc li in
  modifier_type_fonction t l info;
  AstType.Fonction(info, lip, nli)

(* AstTdsFonction list -> AstType.Fonction list *)
let analyse_type_fonctions lf = List.map analyse_type_fonction lf

(* AstTds.programme -> AstType.programme *)
let analyser (AstTds.Programme (vars, fonctions, prog)) =
  let nvs = List.map analyse_type_var vars in
  let nfs = analyse_type_fonctions fonctions in
  let np = analyse_type_bloc prog in
  AstType.Programme(nvs, nfs, np) 

