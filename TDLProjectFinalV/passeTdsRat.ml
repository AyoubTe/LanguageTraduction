(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)
open Tds
open Exceptions
open Ast

type t1 = Ast.AstSyntax.programme
type t2 = Ast.AstTds.programme


(* analyse_tds_affectable : tds -> bool -> AstSyntax.expression -> AstTds.expression *)
(* Parametre tds : la table des symboles courante *)
(* Une flag qui indique est-ce que l'appel est fait à partir de expression (true) ou instruction (false) car affectable peu générer un opérande gauche d'une affectaion qui peut etre une constante *)
(* Parametre a : l'affextable a analyser *)
(* Verifie la bonne utilisation des identifiants et tranforme l'affectable en un affectable de type AstTds.affectable *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_affectable tds flag a =
  match a with
  | AstSyntax.Deref af -> 
    (* Analyse récursive sur l'affectable *)
    let na = analyse_tds_affectable tds flag af in
    AstTds.Deref na

  | AstSyntax.Ident i ->
    (* Recherche de l'identifiant dans la TDS *)
    begin
      match chercherGlobalement tds i with
      | None -> raise (IdentifiantNonDeclare i) (* L'identifiant n'existe pas *)
      | Some ia ->
        (* Vérification de l'utilisation correcte *)
        match info_ast_to_info ia with
        | InfoVar _ -> AstTds.Ident ia
        | InfoConst _ -> 
            (* L'appel c'est fait a partir d'expression i.e constante est l'opérande gauche d'une affectation ou opérande d'une opération binaire *)
            if flag then
              AstTds.Ident ia
            else 
              raise (MauvaiseUtilisationIdentifiant i)
              
        | _ -> raise (MauvaiseUtilisationIdentifiant i)
    end

(* analyse_tds_expression : tds -> AstSyntax.expression -> AstTds.expression *)
(* Parametre tds : la table des symboles courante *)
(* Parametre e : l'expression a analyser *)
(* Verifie la bonne utilisation des identifiants et tranforme l'expression en une expression de type AstTds.expression *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_expression tds e =
  match e with
  | AstSyntax.AppelFonction(id, le) -> 
      (* Vérification si la fonction est définie globalement *)
      begin
        match chercherGlobalement tds id with
        | None -> raise (MauvaiseUtilisationIdentifiant id)
        | Some ia -> 
            match info_ast_to_info ia with
            | InfoFun _ -> 
                let nle = List.map (analyse_tds_expression tds) le in
                AstTds.AppelFonction(ia, nle)
            | _ -> raise (MauvaiseUtilisationIdentifiant id)
      end
    
  | AstSyntax.Binaire(b, e1, e2) -> 
      let x = analyse_tds_expression tds e1 in
      let y = analyse_tds_expression tds e2 in
      AstTds.Binaire(b, x, y)

  | AstSyntax.Unaire(op, e1) ->
      let x = analyse_tds_expression tds e1 in
      AstTds.Unaire(op, x)

  | AstSyntax.Booleen b -> 
      AstTds.Booleen b

  | AstSyntax.Entier i -> 
      AstTds.Entier i

  | AstSyntax.Null -> 
      AstTds.Null

  | AstSyntax.New t -> 
      AstTds.New t

  | AstSyntax.Adresse n ->
    (* Gestion des références d'identifiants *)
    begin
      match chercherGlobalement tds n with
      | None -> raise (IdentifiantNonDeclare n)
      | Some ia -> 
          match info_ast_to_info ia with
          | InfoVar _ | InfoConst _ -> AstTds.Adresse ia
          | _ -> raise (MauvaiseUtilisationIdentifiant n)
    end

  | AstSyntax.Affectable a ->
      (* Gestion des affectables utilisés comme expressions *)
      let na = analyse_tds_affectable tds true a in
      AstTds.Affectable na


(* analyse_tds_var : tds -> info_ast option -> AstSyntax.var -> AstTds.var *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre var : l'variable statique globale à analyser *)
(* Vérifie la bonne declaration des variables statiques globales et tranforme la variable statique en une variable de type AstTds.var *)
(* Erreur si double declaration d'une variable statique globale *)
let analyse_tds_var tds var =
  let AstSyntax.VarGlobal(t, n, e) = var in
  match chercherLocalement tds n with
  | None -> 
      begin
        let info = InfoVar(n, t, 0, "") in
        let ia = info_to_info_ast info in 
        let ne = analyse_tds_expression tds e in
        ajouter tds n ia;
        AstTds.VarGlobal(t, ia, ne)
      end
  | Some _ -> raise (DoubleDeclaration n)

(* analyse_tds_instruction : tds -> info_ast option -> AstSyntax.instruction -> AstTds.instruction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre oia : None si l'instruction i est dans le bloc principal,
 Some ia où ia est l'information associée à la fonction dans laquelle est l'instruction i sinon *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstTds.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_instruction tds oia i =
  match i with
  | AstSyntax.Declaration (t, n, e) ->
    begin
      match chercherLocalement tds n with
      | None ->
        let ne = analyse_tds_expression tds e in
        let info = InfoVar (n, t, 0, "") in
        let ia = info_to_info_ast info in
        ajouter tds n ia;
        AstTds.Declaration (t, ia, ne)
      | Some _ -> raise (DoubleDeclaration n)
    end

  | VarLStatic (t, n, e) -> 
    begin
    match oia with
    | None -> raise VariableStaticDansMain
    | Some _ -> 
      begin
        match chercherLocalement tds n with
        | None ->
          let info = InfoVarSL(n, t, 0, "", false) in
          let ia = info_to_info_ast info in
          ajouter tds n ia;
          let ne = analyse_tds_expression tds e in
          AstTds.VarLStatic (t, ia, ne)
        
        | Some _ -> raise (DoubleDeclaration n)
      end
    end

  | AstSyntax.Affectation (a, e) ->
    let na = analyse_tds_affectable tds false a  in
    let ne = analyse_tds_expression tds e in
    AstTds.Affectation (na, ne)

  | AstSyntax.Constante (n, v) ->
    begin
      match chercherLocalement tds n with
      | None ->
        ajouter tds n (info_to_info_ast (InfoConst (n, v)));
        AstTds.Empty
      | Some _ -> raise (DoubleDeclaration n)
    end

  | AstSyntax.Affichage e ->
    let ne = analyse_tds_expression tds e in
    AstTds.Affichage (ne)

  | AstSyntax.Conditionnelle (c, t, e) ->
    let nc = analyse_tds_expression tds c in
    let tast = analyse_tds_bloc tds oia t in
    let east = analyse_tds_bloc tds oia e in
    AstTds.Conditionnelle (nc, tast, east)

  | AstSyntax.TantQue (c, b) ->
    let nc = analyse_tds_expression tds c in
    let bast = analyse_tds_bloc tds oia b in
    AstTds.TantQue (nc, bast)

  | AstSyntax.Retour (e) ->
    begin
      match oia with
      | None -> raise RetourDansMain
      | Some ia ->
        let ne = analyse_tds_expression tds e in
        AstTds.Retour (ne, ia)
    end

  (* analyse_tds_bloc : tds -> info_ast option -> AstSyntax.bloc -> AstTds.bloc *)
  (* Paramètre tds : la table des symboles courante *)
  (* Paramètre oia : None si le bloc li est dans le programme principal,
  Some ia où ia est l'information associée à la fonction dans laquelle est le bloc li sinon *)
  (* Paramètre li : liste d'instructions à analyser *)
  (* Vérifie la bonne utilisation des identifiants et tranforme le bloc en un bloc de type AstTds.bloc *)
  (* Erreur si mauvaise utilisation des identifiants *)
  and analyse_tds_bloc tds oia li =
    (* Entrée dans un nouveau bloc, donc création d'une nouvelle tds locale pointant sur la table du bloc parent *)
    let tdsbloc = creerTDSFille tds in
    (* Analyse des instructions du bloc avec la tds du nouveau bloc.
    Cette tds est modifiée par effet de bord *)
    let nli = List.map (analyse_tds_instruction tdsbloc oia) li in
    nli (* afficher_locale tdsbloc ; *) (* décommenter pour afficher la table locale *)


(* Fonction qui analyse les expressions des valeurs par defaut d'une *)
let analyse_valeur_defaut tds e =
  match e with
  | None -> None
  | Some v -> let nv = analyse_tds_expression tds v in  Some nv

(* Fonction qui insere les infos des parametres dans la tds de fonction et renvoie typ * info_ast pour construire la liste typ * info_ast * expression option list neccessaire a la creation de noueud de la fonction dans l'arbre de synthaxe *)
let listeTIPrams tds (tp, np, e) =
  match chercherLocalement tds np with
  | None ->
    let ne = analyse_valeur_defaut tds e in
    let infop = InfoVar (np, tp, 0, "") in
    let iap = info_to_info_ast infop in
    ajouter tds np iap;
    (tp, iap, ne)
  | Some _ -> raise (DoubleDeclaration np)

(* analyse_tds_fonction : tds -> AstSyntax.fonction -> AstTds.fonction *)
(* Parametre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_tds_fonction maintds (AstSyntax.Fonction (t, n, lp, li)) =
  let tdsfonction = creerTDSFille maintds in (* Creation d'une nouvelle Tds a la declaration de la fonction *)
  match chercherGlobalement maintds n with (* On verifie que la fonction n'est deja definie *)
  | None -> (* Non la fonction j'amais été déclarée *)
  let l = List.map (fun (t, _, e) -> 
    match e with
      | None -> (t, false) (*On indique que le paramètre n'a pas une valeur par défaut *)
      | Some _ -> (t, true) (* On indique le paramètre admet une valeur par defaut *)                          
    ) lp in 

    let info = InfoFun (n, t, l) in (* Creation d'une nouvelle info *)
    let iaf = info_to_info_ast info in (* Transformer l'info de la fonction en une info_ast *)
    ajouter maintds n iaf; (* Ajouter la fonction a la table des symboles *)
    let nlp = List.map (listeTIPrams tdsfonction) lp in (* On ajoute la liste des parametres a la Tds *)
    let nli = analyse_tds_bloc tdsfonction (Some iaf) li in (* Analyse de bloc *)
    AstTds.Fonction (t, iaf, nlp, nli)

  | Some info -> (* Oui : fonction deja definie *)
    match info_ast_to_info info with
    | InfoFun _ -> raise (DoubleDeclaration n)
    | _ -> raise (MauvaiseUtilisationIdentifiant n)

(* analyser : AstSyntax.programme -> AstTds.programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme en un programme de type AstTds.programme *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstSyntax.Programme (vars, fonctions, prog)) =
  let tds = creerTDSMere () in
  let nvars = List.map (analyse_tds_var tds) vars in
  let nfs = List.map (analyse_tds_fonction tds) fonctions in
  let nb = analyse_tds_bloc tds None prog in
  AstTds.Programme (nvars, nfs, nb)