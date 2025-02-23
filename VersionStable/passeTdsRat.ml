(* Module de la passe de gestion des identifiants *)
(* doit être conforme à l'interface Passe *)
open Tds
open Exceptions
open Ast

type t1 = Ast.AstSyntax.programme
type t2 = Ast.AstTds.programme

(* analyse_tds_expression : tds -> AstSyntax.expression -> AstTds.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'expression
en une expression de type AstTds.expression *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_expression tds e =
  match e with
  | AstSyntax.AppelFonction(id, le) -> 
    begin
      (* On vérifie si la fonction est déja definie ou pas *)
      match chercherGlobalement tds id with
      | None -> raise (MauvaiseUtilisationIdentifiant id)
      | Some ia -> 
        begin
          match info_ast_to_info ia with
          | InfoConst _ | InfoVar _ -> raise (MauvaiseUtilisationIdentifiant id)
          | InfoFun _ -> let nle = List.map (analyse_tds_expression tds) le in
                        AstTds.AppelFonction(ia, nle)
        end
    end

  | AstSyntax.Ident n -> 
    begin
    match chercherGlobalement tds n with
    | None -> raise (IdentifiantNonDeclare n)
    | Some ia -> 
      begin
        match info_ast_to_info ia with
        | InfoConst (_,v) -> (AstTds.Entier v)
        | InfoVar _ -> AstTds.Ident ia
        | InfoFun _ -> raise (MauvaiseUtilisationIdentifiant n)
      end 
    end

  | AstSyntax.Binaire(b, e1, e2) -> 
    let x = analyse_tds_expression tds e1 in
    let y = analyse_tds_expression tds e2 in
    AstTds.Binaire (b, x, y) 
 
  | AstSyntax.Unaire(op, e1) ->
    let x = analyse_tds_expression tds e1 in
    AstTds.Unaire (op, x)

  | AstSyntax.Booleen b -> 
    AstTds.Booleen b

  | AstSyntax.Entier i -> 
    AstTds.Entier i


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
        (* L'identifiant n'est pas trouvé dans la tds locale, il n'a donc pas été déclaré dans le bloc courant *)
        (* Vérification de la bonne utilisation des identifiants dans l'expression *)
        let ne = analyse_tds_expression tds e in (* et obtention de l'expression transformée *)
        (* Création de l'information associée à l'identfiant *)
        let info = InfoVar (n,Undefined, 0, "") in
        (* Création du pointeur sur l'information *)
        let ia = info_to_info_ast info in
        (* Ajout de l'information (pointeur) dans la tds *)
        ajouter tds n ia;
        (* Renvoie de la nouvelle déclaration où le nom a été remplacé par l'information et l'expression remplacée par l'expression issue de l'analyse *)
        AstTds.Declaration (t, ia, ne)
      | Some _ ->(* L'identifiant est trouvé dans la tds locale, il a donc déjà été déclaré dans le bloc courant *)
        raise (DoubleDeclaration n)
    end

  | AstSyntax.Affectation (n,e) ->
    begin
      match chercherGlobalement tds n with
      | None ->
        raise (IdentifiantNonDeclare n) (* L'identifiant n'est pas trouvé dans la tds globale. *)
      | Some info ->
        (* L'identifiant est trouvé dans la tds globale,
        il a donc déjà été déclaré. L'information associée est récupérée. *)
        begin
          match info_ast_to_info info with
          | InfoVar _ ->
            (* Vérification de la bonne utilisation des identifiants dans l'expression *)
            (* et obtention de l'expression transformée *)
            let ne = analyse_tds_expression tds e in
            (* Renvoie de la nouvelle affectation où le nom a été remplacé par l'information et l'expression remplacée par l'expression issue de l'analyse *)
            AstTds.Affectation (info, ne)
          | _ ->
            raise (MauvaiseUtilisationIdentifiant n) (* Modification d'une constante ou d'une fonction *)
        end
    end

  | AstSyntax.Constante (n,v) ->
    begin
    match chercherLocalement tds n with
    | None ->
      (* L'identifiant n'est pas trouvé dans la tds locale, il n'a donc pas été déclaré dans le bloc courant *)
      ajouter tds n (info_to_info_ast (InfoConst (n,v))); (* Ajout dans la tds de la constante *)
      AstTds.Empty (* Suppression du noeud de déclaration des constantes, i.e le noeud est devenu inutile *)
    | Some _ ->
      (* L'identifiant est trouvé dans la tds locale, il a donc déjà été déclaré dans le bloc courant *)
      raise (DoubleDeclaration n)
    end
  
  | AstSyntax.Affichage e ->
    (* Vérification de la bonne utilisation des identifiants dans l'expression et obtention de l'expression transformée *)
    let ne = analyse_tds_expression tds e in
    (* Renvoie du nouvel affichage où l'expression remplacée par l'expression issue de l'analyse *)
    AstTds.Affichage (ne)

  | AstSyntax.Conditionnelle (c,t,e) ->
    let nc = analyse_tds_expression tds c in (* Analyse de la condition *) 
    let tast = analyse_tds_bloc tds oia t in (* Analyse du bloc then *)
    let east = analyse_tds_bloc tds oia e in (* Analyse du bloc else *)
    AstTds.Conditionnelle (nc, tast, east) (* Renvoie la nouvelle structure de la conditionnelle *)

  | AstSyntax.TantQue (c,b) ->
    let nc = analyse_tds_expression tds c in (* Analyse de la condition *)
    let bast = analyse_tds_bloc tds oia b in (* Analyse du bloc *)
    AstTds.TantQue (nc, bast) (* Renvoie la nouvelle structure de la boucle *)

  | AstSyntax.Retour (e) ->
    begin
      (* On récupère l'information associée à la fonction à laquelle le return est associée *)
      match oia with
      (* Il n'y a pas d'information -> l'instruction est dans le bloc principal : erreur *)
      | None -> raise RetourDansMain
      (* Il y a une information -> l'instruction est dans une fonction *)
      | Some ia ->
        let ne = analyse_tds_expression tds e in (* Analyse de l'expression *)
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

(*Fonction pour avoir le type des élements d'une liste de paramètres*)
let rec getType lp acc =
 match lp with
 | [] -> acc
 | (typ, _)::q -> getType q (typ::acc) 

 (* Fonction qui renvoie la liste de*)
let listeTIPrams tds (tp, np) =
  match chercherLocalement tds np with
  | None ->
    let infop = InfoVar (np, tp, 0, "") in
    let iap = info_to_info_ast infop in
    ajouter tds np iap;
    (tp, iap)
  | Some _ -> raise (DoubleDeclaration np)

(* analyse_tds_fonction : tds -> AstSyntax.fonction -> AstTds.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_tds_fonction maintds (AstSyntax.Fonction (t, n, lp, li)) =
  let tdsfonction = creerTDSFille maintds in
  match chercherGlobalement maintds n with
  | None ->
    let ltp = List.rev (getType lp []) in
    let info = InfoFun (n, t, ltp) in
    let iainfo = info_to_info_ast info in
    ajouter maintds n iainfo;
    let nlp = List.map (listeTIPrams tdsfonction) lp in
    let nli = analyse_tds_bloc tdsfonction (Some iainfo) li in
    AstTds.Fonction (t, iainfo, nlp, nli)
  | Some info ->
    match info_ast_to_info info with
    | InfoFun _ -> raise (DoubleDeclaration n)
    | InfoConst _-> raise (MauvaiseUtilisationIdentifiant n)
    | InfoVar _ -> raise (MauvaiseUtilisationIdentifiant n)

(* analyser : AstSyntax.programme -> AstTds.programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme
en un programme de type AstTds.programme *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstSyntax.Programme (fonctions,prog)) =
 let tds = creerTDSMere () in
 let nf = List.map (analyse_tds_fonction tds) fonctions in
 let nb = analyse_tds_bloc tds None prog in
 AstTds.Programme (nf,nb)