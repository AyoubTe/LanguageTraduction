type typ = Bool | Int | Rat | Undefined | Pointeur of typ

let string_of_type t = 
  match t with
  | Bool ->  "Bool"
  | Int  ->  "Int"
  | Rat  ->  "Rat"
  | Pointeur _ -> "Pointeur"
  | Undefined -> "Undefined"


  let rec est_compatible (t1, vpd) t2 =
    if vpd then
      true
    else 
      match t1, t2 with
      | Bool, Bool -> true
      | Int, Int -> true
      | Rat, Rat -> true
  
      (* Autoriser : null -> n'importe quel pointeur *)
      | Pointeur Undefined, Pointeur _ -> true
  
      (* Déjà existant, mais dans l'autre sens *)
      | Pointeur _, Pointeur Undefined -> true
  
      | Pointeur tp1, Pointeur tp2 -> est_compatible (tp1, false) tp2
      | _ -> false
  
  

let%test _ = est_compatible (Bool, false) Bool
let%test _ = est_compatible (Int, false) Int
let%test _ = est_compatible (Rat, false) Rat
let%test _ = not (est_compatible (Int, false) Bool)
let%test _ = not (est_compatible (Bool, false) Int)
let%test _ = not (est_compatible (Int, false) Rat)
let%test _ = not (est_compatible (Rat, false) Int)
let%test _ = not (est_compatible (Bool, false) Rat)
let%test _ = not (est_compatible (Rat, false) Bool)
let%test _ = not (est_compatible (Undefined, false) Int)
let%test _ = not (est_compatible (Int, false) Undefined)
let%test _ = not (est_compatible (Rat, false) Undefined)
let%test _ = not (est_compatible (Bool, false) Undefined)
let%test _ = not (est_compatible (Undefined, false) Int)
let%test _ = not (est_compatible (Undefined, false) Rat)
let%test _ = not (est_compatible (Undefined, false) Bool)


(* est_compatible_list : typ * bool list -> typ list -> bool : <fun> *)
let rec est_compatible_list lt1 lt2 =
 match lt1, lt2 with
 | [], [] -> true (* On suppose que a chaque fois les parametres avec valeur par defaut se trouve a la fin *)
 | (_, b)::_, [] -> if b then true else false
 | [], _ -> false
 | t1::q1, t2::q2 -> if est_compatible t1 t2 then (est_compatible_list q1 q2) else false

let%test _ = est_compatible_list [] []
let%test _ = est_compatible_list [(Int, false) ; (Rat, false)] [Int ; Rat]
let%test _ = est_compatible_list [(Bool, false) ; (Rat, false) ; (Bool, true)] [Bool ; Rat ; Bool]
let%test _ = not (est_compatible_list [(Int, false)] [Int ; Rat])
let%test _ = not (est_compatible_list [(Int, false)] [Rat ; Int])
let%test _ = not (est_compatible_list [(Int, false) ; (Rat, true)] [Rat ; Int])
let%test _ = not (est_compatible_list [(Bool, false) ; (Rat, false) ; (Bool, false)] [Bool ; Rat ; Bool ; Int])

let getTaille t =
  match t with
  | Int -> 1
  | Bool -> 1
  | Rat -> 2
  | Undefined -> 0
  | Pointeur _ -> 1  
  
let%test _ = getTaille Int = 1
let%test _ = getTaille Bool = 1
let%test _ = getTaille Rat = 2

