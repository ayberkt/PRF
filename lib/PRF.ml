(* open Core.List;; *)
open Core.In_channel;;
open Core.Printf;;
open AbsPRF;;

type prf_exp =
   Zero
 | Succ
 | Proj of int
 | Comp of prf_exp * (prf_exp list)
 | Rec of prf_exp * prf_exp

type prfi_exp = prf_exp * int list

(* matches_arity : PRF -> int -> bool *)
(* matches_arity zero 0 = true *)
(* matches_arity zero _ = false *)
(* matches_arity (suc _) 1 = true *)
(* matches_arity (suc _) _ = true *)
(* matches_arity (proj i) n = 0 <= i && i < n *)

exception Undefined

let rec index : 'a list -> int -> 'a =
  fun xs n ->
    match (xs, n) with
    | x::_, 0 -> x
    | _::xs, n -> index xs (n-1)
    | _ -> raise Undefined

let rec natrec (n : int) (z : 'a) (s : int -> 'a -> 'a) : 'a =
  match n, z, s with
  | 0, z, _ -> z
  | n, z, s -> s (n-1) (natrec (n-1) z s)

let rec eval (p : prf_exp) (arg : int list) : int =
  match p, arg with
  | Zero, [] -> 0
  | Succ, n::[] -> 1 + n
  | Proj i, rho -> index rho i
  | Comp (f, gs), rho -> eval f (List.map (fun x -> eval x rho) gs)
  | Rec (f, g), n::rho -> natrec n (eval f rho) (fun n r -> eval g (r::n::rho))
  | _ -> raise Undefined

let rec to_prf_exp : sPRFExp -> prf_exp =
  function
  | Zero -> Zero
  | Succ -> Succ
  | Proj x -> Proj x
  | Comp (f, gs) -> Comp (to_prf_exp f, List.map to_prf_exp (to_list gs))
  | Rec (f, g) -> Rec (to_prf_exp f, to_prf_exp g)
and to_list : sPRFExpList -> sPRFExp list =
  function
  | SPRFExpNil -> []
  | SPRFExpCons (f, gs) -> f::(to_list gs)

let rec vec_to_list : vector -> int list =
  function
  | Nil -> []
  | Cons (xs, x) -> x :: vec_to_list xs

let run (_ : string) : int = 0

let main () =
  let MkPRFI (sprf, args) = ParPRF.pPRFIExp LexPRF.token (Lexing.from_channel stdin) in
  let prf  = to_prf_exp sprf in
  printf "%d\n" (eval prf (vec_to_list args));;

(* The predecessor function. *)
let pred = Rec (Zero, Proj 1)
