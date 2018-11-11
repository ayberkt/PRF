(* open Core.Printf;; *)
(* open Core.List;; *)

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

(* The predecessor function. *)
let pred = Rec (Zero, Proj 1)
