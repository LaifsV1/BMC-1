(*author: Yu-Yang Lin, date: 21/11/2016*)
open Format

type var = string        (* Variables *)
type phi = string        (* Formulas *)
type binop = string      (* Binary Operations *)

(* Natural Numbers *)
type nat = Nil | Suc of nat
let rec nat_of_int (i : int) :(nat) =
  match i > 0 with
  | true -> Suc(nat_of_int (i-1))
  | false -> Nil

(* Values *)
type value = Unit | Int of int | Method of var | Ref of var | Var of var | Pair of value * value
let rec string_of_value (v : value) :(string) =
  match v with
  | Int i -> string_of_int i
  | Method x -> x
  | Ref x -> x
  | Pair(x,y) -> sprintf "(%s , %s)" (string_of_value x) (string_of_value y)
  | Unit -> "()"
  | Var x -> x

(* Canonical Form *)
type canon = Let of var * canon * canon                    (* let x = C in C *)
           | Lambda of var * (var * canon) * canon         (* let x = \x.C in C *)
           | Apply of value * value                        (* v v *)
           | BinOp of value * value * binop                (* v (+) v *)
           | Assign of value * value                       (* v := v *)
           | Deref of value                                (* ! v *)
           | Pi1 of value                                  (* pi1 (v,v) *)
           | Pi2 of value                                  (* pi2 (v,v) *)
           | Val of value                                  (* v *)
           | If of value * canon * canon                   (* if v then C else C *)
           | Fail                                          (* fail *)

(*********************)
(* Method Repository *)
(*********************)
(* partial map, method names to functions *)
type repo = (value * (var * canon)) list
let rec get_method (r : repo) (v : value) =
  match r with
  | [] -> failwith (sprintf "***[error] : method '%s' not in repo.***" (string_of_value v))
  | (m,(x,c))::xs -> if m=v then (x,c) else get_method xs v

(*******************)
(* Reference Store *)
(*******************)
(* partial map, references to values *)
type store = (value * value) list
let rec get_state (r : store) (v : value) =
  match r with
  | [] -> failwith (sprintf "***[error] : variable '%s' not in store.***" (string_of_value v))
  | (v1,v2)::xs -> if v1=v then v2 else get_state xs v

(**********************)
(* Variables Assigned *)
(**********************)
(* list of variables assigned so far; all should be unique *)
type names = var list
let uplus n1 n2 n3 = n1@n2
(* (**for testing only**)
let rec uplus n1 n2 acc =
  match n1 with
  | [] -> acc@n2
  | (x::xs) -> (if List.mem x n2
                then failwith (sprintf "***[error] : variable '%s' in N1 exists in N2.***" x)
                else uplus xs n2 (acc@[x])) *)

let rec string_of_names = function
  | [] -> ""
  | (x::xs) -> sprintf "%s;\n %s" x (string_of_names xs)
