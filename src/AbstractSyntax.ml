(*author: Yu-Yang Lin, date: 21/11/2016*)
open Format

type var = string        (* Variables *)
type binop = string      (* Binary Operations *)

(* Natural Numbers *)
type nat = Nil | Suc of nat
let rec nat_of_int (i : int) :(nat) =
  match i > 0 with
  | true -> Suc(nat_of_int (i-1))
  | false -> Nil

(* Types *)
type tp = Command | Integer | Product of tp * tp | Arrow of tp * tp

(* Values *)
type value = Unit | Int of int | Method of var | Ref of var | Var of var * tp  | Pair of value * value
let rec string_of_value (v : value) :(string) =
  match v with
  | Int i -> string_of_int i
  | Method x -> x
  | Ref x -> x
  | Pair(x,y) -> sprintf "(%s , %s)" (string_of_value x) (string_of_value y)
  | Unit -> "skip"
  | Var (x,y) -> x

(* Canonical Form *)
type canon = Let of value * canon * canon                 (* let (x : tau) = C in C *)
           | Lambda of value * (value * canon) * canon    (* let x = \x.C in C *)
           | Apply of value * value                       (* v v *)
           | BinOp of value * value * binop               (* v (+) v *)
           | Assign of value * value                      (* v := v *)
           | Deref of value                               (* ! v *)
           | Pi1 of value                                 (* pi1 (v,v) *)
           | Pi2 of value                                 (* pi2 (v,v) *)
           | Val of value                                 (* v *)
           | If of value * canon * canon                  (* if v then C else C *)
           | Fail                                         (* fail *)

(* CNF *)
type clause = Eq of var * var     (* x=x' *)
            | Neq of var * var    (* x=/=x' *)
type cnf_elem = Clause of clause              (* x=x' *)
              | Implies of clause * clause    (* (v=v') => (x=x') *)
type cnf = cnf_elem list                      (* conjunctive normal form *)

let cnf_fail = "CNF_FAIL"
let cnf_nil  = "CNF_NIL"

let (===) v1 v2 = Clause(Eq(v1,v2))
let (=/=) v1 v2 = Clause(Neq(v1,v2))
let (==>) v1 v2 =
  match v1,v2 with
  | Clause a, Clause b -> Implies(a,b)
  | _ -> failwith "***[error] : tried to build CNF with nested implications."

(*******************************************)
(* Method Repository and Reference Counter *)
(*******************************************)
(* partial map, method names to functions *)
module Repo = Map.Make(struct type t = value let compare = compare end)
let get    map key        = Repo.find key map
let update map key record = Repo.add key record map

type repo  = (value * canon * tp) Repo.t
let empty_repo :(repo) = Repo.empty

(* partial map, references to int *)
(* counter maps r to its assignments seen so far; i.e. if none, then zero *)
module Counter = Map.Make(String)
let cget map key = try Counter.find key map with Not_found -> 0
let cupdate map key =  Counter.add key ((cget map key)+1) map
let cmerge  m1  m2  =
  Counter.merge (fun key v1 v2 ->
                  match v1,v2 with
                  | Some a, None -> Some a
                  | None, Some b -> Some b
                  | _ -> failwith "***[error] : duplicate in the ref counters."
                ) m1 m2
let rcget map key = sprintf "_%s_%s_" key (string_of_int (cget map key))

type counter = int Counter.t
let empty_counter :(counter) = Counter.empty
