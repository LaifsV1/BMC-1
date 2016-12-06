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
type value = Unit | Int of int | Method of var | Ref of var 
             | Var of var * tp  | Pair of value * value
let rec string_of_value (v : value) :(string) =
  match v with
  | Int i -> string_of_int i
  | Method x -> x
  | Ref x -> x
  | Pair(x,y) -> sprintf "(%s , %s)" (string_of_value x) (string_of_value y)
  | Unit -> "skip"
  | Var (x,y) -> x

(* Canonical Form *)
type canon = Let of value * canon * canon             (* let (x:tau) = C in C *)
           | Lambda of value * (value * canon) * canon(* let x = \x.C in C *)
           | Apply of value * value                   (* v v *)
           | BinOp of value * value * binop           (* v (+) v *)
           | Assign of value * value                  (* v := v *)
           | Deref of value                           (* ! v *)
           | Pi1 of value                             (* pi1 (v,v) *)
           | Pi2 of value                             (* pi2 (v,v) *)
           | Val of value                             (* v *)
           | If of value * canon * canon              (* if v then C else C *)
           | Fail                                     (* fail *)
let rec string_of_canon = function
  | Let(v,c1,c2) -> sprintf "let %s = (%s) in (%s)"
                            (string_of_value v) 
                            (string_of_canon c1) 
                            (string_of_canon c2)
  | Lambda(f,(x,c1),c2) -> sprintf "let %s = (fun %s.%s) in (%s)"
                                   (string_of_value f) (string_of_value x)
                                   (string_of_canon c1) (string_of_canon c2)
  | Apply(v1,v2) -> sprintf "%s %s" (string_of_value v1) (string_of_value v2)
  | BinOp(v1,v2,op) -> let x1 = string_of_value v1 in
                       let x2 = string_of_value v2 in
                       x1^op^x2
  | Assign(v1,v2) -> sprintf "%s := %s" 
                             (string_of_value v1) 
                             (string_of_value v2)
  | Deref(v) -> sprintf "!%s" (string_of_value v)
  | Pi1(v) -> sprintf "Pi1(%s)" (string_of_value v)
  | Pi2(v) -> sprintf "Pi2(%s)" (string_of_value v)
  | Val(v) -> sprintf "%s" (string_of_value v)
  | If(v,c1,c2) -> sprintf "if %s then (%s) else (%s)"
                            (string_of_value v) 
                            (string_of_canon c1) 
                            (string_of_canon c2)
  | Fail -> "fail"

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
let repo_get map key = 
  try Repo.find key map
  with Not_found ->
    failwith (sprintf "***[error] : method '%s' not in repo." 
                      (string_of_value key))
let repo_update map key record = Repo.add key record map

type repo  = (value * canon * tp) Repo.t
let empty_repo :(repo) = Repo.empty

(* partial map, references to int *)
(* counter maps r to its assignments seen so far; i.e. if none, then zero *)
module Counter = Map.Make(String)
let c_get     map key = try Counter.find key map with Not_found -> 0
let c_update  map key = Counter.add key ((c_get map key)+1) map
let ref_get   map key = sprintf "_%s%s_" key (string_of_int (c_get map key))
let d_update  map key new_val = Counter.add key new_val map
let string_of_ref key value   = sprintf "_%s%s_" key (string_of_int value)
type counter = int Counter.t
let empty_counter :(counter) = Counter.empty
