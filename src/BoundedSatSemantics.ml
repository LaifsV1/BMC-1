(*author: Yu-Yang Lin, date: 21/11/2016*)
open AbstractSyntax
open Format

(*******************)
(* Fresh Variables *)
(*******************)
let var_x = ref 0
let var_r = ref 0
let var_m = ref 0
let return = ref 0
let fresh_x () = var_x := !var_x + 1; "_x_" ^ string_of_int (!var_x) ^ "_" (*format: _x_int_*)
let fresh_r () = var_r := !var_r + 1; "_r_" ^ string_of_int (!var_r) ^ "_" (*format: _r_int_*)
let fresh_m () = var_m := !var_m + 1; "_m_" ^ string_of_int (!var_m) ^ "_" (*format: _m_int_*)
let fresh_ret () = return := !return + 1; "_ret_" ^ string_of_int (!return) ^ "_" (*format: _ret_int_*)

(**********************)
(* Substitute: v{a/b} *)
(**********************)
let rec subs_pair (v : value) (a : value) (b : value) =
  match v with
  | Pair(v1,v2) -> Pair(subs_pair v1 a b, subs_pair v2 a b)
  | v -> if v=b then a else v

let rec subs (m : canon) (a : value) (b : value) =
  match m with
  | Let(x,c1,c2) -> if Var(x)=b then m else Let(x,(subs c1 a b),(subs c2 a b))
  | Lambda(f,(x,c1),c2) -> if Var(f)=b then m
                           else (if Var(x)=b
                                 then Lambda(f,(x,c1),subs c2 a b)
                                 else Lambda(f,(x,subs c1 a b),subs c2 a b))
  | Apply(v1,v2) -> (match (v1=b,v2=b) with
                     | true,true -> Apply(a,a)
                     | true,false -> Apply(a,v2)
                     | false,true -> Apply(v1,a)
                     | false,false -> Apply(v1,v2)
                    )
  | BinOp(v1,v2,op) -> (match (v1=b,v2=b) with
                        | true,true -> BinOp(a,a,op)
                        | true,false -> BinOp(a,v2,op)
                        | false,true -> BinOp(v1,a,op)
                        | false,false -> BinOp(v1,v2,op)
                    )
  | Assign(v1,v2) -> (match (v1=b,v2=b) with
                      | true,true -> Assign(a,a)
                      | true,false -> Assign(a,v2)
                      | false,true -> Assign(v1,a)
                      | false,false -> Assign(v1,v2)
                     )
  | Deref(v) -> if v=b then Deref(a) else m
  | Pi1(v) -> Pi1(subs_pair v a b)
  | Pi2(v) -> Pi2(subs_pair v a b)
  | Val(v) -> if v=b then Val(a) else m
  | If(v,c1,c0) -> let sc1,sc0 = subs c1 a b, subs c0 a b in
                   if v=b then If(a,sc1,sc0) else If(v,sc1,sc0)
  | Fail -> Fail

(*************************)
(* Bounded SAT Semantics *)
(*************************)
let rec sat (m : canon) (r : repo) (s : store) (k : nat) :(var * phi list * names) =
  let ret = fresh_ret () in
  match (k,m) with
  | Nil,_ -> (ret,[sprintf "(%s=false)" ret],ret::[])
  | k,Let(x,c1,c2) -> let x' = fresh_x () in
                      let (x1,phi1,n1) = sat c1 r s k in
                      let (x2,phi2,n2) = sat (subs c2 (Var x') (Var x)) r s k in
                      let ret_eq_x2 = sprintf "(%s=%s)" ret x2 in
                      let x_eq_x1   = sprintf "(%s=%s)" x' x1  in
                      (ret,x_eq_x1::ret_eq_x2::(phi1@phi2),uplus (x'::ret::n1) n2 [])
  | k,Lambda(f,(x,c1),c2) -> let new_x = fresh_m () in
                             let new_m = Method(new_x) in
                             let f' = fresh_x () in
                             let c2' = subs c2 (Var f') (Var f) in
                             let (x1,phi1,n1) = sat c1 r s k in
                             let (x2,phi2,n2) = sat (subs c2' new_m (Var f'))
                                                    ((new_m,(x,c1))::r) s k in
                             let ret_eq_x2 = sprintf "(%s=%s)" ret x2 in
                             (*x's in methods are replaced on apply, so no need for fresh*)
                             (ret,ret_eq_x2::(phi1@phi2),
                             (*no need to say f' = x1 since it's just put in the repo*)
                             (*we do have to c2{f'/f} though, for SSA*)
                             uplus (new_x::ret::n1) n2 [])
  | Suc(k),Apply(v1,v2) -> let (x,c) = get_method r v1 in
                           let c' = subs c v2 (Var x) in
                           sat c' r s k
  | k,BinOp(v1,v2,op) -> let x1 = string_of_value v1 in
                         let x2 = string_of_value v2 in
                         (ret,[sprintf "(%s=%s%s%s)" ret x1 op x2],ret::[])
  | k,Assign(v1,v2) -> let x1 = string_of_value v1 in
                       let x2 = string_of_value v2 in
                       let v1_eq_v2    = sprintf "(%s=%s)" x1 x2 in
                       let ret_eq_unit = sprintf "(%s=true)" ret in
                       (ret,v1_eq_v2::ret_eq_unit::[],x1::ret::[])
  | k,Deref(v) -> let x = string_of_value (get_state s v) in
                  (ret,[sprintf "(%s=%s)" ret x],ret::[])
  | k,Pi1(Pair(v1,v2)) -> let x = string_of_value v1 in
                          (ret,[sprintf "(%s=%s)" ret x],ret::[])
  | k,Pi2(Pair(v1,v2)) -> let x = string_of_value v2 in
                          (ret,[sprintf "(%s=%s)" ret x],ret::[])
  | k,Val(v) -> let x = string_of_value v in
                (ret,[sprintf "(%s=%s)" ret x],ret::[])
  | k,If(v,c1,c0) -> let (x0,phi0,n0) = sat c0 r s k in
                     let (x1,phi1,n1) = sat c1 r s k in
                     let x = string_of_value v in
                     let v0_to_x0 = sprintf "((%s=0) => (%s=%s))"   x ret x0 in
                     let vi_to_x1 = sprintf "((%s=/=0) => (%s=%s))" x ret x1 in
                     (ret,v0_to_x0::vi_to_x1::(phi0@phi1),uplus (ret::n0) n1 [])
  | k,Fail -> (ret,[sprintf "(%s=false)" ret],ret::[])
  | _ -> (ret,[sprintf "(%s=true)" ret],ret::[])

let rec string_of_phi = function
  | [] -> ""
  | (x::xs) -> sprintf "%s and\n %s" x (string_of_phi xs)


(***********)
(* TESTING *)
(***********)
let factorial_body :(canon) =
  If (Var "n",
      Let("x0",
          BinOp(Var "n",
                Int 1,
                "-"),
          Let("x",
              Apply(Method "f",Var "x0"),
              BinOp(Var "x",
                    Var "n",
                   "*"))),
      Val (Int 1))

let result = sat (Apply(Method "f",Int 5))
                 ((Method "f",("n" , factorial_body))::[]) ([])
                 (nat_of_int 100)

let _ = let (x,y,z) = result in
        printf "Formula:\n %s\n" (string_of_phi y);
        printf "Names:\n %s"     (string_of_names z);
        exit 1
