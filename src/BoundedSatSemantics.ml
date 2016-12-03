(*author: Yu-Yang Lin, date: 21/11/2016*)
open AbstractSyntax
open Format

(*******************)
(* Fresh Variables *)
(*******************)
let var_x  = ref 0
let var_r  = ref 0
let var_m  = ref 0
let return = ref 0
let fresh_x   () = var_x  := !var_x + 1;  sprintf "_x_%s_"   (string_of_int (!var_x))
let fresh_r   () = var_r  := !var_r + 1;  sprintf "_r_%s_"   (string_of_int (!var_r))
let fresh_m   () = var_m  := !var_m + 1;  sprintf "_m_%s_"   (string_of_int (!var_m))
let fresh_ret () = return := !return + 1; sprintf "_ret_%s_" (string_of_int (!return))

(**********************)
(* Substitute: v{a/b} *)
(**********************)
let rec subs_pair (v : value) (a : value) (b : value) =
  match v with
  | Pair(v1,v2) -> Pair(subs_pair v1 a b, subs_pair v2 a b)
  | v -> if v=b then a else v

let rec subs (m : canon) (a : value) (b : value) =
  match m with
  | Let(x,c1,c2) -> if x=b then m else Let(x,(subs c1 a b),(subs c2 a b))
  | Lambda(f,(x,c1),c2) -> if f=b then m
                           else (if x=b
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
let rec sat_smt (m : canon) (r : repo) (rc : counter) (rd : counter) (k : nat) (acc : cnf) :(var * cnf * repo * counter * counter) =
  let ret = fresh_ret () in
  match (k,m) with
  | Nil,_ -> (ret,(ret === cnf_nil)::acc,r,rc,rd)
  | k,Let(Var(x,tau),c1,c2) ->
     let x' = fresh_x () in
     let (x1,phi1,r1,rc1,rd1) = sat_smt c1 r rc rd k acc in
     let (x2,phi2,r2,rc2,rd2) = sat_smt (subs c2 (Var (x',tau)) (Var (x,tau)))
                                        r1 rc1 rd1 k phi1 in
     let x_fail   = (x'===cnf_fail)==>(ret===cnf_fail) in
     let x_nofail = (x'=/=cnf_fail)==>(ret===x2)       in
     let x_eq_x1  = x' === x1  in
     (ret,x_fail::x_nofail::x_eq_x1::phi2,r2,rc2,rd2)
  | k,Lambda(Var(f,tau_to_tau),(Var(x,tau1),c1),c2) ->
     let new_x = fresh_m () in
     let new_m = Method(new_x) in
     let f' = fresh_x () in
     let f'' = Var (f',tau_to_tau) in
     let c2' = subs c2 f'' (Var (f,tau_to_tau)) in
     let (x2,phi2,r2,rc2,rd2) = sat_smt (subs c2' new_m f'')
                                        (repo_update r new_m (Var(x,tau1),c1,tau_to_tau))
                                        rc rd k acc in
     let ret_eq_x2 = ret === x2 in
     (*x's in methods are replaced on apply, so no need for fresh*)
     (ret,ret_eq_x2::phi2,r2,rc2,rd2)
     (*no need to say f' = x1 since it's just put in the repo*)
     (*we do have to c2{f'/f} though, for SSA*)
  | Suc(k),Apply(Method(m),v) ->
     let (x,c,tau) = repo_get r (Method(m)) in
     let c' = subs c v x in
     sat_smt c' r rc rd k acc
  | Suc(k),Apply(Var(x,tau),v) ->
     (** NOTE: this could be optimised **)
     (* fold over all repo names to compute ret = reti *)
     let f key (xi,mi,taui) (philast,rlast,rclast,rdlast) =
       if taui=tau
       then let key_string = string_of_value key in (* refs in R *)
            let (reti,phii,ri,rci,rdi) = sat_smt (subs mi v xi) rlast rclast rd k acc in
            let phii'  = ((x===key_string)==>(ret===reti))::phii in
            (phii',ri,rci,(key_string,rdi)::rdlast)
       else (philast,rlast,rclast,rdlast)
     in
     let phij,rj,rcj,rd_list = Repo.fold f r (acc,r,rc,[]) in
     (* fold over all Di's and C' for the (x=m_i) in the implication *)
     let rcj' = Counter.map (fun x -> x + 1) rcj in
     let phij' =
       List.fold_right
         (fun (key_string,rdi) phi_acc1 ->
           (* fold over all C' for the (C'(r)=Di(r)) in the implication *)
           Counter.fold
             (fun ref_key counter_val phi_acc2 ->
               let ref_i = string_of_ref ref_key counter_val in
               ((x===key_string)==>(ref_i===(ref_get rdi ref_key)))::phi_acc2)
             rcj' phi_acc1)
         rd_list phij
     in
     (ret,phij',rj,rcj',rcj')
  | k,BinOp(v1,v2,op) ->
     let binop = string_of_canon (BinOp(v1,v2,op)) in
     (ret,(ret === binop)::acc,r,rc,rd)
  | k,Assign(Ref v1,v2) ->
     let x1 = string_of_value (Ref v1) in
     let x2 = string_of_value v2 in
     let rc'= c_update rc x1 in
     let rd'= d_update rd x1 (c_get rc' x1) in
     let v1_eq_v2    = (ref_get rc' x1) === x2 in
     let ret_eq_unit = ret === "true" in
     (ret,v1_eq_v2::ret_eq_unit::acc,r,rc',rd')
  | k,Deref(Ref(v)) ->
     let x = ref_get rd v in
     (ret,(ret === x)::acc,r,rc,rd)
  | k,Pi1(Pair(v1,v2)) ->
     let x = string_of_value v1 in
     (ret,(ret === x)::acc,r,rc,rd)
  | k,Pi2(Pair(v1,v2)) ->
     let x = string_of_value v2 in
     (ret,(ret === x)::acc,r,rc,rd)
  | k,Val(v) ->
     let x = string_of_value v in
     (ret,(ret === x)::acc,r,rc,rd)
  | k,If(v,c1,c0) ->
     let (x0,phi0,r0,rc0,rd0) = sat_smt c0 r  rc  rd k acc  in
     let (x1,phi1,r1,rc1,rd1) = sat_smt c1 r0 rc0 rd k phi0 in
     let rc' = Counter.map (fun x -> x + 1) rc1 in
     let x = string_of_value v in
     let v0_to_x0 = (x==="0")==>(ret===x0) in
     let vi_to_x1 = (x=/="0")==>(ret===x1) in
     let phi2_0 =
       Counter.fold
             (fun ref_key counter_val phi_acc ->
               ((x==="0")==>((string_of_ref ref_key counter_val)===(ref_get rd0 ref_key)))::phi_acc)
             rc' phi1
     in
     let phi2_1 =
       Counter.fold
             (fun ref_key counter_val phi_acc ->
               ((x=/="0")==>((string_of_ref ref_key counter_val)===(ref_get rd1 ref_key)))::phi_acc)
             rc'
             phi2_0
     in
     (ret,vi_to_x1::v0_to_x0::phi2_1,r1,rc',rc')
  | k,Fail -> (ret,(ret === cnf_fail)::acc,r,rc,rd)
  | _ -> failwith (sprintf "***[error] : unexpected input to SAT/SMT semantics\n%s"
                           (string_of_canon m))

(***********************)
(* String_of functions *)
(***********************)
let string_of_clause = function
  | Eq (x,y) -> sprintf "(%s=%s)" x y
  | Neq(x,y) -> sprintf "(%s=/=%s)" x y
let rec string_of_cnf' acc = function
  | [] -> acc
  | (Clause x)::xs -> let s = sprintf "%s and\n %s" acc (string_of_clause x) in
                      string_of_cnf' s xs
  | (Implies (x,y))::xs -> let s = sprintf "%s and\n (%s=>%s)" acc
                                           (string_of_clause x)
                                           (string_of_clause y) in
                           string_of_cnf' s xs
let string_of_cnf = function
  | [] -> ""
  | (Clause x)::xs -> let s = (string_of_clause x) in
                      string_of_cnf' s xs
  | (Implies (x,y))::xs -> let s = sprintf "(%s=>%s)"
                                           (string_of_clause x)
                                           (string_of_clause y) in
                           string_of_cnf' s xs


(***********)
(* TESTING *)
(***********)
let time f x =
    let t = Sys.time() in
    let res = f x in
    printf "Execution time: %fs\n" (Sys.time() -. t);
    res

(*~~~~~~~~~~~~~~~~*)
(* TEST FUNCTIONS *)
(*~~~~~~~~~~~~~~~~*)
(*************************)
(* if n                  *)
(* then let x0 = n-1 in  *)
(*      let x  = f x0 in *)
(*      x*n              *)
(* else 1                *)
(*************************)
let factorial :(value * canon * tp) =
  let n  = Var("n",Integer) in
  let x  = Var("x",Integer) in
  let x0 = Var("x0",Integer) in
  let factorial_body :(canon) =
    If (n,
        Let(x0,BinOp(n,Int 1,"-"),
            Let(x,Apply(Method "f",x0),
                BinOp(x,n,"*"))),
        Val (Int 1))
  in
  let tau = Arrow(Integer,Integer)
  in (n,factorial_body,tau)

let factorial_sat = sat_smt (Apply(Method "f",Int 5))
                            (repo_update empty_repo (Method "f") factorial)
                            (empty_counter)
                            (empty_counter)

(****************************)
(* if n                     *)
(* then let x = r1 := 1 in  *)
(*      let x = r2 := 2 in  *)
(*      skip                *)
(* else let x = r2 := 0 in  *)
(*      skip                *)
(****************************)
let ssa_1 =
  let n  = Var("n",Integer) in
  let x  = Var("x",Command) in
  let r1 = Ref("r1") in
  let r2 = Ref("r2") in
  let ssa_1_body = If (n,
                       Let(x,Assign(r1,Int 1),
                           Let(x,Assign(r2,Int 2),Val Unit)),
                       Let(x,Assign(r2,Int 0),Val Unit))
  in
  let tau = Arrow(Integer,Command) in
  (n,ssa_1_body,tau)

let ssa_1_sat = sat_smt (Apply(Method "m",Int 1))
                        (repo_update empty_repo (Method "m") ssa_1)
                        (empty_counter)
                        (empty_counter)

(****************)
(*** RUN TEST ***)
(****************)
let result = ssa_1_sat (nat_of_int 2) []

let _ = let (ret,phi,repo,c_counter,d_counter) = result in
        printf "Formula:\n %s\n" (string_of_cnf (phi));
        exit 0
