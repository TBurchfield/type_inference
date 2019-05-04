open Syntax

exception Type_error of string
exception Eval_error of string

module SS = Set.Make(String)
let fold_union ss = List.fold_left SS.union SS.empty ss

module SM = Map.Make(String)

let rec free_vars (t:term) =
  match t with
    | Zero | True | False -> SS.empty
    | Succ t1 | Pred t1 | IsZero t1 | Fix t1 -> free_vars t1
    | If (t1, t2, t3) -> fold_union (List.map free_vars [t1; t2; t3])
    | Var x -> SS.singleton x
    | TypedLambda (x, _, t1) -> SS.remove x (free_vars t1) 
    | App (t1, t2) -> SS.union (free_vars t1) (free_vars t2)
    | Let (x, t1, t2) -> SS.union (free_vars t1) (SS.remove x (free_vars t2))
    | Lambda (_, _) -> raise (Parse_error "argument must have type")

let rec subst (x:string) (v:term) (t:term) =
  match t with
    | Zero | True | False -> t
    | Succ t1 -> Succ (subst x v t1)
    | Pred t1 -> Pred (subst x v t1)
    | IsZero t1 -> IsZero (subst x v t1)
    | Fix t1 -> Fix (subst x v t1)
    | If (t1, t2, t3) -> If (subst x v t1, subst x v t2, subst x v t3)
    | Var x1 -> if x = x1 then v else t
    | TypedLambda (x1, _, _) when x1 = x -> t
    | TypedLambda (x1, tau1, t2) -> TypedLambda (x1, tau1, subst x v t2)
    | App (t1, t2) -> App (subst x v t1, subst x v t2)
    | Let (x1, t2, t3) when x1 = x -> Let (x1, subst x v t2, t3)
    | Let (x1, t2, t3) -> Let (x1, subst x v t2, subst x v t3)
    | Lambda (_, _) -> raise (Parse_error "argument must have type")

let rec eval_term (t:term) =
  match t with
    | Zero | True | False -> t

    | Succ t1 -> (match eval_term t1 with
      | Zero | Succ _ as v1 -> Succ v1
      | _ -> raise (Eval_error "can't take succ of non-number"))

    | Pred t1 -> (match eval_term t1 with
      | Zero -> Zero
      | Succ v1 -> v1
      | _ -> raise (Eval_error "can't take pred of non-number"))

    | IsZero t1 -> (match eval_term t1 with
      | Zero -> True
      | Succ v -> False
      | _ -> raise (Eval_error "can't apply iszero to non-number"))

    | If (t1, t2, t3) -> (match eval_term t1 with
      | True -> eval_term t2
      | False -> eval_term t3
      | _ -> raise (Eval_error "can't condition on non-boolean"))

    | TypedLambda _ -> t

    | App (t1, t2) -> (match eval_term t1 with 
       | TypedLambda (x11, _, t12) -> let v2 = eval_term t2 in eval_term (subst x11 v2 t12)
       | _ as v1 -> raise (Eval_error ("application of non-function: " ^ format_term v1)))

    | Let (x, t1, t2) -> let v1 = eval_term t1 in eval_term (subst x v1 t2)
    
    | Fix t1 -> (match eval_term t1 with
       | TypedLambda (x11, _, t12) as v1 -> subst x11 (Fix v1) t12
       | _ -> raise (Eval_error "fix must be applied to function"))

    | _ -> raise (Eval_error ("invalid expression " ^ format_term t))

let rec typecheck (env: (string * typ) list) (t:term) : typ =
  match t with
    | Zero -> Nat
    | True | False -> Bool
    | Succ t1 | Pred t1 -> 
        (match typecheck env t1 with
           | Nat -> Nat
           | _ -> raise (Type_error "succ/pred of non-number"))

    | IsZero t1 ->
        (match typecheck env t1 with
           | Nat -> Bool
           | _ -> raise (Type_error "iszero of non-number"))

    | If (t1, t2, t3) ->
        (match List.map (typecheck env) [t1; t2; t3] with
          | [Bool; tau2; tau3] when tau2 = tau3 -> tau2
          | _ -> raise (Type_error "condition is not Bool, or arms don't match"))

    | Var x ->
        (match List.assoc_opt x env with
           | Some tau -> tau
           | None -> raise (Eval_error "unbound type variable"))
    
    | TypedLambda (x1, tau1, t2) ->
        let tau = typecheck ((x1, tau1)::env) t2 in Arrow (tau1, tau)

    | App (t1, t2) ->
        let tau2 = typecheck env t2 in
          (match typecheck env t1 with
             | Arrow (tau11, tau12) when tau11 = tau2 -> tau12
             | _ -> raise (Type_error "application of non-function or function of wrong type"))

    | Let (x, t1, t2) -> let tau1 = typecheck env t1 in typecheck ((x, tau1)::env) t2

    | Fix t1 -> (match typecheck env t1 with
                  | Arrow (tau11, tau12) when tau11 = tau12 -> tau11
                  | _ -> raise (Type_error "fix requires an argument of type X -> X"))

    | _ -> raise (Eval_error "aieeeee")

let () = read_lines "pcf> " (fun line ->
  try
    let t = parse_term line in
      if SS.is_empty (free_vars t) then
        let tau = typecheck [] t in
        let v = eval_term t in
          print_string (format_term v ^ " : " ^ format_type tau ^ "\n")
      else
        raise (Parse_error "unbound variables")
  with
    Parse_error s | Eval_error s | Type_error s -> print_string ("error: " ^ s ^ "\n"))
