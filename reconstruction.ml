module SS = Set.Make(String)

let is_universal (tau : typ) : bool = match tau with
  | Univ (_, _) -> true
  | _ -> false

let context_to_vars (context: (string * typ) list) =
  List.fold_left (fun acc x -> SS.union (match x with (_, TypeVar w) -> SS.singleton w | _ -> SS.empty) acc) SS.empty context

let rec free_type_vars (tau: typ) = match tau with
  | Univ (x1, tau1) -> SS.remove x1 (free_type_vars tau1)
  | Arrow (tau1, tau2) -> SS.union (free_type_vars tau1) (free_type_vars tau2)
  | TypeVar x -> SS.singleton x
  | _ -> SS.empty

let universalize (tau: typ) s =
  SS.fold (fun w typ_acc -> Univ (w, typ_acc)) s

let rec subst_type (w:string) (tau_original : typ) (tau2 : typ) = match tau_original with
  | Nat | Bool -> tau_original
  | Arrow (tau3, tau4) -> Arrow (subst_type w tau3 tau2, subst_type w tau4 tau2)
  | TypeVar x when x=w -> tau2
  | TypeVar _ -> tau_original
  | Univ (x, _) when x=w -> tau_original
  | Univ (x, tau3) -> Univ (x, (subst_type w tau3 tau2))


let constraint_mappee_maker (w: string) (tau_new : typ) =
  fun ((tau1, tau2) : (typ * typ)) -> ((subst_type w tau1 tau_new), (subst_type w tau2 tau_new))

let current = ref ""
let get_fresh : typ =
  current := (!current) ^ "0";
  TypeVar current;

let rec freshen (tau : typ) : typ = match tau with
  | Univ (x1, tau1) -> freshen (subst_type x1 tau1 (get_fresh))
  | _ -> tau

let rec unify (tau: typ) (c_list: (typ * typ) list) =
  match c_list with
  | (tau1, tau2)::xs when tau1 = tau2 -> unify tau xs
  | (TypeVar w, tau2)::xs when not (SS.mem w (free_type_vars tau2)) ->
    unify (subst_type w tau tau2) (List.map (constraint_mappee_maker w tau2) xs)
  | (tau2, TypeVar w)::xs when not (SS.mem w (free_type_vars tau2)) ->
    unify (subst_type w tau tau2) (List.map (constraint_mappee_maker w tau2) xs)
  | (Arrow (tau1a, tau1b), Arrow (tau2a, tau2b))::xs -> unify tau ((tau1a, tau2a)::(tau1b,
  tau2b)::xs)
  | [] -> tau

let look_up (context: (string * typ) list) (var : string) =
  List.find (fun (x, _) -> x = var) context

let rec typecheck_r (t: term) (context: (string * typ) list) : (typ * ((typ * typ) list)) =
  match t with
    | Var x -> [(freshen (look_up context x)); []] (* TODO: make this not lookupthingy *)
    | Lambda (x, t1) -> let tau1 = (get_fresh) and
      tau2, c_list = typecheck_r t1 tau1::context in
      [Arrow (tau1, tau2); c_list]
    | App (t1, t2) -> let tau1, c_list1 = typecheck_r t1 context and
      tau2, c_list2 = typecheck_r t2 context and
      tau3 = (get_fresh) in
      tau3, (tau1, Arrow (tau2, tau3))::(append c_list1 c_list2)
    | Fix t1 -> let tau1, c_list1 = typecheck_r t1 context and
      tau2 = (get_fresh) in
      tau2, (tau1, Arrow (tau2, tau2))::c_list1
    | Let (x, t1, t2) -> let tau1, c_list1 = typecheck_r t1 context and
      tau1 = unify tau1 c_list1 and
      tau1 = universalize tau1 (SS.diff (free_type_vars tau1) (context_to_vars context)) in
      typecheck_r t2 (x, tau1)::context
    | Zero -> (Nat, [])
    | True | False -> (Bool, [])
    | Succ t1 | Pred t1 ->
      let tau1, c_list = typecheck_r t1 context and
      tau1 = unify tau1 c_list in
      (match tau1 with
      | Nat -> Nat
      | _ -> (raise TypeError ("Can't do " ^ format_term t ^ " since " ^ format_term t1 ^ " non number\n")))
    | IsZero t1 ->
      let tau1, c_list = typecheck_r t1 context and
      tau1 = unify tau1 c_list in
      (match tau1 with
      | Nat -> Bool
      | _ -> (raise TypeError ("Can't do " ^ format_term t ^ " since " ^ format_term t1 ^ " non number\n")))

    | If (t1, t2, t3) ->
      let tau1, c_list1 = typecheck_r t1 context and
      tau2, c_list2 = typecheck_r t2 context and
      tau3, c_list3 = typecheck_r t3 context and
      c_list = (c_list1 @ c_list2 @ c_list3) and
      tau1 = unify tau1 c_list and
      tau2 = unify tau2 c_list and
      tau3 = unify tau3 c_list in
      if ((tau1 = true || tau1 = false) && (tau2 = tau3)) then (tau2, c_list) else (raise TypeError ("don't do that"))

let typecheck t =
  let tau, constraints = typecheck_r t [] in
    unify tau constraints
