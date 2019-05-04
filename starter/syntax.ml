(* Types *)

type typ =
  | Nat | Bool 
  | Arrow of (typ * typ)
  | TypeVar of string

type term =
  | Zero | Succ of term | Pred of term | IsZero of term
  | True | False | If of (term * term * term)
  | Var of string
  | Lambda of (string * term)
  | TypedLambda of (string * typ * term)
  | App of (term * term)
  | Let of (string * term * term)
  | Fix of term

exception Parse_error of string

(* Constants *)

let isspace c = String.contains " \t\n" c
let special_toks = ["("; ")"; "λ"; "\\"; "."; "="; ":"; "->"]
let reserved_words = ["0"; "succ"; "pred"; "iszero";
                      "true"; "false"; "if"; "then"; "else";
                      "let"; "in"; 
                      "fix"]

(* Lexer *)

let occurs_at ss s i = 
  let n = String.length ss in 
  i+n <= String.length s && String.sub s i n = ss

let lexer (s:string) =
  let rec scan i j w =
    let flush () = if i < j then String.sub s i (j-i) :: w else w in
    if j == String.length s then flush ()
    else if isspace s.[j] then scan (j+1) (j+1) (flush ())
    else match List.find_opt (fun tok -> occurs_at tok s j) special_toks with
    | Some tok -> let j = j + String.length tok in scan j j (tok :: flush ())
    | None -> scan i (j+1) w
  in List.rev (scan 0 0 [])

(* Parser *)

let expect what w =
  match w with
  | a::rest when a = what -> rest
  | _ -> raise (Parse_error ("expected '" ^ what ^ "'"))

let rec parse_abs w =
  match w with
  | [] -> raise (Parse_error "unexpected end of string")
  | "\\"::w | "λ"::w ->
      let x, w = parse_var w in
      (match w with
      | ":"::w -> 
        let tau, w = parse_arrow w in
        let w = expect "." w in
        let t, w = parse_abs w in TypedLambda (x, tau, t), w
      | "."::w -> let t, w = parse_abs w in Lambda (x, t), w
      | _ -> raise (Parse_error "expected : or ."))
  | "if"::w ->
      let t1, w = parse_abs w in
      let w = expect "then" w in
      let t2, w = parse_abs w in
      let w = expect "else" w in
      let t3, w = parse_abs w in
        If (t1, t2, t3), w
  | "let"::w ->
      let x, w = parse_var w in
      let w = expect "=" w in
      let t1, w = parse_abs w in
      let w = expect "in" w in
      let t2, w = parse_abs w in
        Let (x, t1, t2), w
  | _ -> parse_app w

and parse_app w =
  let rec loop w t =
    match w with
    | [] | ")"::_ | "then"::_ | "else"::_ | "in"::_ -> t, w
    | _ -> let arg, w = parse_atom w in loop w (App (t, arg))
  in
    match w with
    | "succ"::w -> let t, w = parse_atom w in loop w (Succ t)
    | "pred"::w -> let t, w = parse_atom w in loop w (Pred t)
    | "iszero"::w -> let t, w = parse_atom w in loop w (IsZero t)
    | "fix"::w -> let t, w = parse_atom w in loop w (Fix t)
    | _ -> let t, w = parse_atom w in loop w t

and parse_atom w =
  match w with
  | [] -> raise (Parse_error "unexpected end of string")
  | "("::w -> let t, w = parse_abs w in t, expect ")" w
  | "true"::w -> True, w
  | "false"::w -> False, w
  | "0"::w -> Zero, w
  | _ -> let x, w = parse_var w in Var x, w

and parse_var w =
  match w with
  | x::w when List.mem x special_toks || List.mem x reserved_words -> 
      raise (Parse_error ("unexpected '" ^ x ^ "'"))
  | x::w -> x, w
  | [] -> raise (Parse_error "unexpected end of string")

and parse_arrow w =
  let tau, w = parse_base w in
  match w with
  | "->"::w -> let tau2, w = parse_arrow w in Arrow (tau, tau2), w
  | _ -> tau, w

and parse_base w =
  match w with
  | "Nat"::w -> Nat, w
  | "Bool"::w -> Bool, w
  | "("::w -> let tau, w = parse_arrow w in tau, expect ")" w
  | [] -> raise (Parse_error "unexpected end of string")
  | tok::w -> raise (Parse_error ("unexpected '" ^ tok ^ "'"))

let parse_term s =
  let (t, w) = parse_abs (lexer s) in
    match w with
    | [] -> t
    | tok::w -> raise (Parse_error ("unexpected '" ^ tok ^ "' after term"))

let format_type (tau:typ) : string =
  let rec arrow tau =
    match tau with
    | Arrow (tau1, tau2) -> base tau1 ^ "->" ^ arrow tau2
    | _ -> base tau
  and base tau =
    match tau with
    | Nat -> "Nat"
    | Bool -> "Bool"
    | TypeVar x -> x
    | _ -> "(" ^ arrow tau ^ ")"
  in
    arrow tau

let format_term (t:term) : string =
  let rec abs t =
    match t with
    | If (t1, t2, t3) -> "if " ^ abs t1 ^ " then " ^ abs t2 ^ " else " ^ abs t3
    | Lambda (x, t) -> "λ" ^ x ^ ". " ^ abs t
    | TypedLambda (x, tau, t) -> "λ" ^ x ^ ":" ^ format_type tau ^ ". " ^ abs t
    | Let (x1, t2, t3) -> "let " ^ x1 ^ " = " ^ abs t2 ^ " in " ^ abs t3
    | _ -> app t
  and app t =
    match t with
    | Succ t1 -> "succ " ^ atom t1
    | Pred t1 -> "pred " ^ atom t1
    | Fix t1 -> "fix " ^ atom t1
    | IsZero t1 -> "iszero " ^ atom t1
    | App (t1, t2) -> app t1 ^ " " ^ atom t2
    | _ -> atom t
  and atom t =
    match t with
    | Zero -> "0"
    | True -> "true"
    | False -> "false"
    | Var x -> x
    | _ -> "(" ^ abs t ^ ")"
  in 
    abs t

let rec read_lines prompt f = 
  try
    if Unix.isatty Unix.stdin then print_string prompt else ();
    let line = read_line () in
      f line;
      read_lines prompt f
  with
    End_of_file -> if Unix.isatty Unix.stdin then print_newline () else ()
