#load "/usr/lib/ocaml/unix.cma"
#use "./starter/syntax.ml"
#use "./starter/pcf.ml"
#use "./reconstruction.ml"

let interp line = 
  try
    let t = parse_term line in
      if SS.is_empty (free_vars t) then
        let tau = typecheck t in
        let v = eval_term t in
          print_string (format_term v ^ " : " ^ format_type tau ^ "\n")
      else
        raise (Parse_error "unbound variables")
  with
    Parse_error s | Eval_error s | Type_error s -> print_string ("error: " ^ s ^ "\n")
    | Recons_error s -> print_string ("type reconstruction error: " ^ s ^ "\n")

let () = read_lines "tinf> " interp
