open preamble javascriptAstTheory javascriptSemanticsTheory
		 astTheory;

val _ = new_theory"javascriptBackend";

val ata_exp_def = Define `
	(ata_exp (Lannot exp _) = ata_exp exp) /\
	(ata_exp (Con (SOME (Short "true")) _) = JSLit (JSBool T)) /\
	(ata_exp (Con (SOME (Short "false")) _) = JSLit (JSBool F)) /\
	(ata_exp (Log And exp1 exp2) = JSApp (JSOpb JSAnd) [ata_exp exp1; ata_exp exp2])
	(ata_exp (Log Or exp1 exp2) = JSApp (JSOpb JSOr) [ata_exp exp1; ata_exp exp2])`;

val ata_dec_def = Define `
	(ata_dec (Dlet _ Pany exp) = JSExp (ata_exp exp)) /\
	(ata_dec (Dlet _ (Pvar name) exp) = JSLet name (ata_exp exp))`;

val ata_top_def = Define `
	(ata_top (Tdec dec) = JSStm (ata_dec dec))`;

val ast_to_ast_def = Define `
	(ast_to_ast [] = []) /\
	(ast_to_ast (a::ast) = (ata_top a)::(ast_to_ast ast))`;

(*
val ast_to_ast_def = Define `
  (ast_to_ast (Cml_lit (Cml_boolean b)) = SOME (Js_lit (Js_boolean b))) /\
  (ast_to_ast (Cml_unary op expr) = let t = ast_to_ast expr
    in case (op, t) of
        (Cml_not, SOME e) => SOME (Js_unary Js_not e)
      | _ => NONE) /\
  (ast_to_ast (Cml_binary op expr1 expr2) = let
      t1 = ast_to_ast expr1;
      t2 = ast_to_ast expr2
    in case (op, t1, t2) of
        (Cml_and, SOME e1, SOME e2) => SOME (Js_binary Js_and e1 e2)
      | (Cml_or, SOME e1, SOME e2) => SOME (Js_binary Js_or e1 e2)
      | (Cml_eq, SOME e1, SOME e2) => SOME (Js_binary Js_eq e1 e2)
      | (Cml_impl, SOME e1, SOME e2) => let ne1 = Js_unary Js_not e1 in
          SOME (Js_binary Js_or ne1 e2)
      | _ => NONE)`;
val ast_to_ast_ind = fetch "-" "ast_to_ast_ind"
*)

val _ = export_theory();

