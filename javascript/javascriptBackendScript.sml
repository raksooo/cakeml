open preamble javascriptAstTheory javascriptSemanticsTheory cakemlMockAstAndSemanticsTheory;

val _ = new_theory"javascriptBackend";

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

val _ = export_theory();

