open preamble javascriptMockAstTheory;

val _ = new_theory"javascriptSemantics";

val js_sem_def = Define `
  (js_sem (Js_lit (Js_boolean b)) = b) /\
  (js_sem (Js_unary op expr) = case op of
      Js_not => ~(js_sem expr)) /\
  (js_sem (Js_binary op expr1 expr2) = case op of
      Js_and => (js_sem expr1) /\ (js_sem expr2)
    | Js_or => (js_sem expr1) \/ (js_sem expr2)
    | Js_eq => (js_sem expr1) <=> (js_sem expr2))`;

val _ = export_theory();

