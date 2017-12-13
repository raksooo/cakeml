open preamble;

val _ = new_theory"cakemlMockAstAndSemantics";

val cml_lit_def = Hol_datatype `
  cml_lit =
      Cml_boolean of bool`;

val cml_unary_op_def = Hol_datatype `
  cml_unary_op =
      Cml_not`;

val cml_binary_op_def = Hol_datatype `
  cml_binary_op =
      Cml_and
    | Cml_or
    | Cml_impl
    | Cml_eq`;

val cml_expr_def = Hol_datatype `
  cml_expr =
      Cml_lit of cml_lit
    | Cml_unary of cml_unary_op => cml_expr
    | Cml_binary of cml_binary_op => cml_expr => cml_expr`;

val cml_sem_def = Define `
  (cml_sem (Cml_lit (Cml_boolean b)) = b) /\
  (cml_sem (Cml_unary op expr) = case op of
      Cml_not => ~(cml_sem expr)) /\
  (cml_sem (Cml_binary op expr1 expr2) = case op of
      Cml_and => (cml_sem expr1) /\ (cml_sem expr2)
    | Cml_or => (cml_sem expr1) \/ (cml_sem expr2)
    | Cml_impl => (cml_sem expr1) ==> (cml_sem expr2)
    | Cml_eq => (cml_sem expr1) <=> (cml_sem expr2))`;

val _ = export_theory()

