open preamble javascriptAstTheory javascriptSemanticsTheory astTheory stringTheory;

val _ = new_theory"javascriptBackend";

val	sequence_option_def = Define `
	sequence_option options = case options of
		| (NONE :: _) => NONE
		| (SOME opt :: []) => SOME [opt]
		| (SOME opt :: options) => case sequence_option options of
				| NONE => NONE
				| (SOME options) => SOME (opt :: options)`;

val apply_if_some_def = Define `
	(apply_if_some _ NONE = NONE) /\
	(apply_if_some f (SOME v) = SOME (f v))`;

val apply_if_some_list_def = Define `
	apply_if_some_list f options = apply_if_some f (sequence_option options)`;

val ata_op_def = Define `
	ata_op op [a; b] =
		(JSApp (JSAFun ["a"; "b"] (JSBop op (JSVar "a") (JSVar "b"))) [a; b])`;

val ata_exp_def = Define `
	(ata_exp (Lannot exp _) = ata_exp exp) /\
	(ata_exp (Con (SOME (Short "true")) _) = SOME (JSLit (JSBool T))) /\
	(ata_exp (Con (SOME (Short "false")) _) = SOME (JSLit (JSBool F))) /\
	(ata_exp (Log And exp1 exp2) = let exps = [ata_exp exp1; ata_exp exp2]
		in apply_if_some_list (ata_op JSAnd) exps) /\
	(ata_exp (Log Or exp1 exp2) = let exps = [ata_exp exp1; ata_exp exp2]
		in apply_if_some_list (ata_op JSOr) exps) /\
	(ata_exp _ = NONE)`;

val ata_dec_def = Define `
	(ata_dec (Dlet _ Pany exp) = apply_if_some JSExp (ata_exp exp)) /\
	(ata_dec (Dlet _ (Pvar name) exp) = apply_if_some (JSLet name) (ata_exp exp)) /\
	(ata_dec _ = NONE)`;

val ata_top_def = Define `
	(ata_top (Tdec dec) = apply_if_some JSStm (ata_dec dec)) /\
	(ata_top _ = NONE)`;

val ast_to_ast_unsequenced_def = Define `
	(ast_to_ast_unsequenced [] = []) /\
	(ast_to_ast_unsequenced (a::ast) = (ata_top a)::(ast_to_ast_unsequenced ast))`;

val ast_to_ast_sequenced_def = Define `
	ast_to_ast ast = sequence_option (ast_to_ast_unsequenced ast)`;

val _ = export_theory();

