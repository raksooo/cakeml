open preamble basis javascriptBackendTheory prettyPrintTheory;

val _ = new_theory"compiler";

max_print_depth := 11351351;

fun compile' ast = ``THE (OPTION_MAP prog_toString (ata_prog ^ast))`` |> EVAL;
fun compile input = process_topdecs input |> compile';

val a = compile `
	datatype 'a tree = Nil | Tree ('a tree) 'a ('a tree);
	val a = Tree Nil 5 (Tree Nil 3 Nil);`;

val a = compile `
	val foo = true;
	val bar = foo;`;

val a = compile `
	val foo = true;
	val bar = foo;`;

val a = compile `
	val foo = true;
	val bar = foo orelse false;`;

val a = compile `
	val foo = true;
	fun bar a = foo andalso a;
	bar true;`;

val a = compile `
	val foo = true;
	fun bar a = foo andalso a;
	bar false;`;

val a = compile `
	val foo = let val a = true in a end;`;

val a = compile `
	fun foo a b = a + b - 1;
	foo 1 2;`;

val a = compile `
	val _ = 3 + 2;`;

val a = compile `
	val _ = 3 - 2;`;

val a = compile `
	val _ = 3 * 2;`;

val a = compile `
	val _ = 3 / 2;`;

val a = compile `
	val _ = 1 < 3;`;

val a = compile `
	val _ = 1 <= 3;`;

val a = compile `
	val _ = 1 > 3;`;

val a = compile `
	val _ = 1 >= 3;`;

val a = compile `
	val _ = 1 :: 2 :: [3, 4];`;

val a = compile `
	val foo =
		let
			val a = true
		in
			a
		end;`;

val a = compile `
	val foo = let fun bar a = a in bar true end;`;

val a = compile `
	val foo = ref 5;
	val _ = foo := !foo + 1;
	val _ = !foo;`;

val a = compile `
	val foo = ref 5;
	val _ = foo := !foo + 1;`;

val a = compile `
	val foo = ref 5;
	val bar = foo;
	val _ = bar := !bar + 1;
	val _ = !foo;`;

val a = compile `
	val _ = "foo";`;

val a = compile `
	val _ = (1, "foo", true);`;

val a = compile `
	val _ = if true then 1 else 0;`;

val a = compile `
	val foo = fn a => a + 1;`;

val a = process_topdecs `
	datatype 'a tree = Nil | Tree ('a tree) 'a ('a tree);
	val (Tree l v r) = Tree Nil 5 (Tree Nil 4 NIL);`;

val a = process_topdecs `
	val _ = 1;`;

val a = process_topdecs `
	val a = 1;`;

val a = process_topdecs `
	val 2 = 1;`;

val a = process_topdecs `
	val (a :: b) = [1, 2];`;

val a = process_topdecs `
	val [a, b] = [1, 2];`;

val a = process_topdecs `
	val (a, b) = (1, 2);`;

val a = process_topdecs `
	val ref b = a;`;

val _ = export_theory();

