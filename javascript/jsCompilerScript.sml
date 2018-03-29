open preamble basis jsBackendTheory jsPrettyPrintTheory jsComputeLib;

val _ = new_theory"jsCompiler";

max_print_depth := 11351351;

fun compile' ast = ``THE (OPTION_MAP prog_toString (compile_prog ^ast))``;
fun compile input = process_topdecs input |> compile' |> jseval;

val a = process_topdecs `
	fun bar a = case a of 0 => 0 | _ => a - 1`;

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
	val _ = [3, 4, 5];`;

val a = compile `
	val _ = 1 :: 2 :: [];`;

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

val a = compile `
	val _ = case Tree Nil 5 Nil of
			Tree t1 v t2 => v;`;

val a = compile `
	val _ = 1;`;

val a = compile `
	val a = 1;`;

val a = compile `
	val 1 = 1;`;

val a = compile `
	val 2 = 1;`;

val a = compile `
	val (a :: b) = [1, 2];`;

val a = compile `
	val [a, b] = [1, 2];`;

val a = compile `
	val (a :: b) = [1, 2, 3];`;

val a = compile `
	val (a, b) = (1, 2);`;

val a = compile `
	val (a, ("foo", ref b)) = (3, ("foo", ref 5));`;

val a = compile `
	val a = ref 5;
	val ref b = a;`;

val a = compile `
	val (a : int) = 4;`;

val a = compile `
	datatype foobar = Foo string string | Bar int;
	val (Foo a b) = Foo "foo" "bar";`;

val a = compile `
	datatype foobar = Foo string string | Bar int;
	val (Bar a) = Foo "foo" "bar";`;

val a = compile `
	datatype foobar = Foo string string | Bar int;
	val (Bar a b) = Foo "foo" "bar";`;

val a = compile `
	val _ = case "bar" of
		  "foo" => 1
		| "bar" => 2;`;

val a = compile `
	datatype foobar = Foo string string | Bar ((int,  string) list);
	val (Foo _ _) = Foo "foo" "bar";`;

val a = compile `
  datatype foobar = Foo int;
  val (Foo _) = Foo 5;`;

val a = compile `
	val _ = case (1, (2, 3)) of
		(n, (_, n)) => n;`;

val a = compile `
	val _ = case (1, 2) of
		  (_, _) => 1;`;

val a = compile `
	fun tail x = case x of
		(y :: ys) => ys;`;

val a = compile `
	datatype l = Nil | Dot l l;
	fun size x = case x of
			Nil => 1
		| Dot l1 l2 => size l1 + size l2;
	val a = size (Dot Nil (Dot Nil Nil));`;

val a = compile `
	val _ = [2 = 2, 2 = 3, 2 = "foo", "foo" = "foo", "foo" = "bar",
					(fn a => a) = "foo", (fn a => a) = (fn b => b + 1)]`;

val a = compile `
	val _ = [2 <> 2, 2 <> 3, 2 <> "foo", "foo" <> "foo", "foo" <> "bar",
					(fn a => a) <> "foo", (fn a => a) <> (fn b => b + 1)]`;

val a = compile `
	datatype 'a foo = Foo 'a;
	val (Foo (Foo n)) = Foo (Foo 4);`;

val a = compile `
	exception Error int string;
	val _ = raise (Error 5 "foo");`;

val a = compile `
	exception Error;
	val _ = (raise Error) handle
			Error => 0`;

val a = compile `
	exception Error int;`;

val _ = export_theory();

