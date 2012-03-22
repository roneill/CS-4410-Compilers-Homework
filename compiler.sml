signature COMPILER =
sig
    val printIR: unit -> unit
    val printAST: unit -> unit
    val compile: string -> unit
end

structure Compiler : COMPILER =
struct
structure Frame = MipsFrame
		  
val AST = ref Absyn.NilExp
val IR = ref (Translate.getResult())
	 
fun printAST () = () (*TODO print AST*)
fun printIR () =
    let
	val outstream = TextIO.stdOut
	fun printFrag (Frame.PROC {body, frame}) =
	    Printtree.printtree (outstream,body)
	  | printFrag (Frame.STRING (label, s)) =
	    TextIO.output(outstream, s)
    in
	(map printFrag (!IR); ())
    end
	    
fun compile filename =
    let val ast = Parse.parse(filename)
	val fraglist = Semant.transProg ast
    in
	(AST := ast;
	 IR := fraglist)
    end
    
end
