signature COMPILER =
sig
    val printIR: unit -> unit
    val printAST: unit -> unit
    val compile: string -> unit
end

structure Compiler : COMPILER =
struct
structure Frame = MipsFrame
structure Mips = MipsGen
		  
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

fun emitproc out (Frame.PROC{body,frame}) =
    let val _ = () (*print ("emit " ^ Frame.name frame ^ "\n")*)
	         (*val _ = Printtree.printtree(out,body); *)
	 val stms = Canon.linearize body
	         (*val _ = app (fn s => Printtree.printtree(out,s)) stms;*)
         val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
	 val instrs =   List.concat(map (Mips.codegen frame) stms')
         val format0 = Assem.format(Frame.tempToString)
    in
	app (fn i => TextIO.output(out,format0 i)) instrs
    end
  | emitproc out (Frame.STRING(lab,s)) =()(* TextIO.output(out,Frame.string(lab,s))*)

fun withOpenFile fname f = 
    let val out = TextIO.openOut fname
    in (f out before TextIO.closeOut out) 
       handle e => (TextIO.closeOut out; raise e)
    end 


fun compile filename =
    let val ast = Parse.parse(filename)
	val fraglist = Semant.transProg ast
	val _ = (AST := ast; IR := fraglist)
		
    in
	withOpenFile (filename ^ ".s") 
		     (fn out => (app (emitproc out) fraglist))
    end
end
