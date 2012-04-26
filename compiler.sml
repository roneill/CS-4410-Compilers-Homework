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
    
fun filterMoves allocation (Assem.MOVE {assem, src, dst}) = 
	    let
		val s = (case Temp.Table.look (allocation, src)
			  of SOME t => t
			   | NONE => ErrorMsg.impossible "Temp not colored")
		val d = (case Temp.Table.look (allocation, dst)
			  of SOME t => t
			   | NONE => ErrorMsg.impossible "Temp not colored")
	    in
		case String.compare(s,d)
		 of EQUAL => false
		  | _ => true
	    end 
  | filterMoves _  _ = true

fun emitproc out (Frame.PROC{body,frame}) =
    let
	val stms = Canon.linearize body
        val stms' = Canon.traceSchedule(Canon.basicBlocks stms)
	val instrs = List.concat(map (Mips.codegen frame) stms')
	val instrs' = Frame.procEntryExit2(frame, instrs)
	val (instrs'', allocation) = RegAlloc.alloc(instrs', frame)
	val instrs''' = List.filter (filterMoves allocation) instrs''
        val format0 = Assem.format((fn t => case Temp.Table.look (allocation, t)
					      of SOME reg => reg
					       | NONE => ErrorMsg.impossible "Temp was not colored"))
	val {prolog=prolog, body=instrs''', epilog=epilog} = Frame.procEntryExit3(frame, instrs''')
    in
	TextIO.output(out, prolog);
	app (fn i => TextIO.output(out,format0 i)) instrs''';
	TextIO.output(out, epilog)
    end
  | emitproc out (Frame.STRING(lab,s)) =
    let
	val string = Frame.string(lab,s)
	val spimCruft = ".data"^string^".text"
    in
	TextIO.output(out, spimCruft)
    end

fun emitCruft out =
    let
	val spimCruft = String.concat [ ".data\n", 
			      ".globl main\n", 
			      ".text\n\n", 
			      "main:\n",
			      "jal tig_main\n",
			      "li $v0, 10\n",
			      "syscall\n\n" ]
    in
	TextIO.output(out, spimCruft)
    end

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
		     (fn out => (emitCruft out;(app (emitproc out) fraglist)))
    end
        
end
