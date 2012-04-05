signature COMPILER =
sig
    val printIR: unit -> unit
    val printAST: unit -> unit
    val compile: string -> unit
    val test: unit -> unit
end

structure Compiler : COMPILER =
struct
structure Frame = MipsFrame
structure Mips = MipsGen
structure AssemStore = AssemStore
structure MakeGraph = MakeGraph
structure Graph = Graph
		  
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
    
fun testLiveness ()=
(* the undefined label is for the "hello, world" string itself *)
    let
	val (_,_,instrs) = AssemStore.decode ("tig_main", 9, [
					AssemStore.OPER{assem="sw `s1, -4(`s0)", src=[0,16], dst=[], jump=NONE},
					AssemStore.OPER{assem="sw `s1, -8(`s0)", src=[0,17], dst=[], jump=NONE},
					AssemStore.OPER{assem="sw `s1, -12(`s0)", src=[0,18], dst=[], jump=NONE},
					AssemStore.OPER{assem="sw `s1, -16(`s0)", src=[0,19], dst=[], jump=NONE},
					AssemStore.OPER{assem="sw `s1, -20(`s0)", src=[0,20], dst=[], jump=NONE},
					AssemStore.OPER{assem="sw `s1, -24(`s0)", src=[0,21], dst=[], jump=NONE},
					AssemStore.OPER{assem="sw `s1, -28(`s0)", src=[0,22], dst=[], jump=NONE},
					AssemStore.OPER{assem="sw `s1, -32(`s0)", src=[0,23], dst=[], jump=NONE},
					AssemStore.LABEL{assem="l354:", lab="l354"},
					AssemStore.MOVE{assem="move `d0, `s0", src=0, dst=24},
					AssemStore.MOVE{assem="move `d0, `s0", src=2, dst=25},
					AssemStore.OPER{assem="sw `s0, 0(`s1)", src=[25,24], dst=[], jump=NONE},
					AssemStore.OPER{assem="la `d0, l352", src=[], dst=[26], jump=NONE},
					AssemStore.OPER{assem="la `d0, tig_print", src=[], dst=[27], jump=NONE},
					AssemStore.MOVE{assem="move `d0, `s0", src=26, dst=28},
					AssemStore.MOVE{assem="move `d0, `s0", src=28, dst=2},
					AssemStore.OPER{assem="jal `s0", src=[27,2], dst=[1,6,7,8,9,10,11,12,13,14,15,2,3,4,5], jump=NONE},
					AssemStore.MOVE{assem="move `d0, `s0", src=1, dst=29},
					AssemStore.MOVE{assem="move `d0, `s0", src=29, dst=1},
					AssemStore.OPER{assem="b `j0", src=[], dst=[], jump=SOME["l353"]},
					AssemStore.LABEL{assem="l353:", lab="l353"},
					AssemStore.OPER{assem="lw `d0, -4(`s0)", src=[0], dst=[16], jump=NONE},
					AssemStore.OPER{assem="lw `d0, -8(`s0)", src=[0], dst=[17], jump=NONE},
					AssemStore.OPER{assem="lw `d0, -12(`s0)", src=[0], dst=[18], jump=NONE},
					AssemStore.OPER{assem="lw `d0, -16(`s0)", src=[0], dst=[19], jump=NONE},
					AssemStore.OPER{assem="lw `d0, -20(`s0)", src=[0], dst=[20], jump=NONE},
					AssemStore.OPER{assem="lw `d0, -24(`s0)", src=[0], dst=[21], jump=NONE},
					AssemStore.OPER{assem="lw `d0, -28(`s0)", src=[0], dst=[22], jump=NONE},
					AssemStore.OPER{assem="lw `d0, -32(`s0)", src=[0], dst=[23], jump=SOME["l354"]}])
	val (fgraph, nodes) = MakeGraph.instrs2graph(instrs)
	val (igraph, node2temps) = Liveness.interferenceGraph fgraph
    in
	Liveness.show(TextIO.stdOut, igraph) 
    end
    
end
