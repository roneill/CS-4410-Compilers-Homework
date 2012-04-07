signature COMPILER =
sig
    val printIR: unit -> unit
    val printAST: unit -> unit
    val compile: string -> unit
    val testLiveness: unit -> unit
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
					AssemStore.OPER{assem="li `d0, 0", src=[], dst=[2], jump=NONE},
					AssemStore.OPER{assem="li `d0, 0", src=[], dst=[0], jump=NONE},
					AssemStore.LABEL{assem="l1:", lab="l1"},
					AssemStore.OPER{assem="addi `d0, `s0, 1", src=[0], dst=[1], jump=NONE},
					AssemStore.OPER{assem="add `d0, `s0, `s1", src=[2,1], dst=[2], jump=NONE},
					AssemStore.OPER{assem="addi `d0, `s0, 1", src=[1], dst=[0], jump=NONE},
					AssemStore.OPER{assem="bgez `s0, 0", src=[0], dst=[], jump=SOME ["l2","l1"]},
					AssemStore.LABEL{assem="l2:", lab="l2"},
					AssemStore.OPER{assem="move `d0, `s0", src=[2], dst=[], jump=NONE} ])
	val (fgraph, nodes) = MakeGraph.instrs2graph(instrs)
	val (igraph, node2temps) = Liveness.interferenceGraph fgraph
    in
	Liveness.show(TextIO.stdOut, igraph) 
    end
    
end
