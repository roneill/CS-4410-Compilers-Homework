signature REG_ALLOC = 
sig
    structure Frame : FRAME

    type allocation = Frame.register Temp.Table.table
    val alloc : Assem.instr list * Frame.frame -> 
		Assem.instr list * allocation
end

structure RegAlloc : REG_ALLOC =
struct

structure Frame = MipsFrame
structure IGraph = Graph
    type allocation = Frame.register Temp.Table.table
    fun rewriteProgram (frame, instrs, spilledNodes,
			Liveness.IGRAPH{graph, tnode, gtemp, moves},
			Flow.FGRAPH {control, def, use, ismove})
	let
	    val spilledTemps = map gtemp spilledNodes 
	in
	end
    fun alloc (instrs, frame) =
	let 
	    val (fgraph, nodes) = MakeGraph.instrs2graph instrs
	    val (igraph, liveMap) = Liveness.interferenceGraph fgraph

	    val (allocation, spills) = Color.color {interference = igraph,
						   initial = Frame.tempMap,
						   spillCost = (fn n => 1),
						   registers = Frame.registers}
	in
	    if (null spills)
	    then (instrs, allocation)
	    else (alloc(rewriteProgram(frame,instrs,spills)))
	end
end

