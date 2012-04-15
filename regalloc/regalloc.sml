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
    fun str i = if (i < 0) 
		then "-"^(Int.toString (~i))
		else Int.toString i
    fun rewriteProgram (frame, instrs, spills) = 
	let
	    val temps2locals = foldl (fn (t, ma) =>
				   Temp.Table.enter
				       (ma, t, Frame.allocLocal frame true))
			       Temp.Table.empty
			       spills
	    fun lookup temp =
		Temp.table.look(temps2locals, temp)
	    fun replace (old, newtemp) temp =
		if temp = old then newtemp else temp
	    fun rewriteInstrs([], rewrittenInstrs, newTemps) =
		(rev(rewrittenInstrs), newTemps)
	      | rewriteInstrs(instr::instrs, rewritten, newTemps) =
		let
		    fun findReplace (nil) = NONE
		      | findReplace (temp::tail) =
			case lookup temp
			 of SOME (Frame.InFrame offset) => SOME (temp,
							       Temp.newtemp(),
							       offset)
			  | NONE => replaceTemp(tail)
		    fun rewriteUse (instr, oldtemp,
				    newtemp, offset) =
			let 
			    val load =
				A.OPER {assem="lw `d0, "^(str offset)^"`s0\n",
					src=[Frame.FP],
					dst=[temp],
					jump=NONE}
			    val newinstr =
				case instr
				 of A.OPER {assem, src, dst, jump} =>
				    A.OPER {assem,
					    src=map (replace (oldtemp,newtemp)),
					    dst, jump}
				  | A.MOVE {assem, src, dst} =>
				    A.MOVE {assem, replace (oldtemp,newtemp) src, dst, jump}
			in
			    (load, newinstr)
			end
		    fun rewriteDef (instr, newtemp, offset) =
			let
			    val store =
				A.OPER {assem="sw `s0, "^(str offset)^"`d0\n",
					src=[temp],
					dst=[Frame.FP],
					jump=NONE}
			    val newinstr =
				case instr
				 of A.OPER {assem, src, dst, jump} =>
				    A.OPER {assem, src,
					dst=map (replace (oldtemp,newtemp)) dst,
					jump}
				  | A.MOVE {assem, src, dst} =>
				    A.MOVE {assem, replace (oldtemp,newtemp) src, dst, jump}
			in
			    (newinstr, store)
			end
		in 
		    case (instr)
		     of A.OPER {assem, src, dst, jump} =>
			case findReplace (src)
			 of SOME (oldtemp, newtemp, offset) =>
			    let
				val (load, newinstr) =
				    rewriteUse(instr, oldtemp, newtemp, offset)
			    in 
				rewriteInstrs(newinstr::instrs,
					      load::rewritten,
					      newtemp::newTemps)
			    end		  
			  | NONE =>
			    case findReplace (dst)
			     of SOME (oldtemp, newtemp, offset) =>
				let
				    val (newinstr, store) =
					rewriteDef(instr, oldtemp, newtemp, offset)
				in 
				    rewriteInstrs(instrs,
						  store::newinstr::rewritten,
						  newtemp::newTemps)
				end
		  | A.LABEL {assem, lab} =>
		    rewriteInstrs(instrs, instr::rewrittenInstrs, newTemps)
		  | A.MOVE {assem, dst, src} =>
	in
	    (instrs,frame)
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

