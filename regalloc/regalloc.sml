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
structure A = Assem
	      
type allocation = Frame.register Temp.Table.table

fun rewriteProgram (frame, instrs, spills) = 
    let
	(* Make a hash table for spilled temps and allocate space on the frame
	for all new temps*)
	val temps2locals = foldl (fn (t, ma) =>
				     Temp.Table.enter
					 (ma, t, Frame.allocLocal frame true))
				 Temp.Table.empty
				 spills
	fun lookup temp =
	    Temp.Table.look (temps2locals, temp)
	fun replace (old:Temp.temp, newtemp:Temp.temp) temp =
	    if temp = old then newtemp else temp

	(* Rewrite the program from the top down using the original instructions
	as a worklist.  Spilled temps are removed from the instruction at the
	top of the worklist one at a time.  Labels and instructions
	with no spilled temps are pushed onto a rewrittenInstrs list*)
					    
	fun rewriteInstrs ([], rewrittenInstrs) =
	    (rev(rewrittenInstrs))
	  | rewriteInstrs (instr::instrs, rewritten) =
	    let
		fun findReplaceTemp (nil) = NONE
		  | findReplaceTemp (temp::tail) =
		    (case (lookup temp)
		      of SOME access => SOME (temp,
					      access)
		       | NONE => findReplaceTemp(tail))
		fun rewriteUse (instr, spillTemp, access) =
		    let
			val newtemp = Temp.newtemp()
			val load = Frame.loadInstr(newtemp, access)
			val newinstr= 
			  case (instr)
			   of A.OPER {assem, src, dst, jump} => 
			      A.OPER {assem=assem,
				      src=(map (replace (spillTemp,newtemp)) src),
				      dst=dst,
				      jump=jump}
			    | A.MOVE {assem, src, dst} =>
			      A.MOVE {assem=assem,
				      src=newtemp,
				      dst=dst}
			    | A.LABEL _ => ErrorMsg.impossible
					       "Trying to rewrite a label"
		    in
			(load, newinstr)
		    end
		fun rewriteDef (instr, spillTemp, access) =
		    let
			val newtemp = Temp.newtemp()
			val store = Frame.storeInstr(newtemp, access)
			val newinstr = 
			    case instr
			     of A.OPER {assem, src, dst, jump} =>
				A.OPER {assem=assem,
					src=src,
					dst=map (replace (spillTemp,newtemp)) dst,
					jump=jump}
			      | A.MOVE {assem, src, dst} =>
				A.MOVE {assem=assem,
					src=replace (spillTemp,newtemp) src,
					dst=dst}
			      | A.LABEL _ => ErrorMsg.impossible
						 "Trying to rewrite a label"
		    in 
			(newinstr, store)
		    end
		fun procInstr (instr, src, dst) =
		    (* Look for spills to replace in the uses first *)
		    (case findReplaceTemp (src)
		      of SOME (spillTemp, access) =>
			 let
			     (*Re-write the instruction with a load from memory
			     into a new temp *)
			     
			     val (load, newinstr) =
				 rewriteUse(instr, spillTemp, access)
			 in 
			     rewriteInstrs(newinstr::instrs,
					   load::rewritten)
			 end		  
		       | NONE =>
			 (* Look for temps to replace in the defs after all
			 spill have been rewritten in the uses *)
			 case findReplaceTemp (dst)
			  of SOME (spillTemp, access) =>
			     let
				 val (newinstr, store) =
				     rewriteDef(instr, spillTemp, access)
			     in 
				 rewriteInstrs(instrs,
					       store::newinstr::rewritten)
			     end
			   | NONE =>
			     rewriteInstrs(instrs,
					   instr::rewritten))
	    in 
		    case (instr)
		     of A.OPER {assem, src, dst, jump} =>
			procInstr (instr, src, dst)		
		      | A.LABEL {assem, lab} =>
			rewriteInstrs(instrs, instr::rewritten)
		      | A.MOVE {assem, dst, src} =>
			procInstr (instr, [src], [dst])
	    end
    in
	rewriteInstrs(instrs, [])
    end

fun alloc (instrs, frame) =
    let
	
	val (fgraph, nodes) = MakeGraph.instrs2graph instrs

	val (igraph as Liveness.IGRAPH{graph, 
				       tnode, 
				       gtemp, 
				       moves}, 
	     liveMap) = Liveness.interferenceGraph fgraph
	val _ = Liveness.show(TextIO.stdOut, igraph)
	val format0 = Assem.format(Frame.tempToString)
	val _ = ErrorMsg.debug "Original: "
	val _ = app (fn i => ErrorMsg.debug (format0 i)) instrs

	val (allocation, spills) = Color.color {interference = igraph,
						initial = Frame.tempMap,
						spillCost = (fn n => 1),
						registers = Frame.registers}

	val format0 = Assem.format((fn t => case Temp.Table.look (allocation, t)
					     of SOME reg => reg
					      | NONE => Temp.makestring (t)))
	val _ = ErrorMsg.debug "Colored: "
	val _ = app (fn i => ErrorMsg.debug (format0 i)) instrs
    in

	if (null spills)
	then (instrs, allocation)
	else (alloc(rewriteProgram(frame,instrs,spills), frame))
    end

end

