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
	val temps2locals = foldl (fn (t, ma) =>
				     Temp.Table.enter
					 (ma, t, Frame.allocLocal frame true))
				 Temp.Table.empty
				 spills
	fun lookup temp =
	    Temp.Table.look(temps2locals, temp)
	fun replace (old:Temp.temp, newtemp:Temp.temp) temp =
	    if temp = old then newtemp else temp

	(*
	 This function processes the spills in the use set and def
	 set separately.  Unfortunately it does not generate efficient
	 code for an instruction that uses a spilled temp in both the
	 use and the def.  Separate new temps are used for the def and
	 the use
	 *)
					    
	fun rewriteInstrs([], rewrittenInstrs) =
	    (rev(rewrittenInstrs))
	  | rewriteInstrs(instr::instrs, rewritten) =
	    let
		fun findReplaceTemp (nil) = NONE
		  | findReplaceTemp(temp::tail) =
		    (case (lookup temp)
		      of SOME access => SOME (temp,
					      Temp.newtemp(),
					      access)
		       | NONE => findReplaceTemp(tail))
		fun rewriteUse (instr, oldtemp,
				newtemp, access) =
		    let 
			val load = Frame.loadInstr(newtemp, access)
			val newinstr= 
			  case (instr)
			   of A.OPER {assem, src, dst, jump} => 
			      A.OPER {assem=assem,
				      src=(map (replace (oldtemp,newtemp)) src),
				      dst=dst,
				      jump=jump}
			    | A.MOVE {assem, src, dst} =>
			      A.MOVE {assem=assem,
				      src=newtemp,
				      dst=dst}
			    | A.LABEL _ => ErrorMsg.impossible "Trying to rewrite a label"
		    in
			(load, newinstr)
		    end
		fun rewriteDef (instr, oldtemp,newtemp, access) =
		    let
			val store = Frame.storeInstr(newtemp, access)
			val newinstr = 
			    case instr
			     of A.OPER {assem, src, dst, jump} =>
				A.OPER {assem=assem,
					src=src,
					dst=map (replace (oldtemp,newtemp)) dst,
					jump=jump}
			      | A.MOVE {assem, src, dst} =>
				A.MOVE {assem=assem,
					src=replace (oldtemp,newtemp) src,
					dst=dst}
			      | A.LABEL _ => ErrorMsg.impossible "Trying to rewrite a label"
		    in 
			(newinstr, store)
		    end
		fun procInstr (instr, src, dst) =
		    (case findReplaceTemp (src)
		      of SOME (oldtemp, newtemp, access) =>
			 let
			     val (load, newinstr) =
				 rewriteUse(instr, oldtemp, newtemp, access)
			 in 
			     rewriteInstrs(newinstr::instrs,
					   load::rewritten)
			 end		  
		       | NONE =>
			 case findReplaceTemp (dst)
			  of SOME (oldtemp, newtemp, access) =>
			     let
				 val (newinstr, store) =
				     rewriteDef(instr, oldtemp, newtemp, access)
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
	val (igraph, liveMap) = Liveness.interferenceGraph fgraph
				
	val (allocation, spills) = Color.color {interference = igraph,
						initial = Frame.tempMap,
						spillCost = (fn n => 1),
						registers = Frame.registers}
	val _ = ErrorMsg.error 2 ("Spills "^(Int.toString (length spills)))
    in
	if (null spills)
	then (instrs, allocation)
	else (alloc(rewriteProgram(frame,instrs,spills), frame))
    end

end

