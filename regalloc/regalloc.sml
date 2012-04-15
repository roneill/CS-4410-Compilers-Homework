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
		  structure A = Assem
structure IGraph = Graph
    type allocation = Frame.register Temp.Table.table
    fun str i = if (i < 0) 
		then "-"^(Int.toString (~i))
		else Int.toString i
    fun rewriteProgram (frame, instrs, spilledNodes) = 
	let
	    val temps2locals = foldl (fn (t, ma) =>
				   Temp.Table.enter
				       (ma, t, Frame.allocLocal frame true))
			       Temp.Table.empty
			       spilledNodes
	    fun lookup temp = Temp.Table.look(temps2locals, temp)
	    fun rewriteDef (temp) =
		let
		    val offset =
			case lookup temp
			 of SOME access => Frame.getOffset access
			  | NONE => ErrorMsg.impossible "Could not find access for temp"
		in
		    A.OPER {assem="sw `s0, "^(str offset)^"`d0",
			    src=[temp],
			    dst=[Frame.FP],
			    jump=NONE}
		end
	    fun rewriteUse (temp) =
		let
		    val offset =
			case lookup temp
			 of SOME access => Frame.getOffset access
			  | NONE => ErrorMsg.impossible "Could not find access for temp"
		in
		    A.OPER {assem="lw `d0, "^(str offset)^"`s0",
			    src=[Frame.FP],
			    dst=[temp],
			    jump=NONE}
		end
	    fun rewriteInstrs([], rewrittenInstrs) = rev(rewrittenInstrs)
	      | rewriteInstrs(instr::instrs, rewrittenInstrs) =
		case instr
		 of A.OPER {assem, src, dst, jump} =>
		    let
			val usesToRewrite = List.mapPartial (fn t =>
								case lookup t
								 of SOME _ => SOME t
								  | NONE => NONE)
							    src
			val _ = ErrorMsg.error 2 "Got here"
			val useTemp2Temp = foldl
					       (fn (t, ma) =>
						   Temp.Table.enter(ma, t, Temp.newtemp()))
					       Temp.Table.empty
					       usesToRewrite
			val defsToRewrite = List.mapPartial
						(fn t =>
						    case lookup t
						     of SOME _ => SOME t
						      | NONE => NONE)
						dst
			val defTemp2Temp = foldl
					       (fn (t, ma) =>
						   Temp.Table.enter(ma, t, Temp.newtemp()))
					       Temp.Table.empty
					       defsToRewrite
			val useInstrs = map rewriteUse usesToRewrite
			val defInstrs = map rewriteUse defsToRewrite
			val replacedSrc = map (fn t =>
					      case Temp.Table.look(useTemp2Temp, t)
					       of SOME temp => temp
						| NONE => t)
					  src
			val replacedDst = map (fn t =>
						  case Temp.Table.look(useTemp2Temp, t)
						   of SOME temp => temp
						    | NONE => t)
					  dst
			val instr' = A.OPER{assem=assem, src=replacedSrc, dst=replacedDst, jump=jump}
		    in
			ErrorMsg.error 2 ("Length of instrs: "^ (str (length instrs)));
			rewriteInstrs(instrs, useInstrs@[instr']@defInstrs@rewrittenInstrs)
		    end
		  | A.LABEL {assem, lab} =>
		    rewriteInstrs(instrs, instr::rewrittenInstrs)
		  | A.MOVE {assem, dst, src} =>
		    let
			val usesToRewrite =  List.mapPartial (fn t =>
								case lookup t
								 of SOME _ => SOME t
								  | NONE => NONE)
							     [src]
			val useTemp2Temp = foldl
					       (fn (t, ma) =>
						   Temp.Table.enter(ma, t, Temp.newtemp()))
					       Temp.Table.empty
					       usesToRewrite
			val defsToRewrite =  List.mapPartial (fn t =>
								case lookup t
								 of SOME _ => SOME t
								  | NONE => NONE)
							     [dst]
			val defTemp2Temp = foldl
					       (fn (t, ma) =>
						   Temp.Table.enter(ma, t, Temp.newtemp()))
					       Temp.Table.empty
					       defsToRewrite
			val useInstrs = map rewriteUse usesToRewrite
			val defInstrs = map rewriteUse defsToRewrite
			val replacedSrc = map (fn t =>
					      case Temp.Table.look(useTemp2Temp, t)
					       of SOME temp => temp
						| NONE => t)
					      [src]
			val replacedDst = map (fn t =>
						  case Temp.Table.look(useTemp2Temp, t)
						   of SOME temp => temp
						    | NONE => t)
					      [dst]
			val instr' = A.MOVE{assem=assem, dst=(hd (replacedDst)), src=(hd (replacedSrc))}
		    in
			rewriteInstrs(instrs, useInstrs@[instr']@defInstrs@rewrittenInstrs)
		    end
	in
	    (rewriteInstrs(instrs, []), frame)
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
	    else (ErrorMsg.error 2 "Gonna go rewrite some programs";
		  (alloc(rewriteProgram(frame,instrs,spills))))
	end
end
