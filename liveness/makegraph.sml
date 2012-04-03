
signature MAKEGRAPH =
sig
    structure Flow : FLOW
    val instrs2graph: Assem.instr list ->
		      Flow.flowgraph * Flow.Graph.node list
end

structure MakeGraph: MAKEGRAPH =

struct

structure Flow = Flow
structure A = Assem 

structure LabelNodeMap = BinaryMapFn(struct
				   type ord_key = Temp.label
				   val compare = Temp.compareLabels
				   end)
			 
fun list2set l = Flow.Set.addList(Flow.Set.empty, l)
			 
fun instrs2graph instrs =
    let
	val control = Graph.newGraph()
	(* Loop through each instruction, creating nodes and storing information
	 * in tables as we go along
	 * instrTable: node -> instr map 
	 * label2node: label -> node map
	 * def: node -> def set map
	 * use: node -> use set map
	 * ismove: node -> move map 
	 * labels: list of labels that occur directly before the current 
	 *          instruction 
	 * nodes: stack of nodes in the reverse order from the order in the 
	 *         instruction list *)
	fun makeNodes (nil, instrTable, label2node, def, use, ismove, labels, nodes) =
	    (instrTable, label2node, def, use, ismove, nodes)
	  | makeNodes (instr::tail, instrTable, label2node, def, use, ismove, labels, nodes) =
	    case instr
	     of A.OPER {assem, src, dst, jump} =>
		let
		    val node = Graph.newNode(control)
		    val instrTable' = Graph.Table.enter(instrTable, node, instr)
		    val def' = Graph.Table.enter(def, node, list2set dst)
		    val use' = Graph.Table.enter(use, node, list2set src)
		    val ismove' = Graph.Table.enter(ismove, node, false)
		    val label2node' = foldl (fn (label, table) =>
						LabelNodeMap.insert(table, label, node))
					    label2node
					    labels
		in
		    makeNodes(tail, instrTable', label2node', def', use', ismove', [], node::nodes)
		end
	      | A.LABEL {assem, lab} =>
		makeNodes(tail, instrTable, label2node, def, use, ismove, lab::labels, nodes)
	      | A.MOVE {assem, dst, src} =>
		let
		    val node = Graph.newNode(control)
		    val instrTable' = Graph.Table.enter(instrTable, node, instr)
		    val def' = Graph.Table.enter(def, node, list2set [dst])
		    val use' = Graph.Table.enter(use, node, list2set [src])
		    val ismove' = Graph.Table.enter(ismove, node, true)
		    val label2node' = foldl (fn (label, table) =>
						LabelNodeMap.insert(table, label, node))
					    label2node
					    labels					    
		in
		    makeNodes(tail, instrTable', label2node', def', use', ismove', [], node::nodes)
		end
	val (instrTable, label2node, def, use, ismove, nodes) =
	    makeNodes(instrs,
		      Graph.Table.empty,
		      LabelNodeMap.empty,
		      Graph.Table.empty,
		      Graph.Table.empty,
		      Graph.Table.empty,
		      [],
		      [])
	fun makeEdges (nil) = ()    
	  | makeEdges (n1::nil) = ()
	  | makeEdges (next::prev::nodes) =
	    let
		fun getJumpList(node) =
		    let
			val instr =
			    case Graph.Table.look(instrTable, node)
			     of SOME instr => instr
			      | NONE => ErrorMsg.impossible
		              "Node is not entered into instruction table"
			val jumps = case instr
				     of A.OPER {jump=SOME labels, ...} => labels
				      | _ => []
			fun getNode label =
			    case LabelNodeMap.find(label2node, label)
			     of SOME node => node
			      | NONE => ErrorMsg.impossible
		              "Label is not entered into label->node table"
			val jumpNodes = map getNode jumps	
		    in
			jumpNodes
		    end			  
		val prevJumps = getJumpList(prev)
		val nextJumps = getJumpList(next)
		(* Note :
		 may need to handle case where there are jumps to
			 labels that were not in the instruction list *)
		val _ = map (fn jump => Graph.mk_edge {from=prev, to=jump}) prevJumps
		val _ = map (fn jump => Graph.mk_edge {from=next, to=jump}) nextJumps
		val _ =
		    case prevJumps
		     of nil => Graph.mk_edge {from=prev, to=next}
		      | _ => ()
	    in
		makeEdges(prev::nodes)
	    end			  
	val _ = makeEdges(nodes)
	val flowgraph = Flow.FGRAPH {control=control,
				     def=def,
				     use=use,
				     ismove=ismove}
	fun say s =  TextIO.output(TextIO.stdOut,s)
	fun sayln s= (say s; say "\n")
	
	fun printNodeInstr (node) =
	    let
		val instr = getOpt(Graph.Table.look(instrTable, node), A.OPER{assem="",src=[],dst=[],jump=NONE})
		val assemString =
		    case instr
		     of A.OPER {assem=assem, ...} => assem
		      | A.MOVE {assem=assem, ...} => assem
		      | _ => ""
		val nodeString = Graph.nodename(node)
		val succ = Graph.succ(node)
		val succString = "{"^(String.concat(map (fn n => (Graph.nodename n)^" ") succ))^"}"
	    in
		sayln (nodeString^": "^assemString^succString)
	    end
	val _ = app printNodeInstr (rev nodes)
    in
	(flowgraph, Graph.nodes control)
    end
end


