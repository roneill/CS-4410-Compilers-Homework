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
    type nodeSet = unit IGraph.Table.table * IGraph.node list
(*
    fun union (l1, l2) =
	let
	    fun union' (nil, table, xs) = (table, xs)
	      | union' (node::tail, table, xs) =
		case IGraph.Table.look(table, node)
		 of SOME _ => union'(tail, table, xs)
		  | NONE =>
		    let
			val table' = IGraph.Table.enter(table, node, ())
			val xs' = node::xs
		    in
			union'(tail, table', xs')
		    end
	    val (table, xs) = union'(l1, IGraph.Table.empty, [])
	    val (table', xs') = union'(l1, table, xs)
	in
	    xs'
	end
*)
    val numregs = length Frame.registers
    fun union (l1, l2) =
	let
	    val table = foldl (fn (n,t) => IGraph.Table.enter'((n,()),t))
			      IGraph.Table.empty
			      l1
	    fun union' (node, unionAcc) = 
	      	case IGraph.Table.look(table, node)
		 of SOME _ => unionAcc
		  | NONE => node::unionAcc
	    val unionAcc= foldl union' l1 l2
	in
	    unionAcc
	end
	
    fun intersect (l1, l2) =
	let
	    val table = foldl (fn (n,t) => IGraph.Table.enter'((n,()),t))
			      IGraph.Table.empty
			      l1
	    fun intersect' (node, intersection) = 
	      	case IGraph.Table.look(table, node)
		 of SOME _ => node::intersection
		  | NONE => intersection
	    val intersection = foldl intersect' [] l2
	in
	    intersection
	end
    (* Compute l1/l2 *)
    fun difference (l1, l2) =
	let
	    val table = foldl (fn (n,t) => IGraph.Table.enter'((n,()),t))
			      IGraph.Table.empty
			      l2
	    fun  difference' (node, acc) = 
	      	case IGraph.Table.look(table, node)
		 of SOME _ => acc
		  | NONE => node::acc
	    val differences = foldl difference' [] l1
	in
	    differences
	end
		
		   
    fun push (node, nodes) = node::nodes		    
    fun pop nil = ErrorMsg.impossible "Worklist is empty"
      | pop (node::tail) = tail
(*
    fun push (nodeSet as (table, nodes), node) =
	case IGraph.Table.look(table, node)
	 of SOME _ => nodeSet
	  | NONE => (IGraph.Table.enter(table, node, ()), node::nodes)
    fun pop (nodeSet as (table, head::tail)) =
	let
	    val table' = IGraph.Table.remove(table, head)
			 handle NotFound => ErrorMsg.impossible "Node not found in worklist"
	in
	    ((table',tail), head)
	end
*)
    fun alloc (instrs, frame) =
	let 
	    (*
	     simplifyWorklist: nodeSet
             adjSet: (node * node) Set
             adjList: node -> node list
             degree: node -> int
	     precolored: nodeSet
	     *)
	    fun degreeInvariant (simplifyWorklist, precolored, adjList, degree) = 
		let
		    fun check node =
			let
			    val un =  union(precolored, simplifyWorklist)
			    val int = intersect(adjList(node), un)
			in
			    if degree(node) = length (int) then ()
			    else ErrorMsg.impossible
				     "Degree invariant did not hold!"
			end 
		in
		    app check simplifyWorklist
		end
	    fun simplifyWorklistInvariant (simplifyWorklist, degree) =
		let
		    fun check node =
			if degree(node) < numregs then ()
			else ErrorMsg.impossible
				 "SimplifyWorklist invariant did not hold!"
		in
		    app check simplifyWorklist
		end
	    fun build (instrs) =
		let
		    val (fgraph, nodes) = MakeGraph.instrs2graph instrs
		    val (igraph as Liveness.IGRAPH{graph, tnode, gtemp, moves},
			 liveMap)
		      = Liveness.interferenceGraph fgraph
		    val precolored = foldl (fn (reg, nodes) =>
					       tnode(reg)::nodes
					       handle TempNotFound => nodes)
					   [] Frame.registersAsTemps
		    val initial = difference(nodes,
					     precolored)
		    val adjTable = foldl (fn (node, table) => 
					     IGraph.Table.enter(table,
								node,
								(IGraph.adj node)))
					 IGraph.Table.empty
					 nodes
		    fun adjList node =
			case IGraph.Table.look (adjTable, node)
			 of SOME nodes => nodes
			  | NONE => ErrorMsg.impossible
					"Node not found in adjacent table"
		    val degreeTable = foldl (fn (node, table) =>
						let
						    val degree =
							length (adjList node)
						in
						    IGraph.Table.enter(table,
								       node,
								       degree)
						end)
				      IGraph.Table.empty
				      nodes
		    fun degree node = case IGraph.Table.look (degreeTable, node)
				       of SOME d => d
					| NONE => ErrorMsg.impossible
					"Node not found in adjacent table"
		in
		    {igraph=igraph,
		     liveMap=liveMap,
		     precolored=precolored,
		     initial=initial,
		     adjList=adjList,
		     degree=degree}
		end
	    val {igraph,
		 liveMap,
		 precolored,
		 initial,
		 adjList,
		 degree} = build(instrs)
	    fun MakeWorklist (initial) =
		let
		    fun iterate (nil, simplifyWorklist) = simplifyWorklist
		      | iterate (head::tail, simplifyWorklist) =
			if degree(head) >= numregs
			then iterate(tail, simplifyWorklist)
			else iterate(tail, head::simplifyWorklist)
		in
		    iterate(initial, [])
		end
	    val simplifyWorklist = MakeWorklist(initial)
	    val _ = degreeInvariant (simplifyWorklist, precolored, adjList, degree)
	    val _ = simplifyWorklistInvariant (simplifyWorklist, degree)
	    val (allocation, temps) = Color.color {interference = igraph,
						   initial = Frame.tempMap,
						   spillCost = (fn n => 1),
						   registers = Frame.registers}
	in
	    (instrs, Frame.tempMap)
	end
end
