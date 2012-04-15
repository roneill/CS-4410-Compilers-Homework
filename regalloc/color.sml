signature COLOR =
sig
    structure Frame: FRAME
    type allocation = Frame.register Temp.Table.table
		      
    val color: { interference: Liveness.igraph,
		 initial: allocation,
		 spillCost: Graph.node -> int,
		 registers: Frame.register list }
	       -> allocation * Temp.temp list
end

structure Color : COLOR = 
struct
    structure Frame = MipsFrame
    structure IGraph = Liveness.IGraph
    type allocation = Frame.register Temp.Table.table

structure RegTable = BinaryMapFn(struct
				     type ord_key = Frame.register
				     val compare = String.compare
				     end)
		      
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
    fun differenceT (l1, l2) =
	let
	    val table = foldl (fn (n,t) => RegTable.insert'((n,()),t))
			      RegTable.empty
			      l2
	    fun  difference' (node, acc) = 
	      	case RegTable.find(table, node)
		 of SOME _ => acc
		  | NONE => node::acc
	    val differences = foldl difference' [] l1
	in
	    differences
	end
		   
    fun push (nodes, node) = node::nodes		    
    fun pop nil = ErrorMsg.impossible "Worklist is empty"
      | pop (node::tail) = (tail, node)

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
    val str = Int.toString
    fun color {interference as Liveness.IGRAPH{graph, tnode, gtemp, moves},
	       initial, spillCost, registers } =
	let 
	    (*
	     simplifyWorklist: nodeSet
             adjSet: (node * node) Set
             adjList: node -> node list
             degree: node -> int
	     precolored: nodeSet
	     *)
	    fun lookup table key =
		case IGraph.Table.look (table, key)
		 of SOME value => value
		  | NONE => ErrorMsg.impossible
				"Key not found in table"
	    fun enter table (key,value) = IGraph.Table.enter(table, key, value) 
	    fun build () =
		let
		    val nodes = IGraph.nodes graph
		    val precolored = foldl (fn (reg, nodes) =>
					       tnode(reg)::nodes
					       handle TempNotFound => nodes)
					   [] Frame.registersAsTemps
		    val uncolored = difference(nodes,
					       precolored)
		    val adjTable = foldl (fn (node, table) => 
					     IGraph.Table.enter(table,
								node,
								(IGraph.adj node)))
					 IGraph.Table.empty
					 nodes
		    val degreeTable = foldl (fn (node, table) =>
						let
						    val degree =
							length (lookup adjTable node)
						in
						    IGraph.Table.enter(table,
								       node,
								       degree)
						end)
				      IGraph.Table.empty
				      nodes
		in
		    {igraph=interference,
		     precolored=precolored,
		     uncolored=uncolored,
		     adjTable=adjTable,
		     degreeTable=degreeTable}
		end
		
	    val {igraph,
		 precolored,
		 uncolored,
		 adjTable,
		 degreeTable} = build()
				
	    fun MakeWorklist (uncolored) =
		let
		    fun iterate (nil, simplifyWorklist) = simplifyWorklist
		      | iterate (head::tail, simplifyWorklist) =
			if lookup degreeTable head >= numregs
			then iterate(tail, simplifyWorklist)
			else iterate(tail, head::simplifyWorklist)
		in
		    iterate(uncolored, [])
		end
	    val simplifyWorklist = MakeWorklist(uncolored)
	    fun adjacent (node, selectStack) = difference(lookup adjTable node,
							  selectStack)
	    fun decrementDegree (node, degreeTable, simplifyWorklist) =
		let
		    val d = lookup degreeTable node
		    val degreeTable' = enter degreeTable (node, d-1)
		    val simplifyWorklist' =
			if d = numregs
			then union(simplifyWorklist, [node])
			else simplifyWorklist
		in
		    (degreeTable', simplifyWorklist')
		end 
	    fun simplify (selectStack, simplifyWorklist, degreeTable) =
		let
		    val (simplifyWorklist', n) = pop simplifyWorklist
		    val selectStack' = push(selectStack, n)
		    val adjNodes = adjacent(n, selectStack')
		    val (degreeTable', simplifyWorklist') =
			foldl (fn (n, (d,s)) => decrementDegree (n, d, s))
			  (degreeTable, simplifyWorklist')
			  adjNodes
		in
		    (selectStack', simplifyWorklist', degreeTable')
		end
	    fun loop (selectStack, nil, degreeTable) = selectStack
	      | loop (selectStack, simplifyWorklist, degreeTable) =
		let
		    val (selectStack', simplifyWorklist', degreeTable') =
			simplify(selectStack, simplifyWorklist, degreeTable)
		in
		    loop(selectStack', simplifyWorklist', degreeTable')
		end
	    val selectStack = loop([], simplifyWorklist, degreeTable)
	    fun assignColors (selectStack) =
		let
		    fun nodeColor color node =
			Temp.Table.look(color, (gtemp node))
		    fun loop (nil, color) = color
 		      | loop(head::tail, color) =
			let
			    val temp = gtemp head
			    val adjNodes = lookup adjTable head
			    val usedColors = List.mapPartial (nodeColor color) adjNodes
			    val okColors = differenceT(registers, usedColors)
			    val color' = if (null okColors)
					 then (ErrorMsg.error 1 "Spill alert bong bong bong";
					       color)
					 else (Temp.Table.enter (color, temp, (hd okColors)))			 
			in
			    loop(tail, color')
			end
		in
		    loop(selectStack, initial)
		end
	    val coloring = assignColors(selectStack)
	
	    val _ = degreeInvariant (simplifyWorklist,
				 precolored,
				 lookup adjTable,
				 lookup degreeTable)
	    val _ = simplifyWorklistInvariant (simplifyWorklist,
					       lookup degreeTable)
	    val _ = ErrorMsg.error 1 "Got to the end"
	in
	    (*Temporary*)
	    (coloring,[])
	end
end
(*
1. Implement Color without spilling or coalescing
 a. 
*)

