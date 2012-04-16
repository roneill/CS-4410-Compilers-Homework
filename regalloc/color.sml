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
    fun degreeInvariant (simplifyWorklist, spillWorklist, precolored, adjList, degree) = 
	let
	    fun check node =
		let
		    val un =  union(spillWorklist,
				    union(precolored, simplifyWorklist))
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
    fun spillWorklistInvariant (spillWorklist, degree) =
	app (fn node => if degree(node) >= numregs
			then ()
			else ErrorMsg.impossible
				 "SpillWorklist invariant did not hold!")
	    spillWorklist
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
				
	    fun makeWorklist (uncolored) =
		let
		    fun iterate (nil, simplifyWorklist, spillWorklist) =
			(simplifyWorklist, spillWorklist)
		      | iterate (head::tail, simplifyWorklist, spillWorklist) =
			if lookup degreeTable head >= numregs
			then iterate(tail, simplifyWorklist, head::spillWorklist)
			else iterate(tail, head::simplifyWorklist, spillWorklist)
		in
		    iterate(uncolored, [], [])
		end
	    val (simplifyWorklist, spillWorklist) = makeWorklist(uncolored)
	    fun adjacent (node, selectStack) = difference(lookup adjTable node,
							  selectStack)
	    fun decrementDegree (node, degreeTable, simplifyWorklist, spillWorklist) =
		let
		    val d = lookup degreeTable node
		    val degreeTable' = enter degreeTable (node, d-1)
		    val (simplifyWorklist', spillWorklist') =
			if d = numregs
			then (union(simplifyWorklist, [node]),
			      difference(spillWorklist, [node]))
			else (simplifyWorklist, spillWorklist)
		in
		    (degreeTable', simplifyWorklist', spillWorklist')
		end 
	    fun simplify (selectStack, simplifyWorklist, spillWorklist, degreeTable) =
		let
		    val (simplifyWorklist', n) = pop simplifyWorklist
		    val selectStack' = push(selectStack, n)
		    val adjNodes = adjacent(n, selectStack')
		    val (degreeTable', simplifyWorklist', spillWorklist') =
			foldl (fn (n, (d,s, swl)) => decrementDegree (n, d, s, swl))
			  (degreeTable, simplifyWorklist', spillWorklist)
			  adjNodes
		in
		    (selectStack', simplifyWorklist', spillWorklist', degreeTable')
		end
	    fun selectSpill (selectStack, simplifyWorklist, spillWorklist, degreeTable) =
		let
		    (* TODO: we should call spill cost *)
		    val (spillWorklist', node) = pop spillWorklist
		    val simplifyWorklist' = push(simplifyWorklist, node)
		in
		    (selectStack, simplifyWorklist', spillWorklist', degreeTable)
		end
	    fun loop (selectStack, simplifyWorklist, spillWorklist, degreeTable) =
		let
		    val (selectStack', simplifyWorklist',
			 spillWorklist', degreeTable') =
			if not (null simplifyWorklist)
			then simplify(selectStack,
				      simplifyWorklist,
				      spillWorklist,
				      degreeTable)
			else if not (null spillWorklist)
			then selectSpill(selectStack,
					 simplifyWorklist,
					 spillWorklist,
					 degreeTable)
			else (selectStack, simplifyWorklist,
			      spillWorklist, degreeTable)			
		in
		    if (null simplifyWorklist) andalso
		       (null spillWorklist)
		    then selectStack'
		    else loop(selectStack', simplifyWorklist',
			      spillWorklist' , degreeTable')
		end
	    val selectStack = loop([], simplifyWorklist,
				   spillWorklist, degreeTable)
	    fun assignColors (selectStack) =
		let
		    fun nodeColor color node =
			Temp.Table.look(color, (gtemp node))
		    fun loop (nil, color, spilledNodes) = (color, spilledNodes)
 		      | loop(head::tail, color, spilledNodes) =
			let
			    val temp = gtemp head
			    val adjNodes = lookup adjTable head
			    val usedColors = List.mapPartial
						 (nodeColor color)
						 adjNodes
			    val okColors = differenceT(registers, usedColors)
(*			    val _ = ErrorMsg.error 2 ("Length of okColors"^
						      (Int.toString (length okColors))) *)
			    val (color', spilledNodes') = if (null okColors)
					 then (color, head::spilledNodes)
					 else (Temp.Table.enter
						   (color, temp, (hd okColors)),
					      spilledNodes)
			in
			    loop(tail, color', spilledNodes')
			end
		in
		    loop(selectStack, initial, [])
		end
	    val (coloring, spilledNodes) = assignColors(selectStack)
	    val spilledTemps = map gtemp spilledNodes 
	    val _ = degreeInvariant (simplifyWorklist,
				     spillWorklist,
				     precolored,
				     lookup adjTable,
				     lookup degreeTable)
	    val _ = simplifyWorklistInvariant (simplifyWorklist,
					       lookup degreeTable)
	    val _ = spillWorklistInvariant(spillWorklist, lookup degreeTable)
	    val _ = ErrorMsg.error 1 "Got to the end"
	in
	    (*Temporary*)
	    (coloring, spilledTemps)
	end
end
(*
1. Implement Color without spilling or coalescing
 a. 
*)

