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
    structure MoveSet = ListSetFn (struct type ord_key = Move.move
				      val compare = Move.compareMoves
			       end)
    structure RegTable = BinaryMapFn(struct
				 type ord_key = Frame.register
				 val compare = String.compare
				 end)
		     

		    
    type allocation = Frame.register Temp.Table.table
    datatype worklists = WKL of
	     {selectStack: IGraph.node list,
	      coalecsedNodes: IGraph.node list,
	      degreeTable: int IGraph.Table.table,
	      adjTable: IGraph.node list IGraph.Table.table,
	      moveTable: MoveSet.set IGraph.Table.table,
	      simplifyWL: IGraph.node list,
	      spillWL: IGraph.node list,
	      freezeWL: IGraph.node list,
	      activeMoves: MoveSet.set,
	      workListMoves: MoveSet.set}
	     
    val numregs = length Frame.registers
    (*TODO use SML set functors and replace all these functions*)
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
    fun differenceReg (l1, l2) =
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
    fun pop nil = ErrorMsg.impossible "WL is empty"
      | pop (node::tail) = (tail, node)
    
    val str = Int.toString
    fun color {interference as Liveness.IGRAPH{graph, tnode, gtemp, moves},
	       initial, spillCost, registers } =
	let
	    (*
	     simplifyWL: nodeSet
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

	    val nodes = IGraph.nodes graph
	    val precolored = foldl (fn (reg, nodes) =>
				       tnode(reg)::nodes
				       handle TempNotFound => nodes)
				   [] Frame.registersAsTemps
	    val uncolored = difference(nodes,
				       precolored)
	    val adjTable =
		foldl (fn (node, table) => 
			  IGraph.Table.enter(table,
					     node,
					     (IGraph.adj node)))
		      IGraph.Table.empty
		      nodes
	    val emptyMovesTable(*: Move.move list IGraph.Table.table*) = IGraph.Table.empty
	    val moveTable =
		foldl (fn (move as (n1,n2), table) =>
			  let
			      val table' =
				  case IGraph.Table.look(table, n1)
				   of SOME moves => 
				      IGraph.Table.enter
					  (table, n1, MoveSet.add(moves, move))
				    | NONE => IGraph.Table.enter
						  (table, n1,
						   MoveSet.singleton(move))
			      val table'' =
				  case IGraph.Table.look(table, n2)
				   of SOME moves => 
				      IGraph.Table.enter
					  (table, n2, MoveSet.add(moves, move))
				    | NONE => IGraph.Table.enter
						  (table, n2,
						   MoveSet.singleton(move))
			  in
			      table''
			  end)
		      IGraph.Table.empty
		      moves
	    val aliasTable = IGraph.Table.empty
	    val activeMoves = MoveSet.empty
	    val workListMoves = MoveSet.empty
	    val coalescedNodes = []
	    fun nodeMoves (activeMoves, workListMoves, moveTable)
			  node =
		let  
		    val moves = lookup moveTable node
		    val un = MoveSet.union(activeMoves, workListMoves)
		in
		    MoveSet.intersection (moves, un)
		end
		
	    fun moveRelated (activeMoves, workListMoves, moveTable)
			    node =
		let
		    val nmoves = nodeMoves (activeMoves, workListMoves, moveTable) node
		in
		    MoveSet.isEmpty(nmoves)
		end
		
	    (*Precolored nodes have infinite degree*)
	    val precoloredTable = foldl (fn (node, table) =>
					    let
						val degree = 100000000
					    in
						IGraph.Table.enter(table,
								   node,
								   degree)
					    end)
					IGraph.Table.empty
					precolored
					
	    val degreeTable = foldl (fn (node, table) =>
					let
					    val degree =
						length (lookup adjTable node)
					in
					    IGraph.Table.enter(table,
							       node,
							       degree)
					end)
				    precoloredTable
				    uncolored
				    
	    fun makeWorklist (uncolored) = 
		let
		    fun iterate (nil, simplifyWL, spillWL, freezeWL) =
			(simplifyWL, spillWL, freezeWL)
		      | iterate (head::tail, simplifyWL, spillWL, freezeWL) =
			if lookup degreeTable head >= numregs
			then iterate(tail, simplifyWL, head::spillWL, freezeWL)
			else if moveRelated (activeMoves, workListMoves, moveTable) head
			then iterate(tail, simplifyWL, spillWL, head::freezeWL)
			else iterate(tail, head::simplifyWL, spillWL, freezeWL)
		in
		    iterate(uncolored, [], [], [])
		end
		
	    fun print (name, workList) =
		let
		    fun str node =
			(IGraph.nodename node) ^ " "
		    val workListString = String.concat (map str workList)
		in
		    ErrorMsg.error 2 ("The "^name^" worklist string is: " ^ workListString)
		end
		
	    val (simplifyWL, spillWL, freezeWL) = makeWorklist(uncolored)
	    val _ = print ("Simplify", simplifyWL)
	    val _ = print ("Spill", spillWL)
		    
	    fun adjacent (selectStack, coalescedNodes, adjTable) node =
		difference(lookup adjTable node,
			   union(selectStack, coalescedNodes))
		
	    fun enableMoves (activeMoves, workListMoves, moveTable) nodes =
		let 
		    fun enableMove (node,(activeMoves, workListMoves)) =
			let val moves = nodeMoves (activeMoves, workListMoves, moveTable) node
			in 
			    MoveSet.foldl (fn (m, (activeMoves, workListMoves)) =>
				      if MoveSet.member(activeMoves, m)
				      then (MoveSet.delete(activeMoves, m),
					    MoveSet.add(workListMoves, m))
				      else (activeMoves, workListMoves))
				  (activeMoves, workListMoves) moves
			end
		in
		    foldl enableMove (activeMoves, workListMoves) nodes
		end 
	    fun decrementDegree  ({selectStack,
				      coalescedNodes,
				      degreeTable,
				      moveTable,
				      adjTable,
				      simplifyWL,
				      spillWL,
				      freezeWL,
				      activeMoves,
				      workListMoves}) node =
		let
		    val adjNodes = adjacent (selectStack, coalescedNodes, adjTable) node
		    val d = lookup degreeTable node
		    val degreeTable' = enter degreeTable (node, d-1)
		    val (simplifyWL',
			 spillWL',
			 freezeWL',
			 (activeMoves',
			  workListMoves')) =
			if d = numregs
			then if moveRelated (activeMoves, workListMoves, moveTable) node
			     then (simplifyWL,
				   difference(spillWL, [node]),
				   push(freezeWL, node),
				   enableMoves (activeMoves, workListMoves, moveTable)
					       (node::adjNodes))
			     else (union(simplifyWL, [node]),
				   difference(spillWL, [node]),
				   freezeWL,
				   enableMoves (activeMoves, workListMoves, moveTable)
					      (node::adjNodes))
			else (simplifyWL, spillWL,freezeWL,(activeMoves, workListMoves))
		in
		    {selectStack=selectStack,
		     coalescedNodes=coalescedNodes,
		     degreeTable=degreeTable',
		     moveTable=moveTable,
		     adjTable=adjTable,
		     simplifyWL=simplifyWL',
		     spillWL=spillWL',
		     freezeWL=freezeWL',
		     activeMoves=activeMoves',
		     workListMoves=workListMoves'}
		end
		
	    fun simplify (worklists as {selectStack,
					coalescedNodes,
					degreeTable,
					moveTable,
					adjTable,
					simplifyWL,
					spillWL,
					freezeWL,
					activeMoves,
					workListMoves}) =
		let
		    val (simplifyWL', n) = pop simplifyWL
		    val selectStack' = push(selectStack, n)
		    val adjNodes = adjacent (selectStack, coalescedNodes, adjTable) n
		    val {degreeTable=degreeTable', simplifyWL=simplifyWL'',
			 spillWL=spillWL', freezeWL=freezeWL',
			 activeMoves=activeMoves', workListMoves=workListMoves', ...} =
			foldl (fn (node, worklists) =>
				  (decrementDegree worklists node))
			  worklists
			  adjNodes
		in
		    {selectStack=selectStack',
		     coalescedNodes=coalescedNodes,
		     degreeTable=degreeTable',
		     moveTable=moveTable,
		     adjTable=adjTable,
		     simplifyWL=simplifyWL'',
		     spillWL=spillWL',
		     freezeWL=freezeWL',
		     activeMoves=activeMoves',
		     workListMoves=workListMoves'}
		end
	    fun selectSpill ({selectStack,
			      coalescedNodes,
			      degreeTable,
			      moveTable,
			      simplifyWL,
			      adjTable,
			      spillWL,
			      freezeWL,
			      activeMoves,
			      workListMoves}) =
		let
		    (* TODO: we should call spill cost *)
		    val (spillWL', node) = pop spillWL
		    val simplifyWL' = push(simplifyWL, node)
		in
		    {selectStack=selectStack,
		     coalescedNodes=coalescedNodes,
		     degreeTable=degreeTable,
		     moveTable=moveTable,
		     adjTable=adjTable,
		     simplifyWL=simplifyWL',
		     spillWL=spillWL',
		     freezeWL=freezeWL,
		     activeMoves=activeMoves,
		     workListMoves=workListMoves}
		end
	    fun loop (worklists as {selectStack,
				       simplifyWL,
				       spillWL,
				       freezeWL,
				       workListMoves, ...}) =
		let
		    val _ = print ("Simplify2", simplifyWL)
		    val _ = print ("Spill2", spillWL)
		    val _ = print ("Select2", selectStack)
		    val worklists' =
			if not (null simplifyWL)
			then simplify worklists
			else if not (null spillWL)
			then selectSpill worklists
			else worklists
			     
		    val {simplifyWL=simplifyWL',
			 spillWL=spillWL',
			 freezeWL=freezeWL',
			 workListMoves=worklistMoves',
			 selectStack=selectStack', ...} = worklists'
		in
		    if (null simplifyWL') andalso
		       (null spillWL') andalso
		       (null freezeWL') andalso
		       (MoveSet.isEmpty workListMoves)
		    then selectStack'
		    else loop worklists'
		end		    
		
	    val initWorklist =  {selectStack = [],
				coalescedNodes=coalescedNodes,
				degreeTable=degreeTable,
				moveTable=moveTable,
				 adjTable=adjTable,
				simplifyWL=simplifyWL,
				spillWL=spillWL,
				freezeWL=freezeWL,
				activeMoves=activeMoves,
				workListMoves=workListMoves}
		
	    val selectStack = loop initWorklist
(*
	    fun updateRecord {selectStack
			      coalescedNodes
			      degreeTable
			      moveTable
			      simplifyWL
			      spillWL
			      freezeWL
			      activeMoves
			      workListMoves} =
		case *)
					      
	    val _ = print ("Select", selectStack)
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
			    val _ = ErrorMsg.error 2 ("Node: "^(IGraph.nodename head))
			    val _ = ErrorMsg.error 2 ("Adjacent Nodes: "^(Int.toString (length usedColors)))
			    val _ = ErrorMsg.error 2 ("Used colors: "^(String.concat (map (fn s=> s^" ") usedColors)))
			    val okColors = differenceReg(registers, usedColors)
(*			    val _ = ErrorMsg.error 2 ("Length of okColors"^
						      (Int.toString (length okColors))) *)
			    val _ = ErrorMsg.error 2 ("OK colors: "^(String.concat (map (fn s=> s^" ") okColors)))
			    val (color', spilledNodes') = if (null okColors)
					 then (color, head::spilledNodes)
					 else  let val reg = (hd okColors) in
						   (ErrorMsg.error 2 ("Assigning temp "^(Temp.makestring temp)^" register "^reg);
					       (Temp.Table.enter
						   (color, temp, reg),
					      spilledNodes)) end
			in
			    loop(tail, color', spilledNodes')
			end
		in
		    loop(selectStack, initial, [])
		end
	    val (coloring, spilledNodes) = assignColors(selectStack)
	    fun check (activeMoves, workListMoves, moveList, degree) node =
		let
		    val deg = degree(node)
		    val moves = moveList(node)
		    val un = MoveSet.union(workListMoves, activeMoves)
		    val int = MoveSet.intersection(moves, un)
		in
		    if (deg < numregs) andalso (MoveSet.isEmpty int) then ()
		    else ErrorMsg.impossible
			     "SimplifyWL invariant did not hold!"
		end

	    val spilledTemps = map gtemp spilledNodes 
	
	    fun simplifyWLInvariant (simplifyWL, activeMoves, workListMoves, moveList, degree)  =
		app (check (activeMoves, workListMoves, moveList, degree)) simplifyWL

	    fun freezeWLInvariant (freezeWL, activeMoves, workListMoves, moveList, degree) =
		app (check (activeMoves, workListMoves, moveList, degree)) freezeWL
	
	    fun spillWLInvariant (spillWL, degree) =
		app (fn node => if degree(node) >= numregs
				then ()
				else ErrorMsg.impossible
					 "SpillWL invariant did not hold!")
		    spillWL
	    fun degreeInvariant (simplifyWL, spillWL, freezeWL,
				 precolored, adjList, degree) = 
		let
		    fun check node =
			let
			    val un =  union(freezeWL,
					    union(spillWL,
						  union(precolored,
							simplifyWL)))
			    val int = intersect(adjList(node), un)
			in
			    if degree(node) = length (int) then ()
			    else ErrorMsg.impossible
				     "Degree invariant did not hold!"
			end 
		in
		    app check simplifyWL
		end

	    val _ = degreeInvariant (simplifyWL,
				     spillWL,
				     freezeWL,
				     precolored,
				     lookup adjTable,
				     lookup degreeTable)
	    val _ = simplifyWLInvariant (simplifyWL, activeMoves, workListMoves,
					 lookup moveTable,
					 lookup degreeTable)
	    val _ = freezeWLInvariant (freezeWL, activeMoves, workListMoves,
				       lookup moveTable,
				       lookup degreeTable)
	    val _ = spillWLInvariant(spillWL, lookup degreeTable)
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

