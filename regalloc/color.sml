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
structure Move = NodePair
structure IGraph = Liveness.IGraph
structure MoveSet = ListSetFn (struct type ord_key = Move.pair
				      val compare = Move.comparePairs
			       end)
structure RegTable = BinaryMapFn(struct
				 type ord_key = Frame.register
				 val compare = String.compare
				 end)
structure Adj = NodePair		     

		     
type allocation = Frame.register Temp.Table.table
datatype worklists = WKL of
	 {selectStack: IGraph.node list,
	  coalecsedNodes: IGraph.node list,
	  degreeTable: int IGraph.Table.table,
	  adjTable: IGraph.node list IGraph.Table.table,
	  adjSetTable: unit Adj.Table.map,
	  moveTable: MoveSet.set IGraph.Table.table,
	  aliasTable: IGraph.node IGraph.Table.table,
	  simplifyWL: IGraph.node list,
	  spillWL: IGraph.node list,
	  freezeWL: IGraph.node list,
	  activeMoves: MoveSet.set,
	  workListMoves: MoveSet.set,
	  frozenMoves: MoveSet.set,
	  constrainedMoves: MoveSet.set,
	  coalescedMoves: MoveSet.set}
	 
val numregs = length Frame.registers

fun member items item =
    List.exists (fn i => IGraph.eq(i, item)) items
    
(*TODO use SML set functors and replace all these functions*)
fun union (l1, l2) =
    let
	val table = foldl (fn (n,t) => IGraph.Table.enter'((n,()),t))
			  IGraph.Table.empty
			  l1
	fun unionf (node, unionAcc) = 
	    case IGraph.Table.look(table, node)
	     of SOME _ => unionAcc
	      | NONE => node::unionAcc
	val unionAcc= foldl unionf l1 l2
    in
	unionAcc
    end
    
fun intersect (l1, l2) =
    let
	val table = foldl (fn (n,t) => IGraph.Table.enter'((n,()),t))
			  IGraph.Table.empty
			  l1
	fun intersectf (node, intersection) = 
	    case IGraph.Table.look(table, node)
	     of SOME _ => node::intersection
	      | NONE => intersection
	val intersection = foldl intersectf [] l2
    in
	intersection
    end
(* Compute l1/l2 *)
fun difference (l1, l2) =
    let
	val table = foldl (fn (n,t) => IGraph.Table.enter'((n,()),t))
			  IGraph.Table.empty
			  l2
	fun  differencef (node, acc) = 
	     case IGraph.Table.look(table, node)
	      of SOME _ => acc
	       | NONE => node::acc
	val differences = foldl differencef [] l1
    in
	differences
    end
fun differenceReg (l1, l2) =
    let
	val table = foldl (fn (n,t) => RegTable.insert'((n,()),t))
			  RegTable.empty
			  l2
	fun  differencef (node, acc) = 
	     case RegTable.find(table, node)
	      of SOME _ => acc
	       | NONE => node::acc
	val differences = foldl differencef [] l1
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
	val _ = ErrorMsg.debug "In Color\n"
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
			
	fun lookupSet table key =
	    case IGraph.Table.look (table, key)
	     of SOME value => value
	      | NONE => MoveSet.empty

	fun enter table (key,value) = IGraph.Table.enter(table, key, value) 

	fun inAdjSet table key =
	    case Adj.Table.find (table, key)
	     of SOME _ => true
	      | NONE => false
			
	fun print (name, workList) =
	    let
		fun str node =
		    (IGraph.nodename node) ^ " "
		val workListString = String.concat (map str workList)
	    in
		ErrorMsg.debug ("The "^name^" worklist is: " ^ workListString)
	    end
	    
	fun printMoves (name, moves) =
	    let
		fun str (n1, n2) =
		    String.concat ["(",(IGraph.nodename n1),",",IGraph.nodename n2,") "]
		val workListString = String.concat (map str moves)
	    in
		ErrorMsg.debug ("The "^name^" is: " ^ workListString)
	    end
	val _ = printMoves ("Moves", moves) 
	fun simplifyWLInvariant (simplifyWL, activeMoves,
				 workListMoves, moveList, degree)  =
	    let
		fun check node =
		    let
			val deg = degree(node)
			val moves = moveList(node)
			val un = MoveSet.union(workListMoves, activeMoves)
			val int = MoveSet.intersection(moves, un)
		    in
			if (deg < numregs) andalso (MoveSet.isEmpty int) then ()
			else ErrorMsg.impossible
				 ("SimplifyWL invariant did not hold! degree:"^(Int.toString deg))
		    end
	    in 
		app check simplifyWL
	    end
	    
	fun freezeWLInvariant (freezeWL, activeMoves, workListMoves, moveList, degree) =
	    let
		fun check node =
		    let
			val deg = degree(node)
			val moves = moveList(node)
			val un = MoveSet.union(workListMoves, activeMoves)
			val int = MoveSet.intersection(moves, un)
		    in
			if (deg < numregs) andalso not (MoveSet.isEmpty int) then ()
			else ErrorMsg.impossible
				 "FreezeWL invariant did not hold!"
		    end
	    in 
		app check freezeWL
	    end 
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
	    
	val precolored = foldl (fn (reg, nodes) =>
				   tnode(reg)::nodes
				   handle TempNotFound => nodes)
			       [] Frame.registersAsTemps

	val nodes = IGraph.nodes graph

	val uncolored = difference(nodes,
				   precolored)
			
	fun nodeMoves (activeMoves, workListMoves, moveTable)
		      node =
	    let  
		val moves = lookupSet moveTable node
		val _ = printMoves ("Move Looked up for "^(IGraph.nodename node),MoveSet.listItems moves)
		val un = MoveSet.union(activeMoves, workListMoves)
	    in
		MoveSet.intersection (moves, un)
	    end
	    
	fun moveRelated (activeMoves, workListMoves, moveTable)
			node =
	    let
		val nmoves = nodeMoves (activeMoves, workListMoves, moveTable) node
	    in
		not (MoveSet.isEmpty(nmoves))
	    end
	    
	fun OK (t, r, degree, inAdjSet) =
	    degree(t) < numregs orelse
	    member precolored t orelse
	    inAdjSet (t, r)
			     
	fun conservative (nodes, degree) =
	    let
		val k = foldl (fn (n, k) =>
    				  if degree(n) >= numregs
	       			  then k + 1
				  else k)
			      0
			      nodes
	    in
		k < numregs
	    end
	    
	fun getAlias (coalescedNodes, alias) n =
	    if member coalescedNodes n
	    then getAlias (coalescedNodes, alias) (alias(n))
	    else n
		 
	fun freezeMoves {selectStack,
			 coalescedNodes,
			 degreeTable,
			 moveTable,
			 adjTable,
			 adjSetTable,
			 aliasTable,
			 simplifyWL,
			 spillWL,
			 freezeWL,
			 activeMoves,
			 workListMoves,
			 frozenMoves,
			 constrainedMoves,
			 coalescedMoves}
			node =
	    let
		val moves = nodeMoves (activeMoves, workListMoves, moveTable)
				      node
		val (activeMoves,
		     frozenMoves,
		     freezeWL,
		     simplifyWL) =

		    MoveSet.foldl (fn (m as (x,y), (activeMoves,
						    frozenMoves,
						    freezeWL,
						    simplifyWL)) =>
			  let
			      val aliasx = getAlias (coalescedNodes,
						     lookup aliasTable) x
			      val aliasy = getAlias (coalescedNodes,
						     lookup aliasTable) y
			      val v = if (IGraph.eq (aliasx, aliasy))
				      then aliasx
				      else aliasy
			      val vmoves = nodeMoves (activeMoves,
						      workListMoves,
						      moveTable) v
			      val (freezeWL, simplifyWL) =
				  if (MoveSet.isEmpty(vmoves) andalso
				      (lookup degreeTable v) < numregs)
				  then (difference(freezeWL, [v]),
					(v::simplifyWL))
				  else (freezeWL, simplifyWL)
			      val activeMoves = MoveSet.delete(activeMoves, m)
			      val frozenMoves = MoveSet.add(frozenMoves,m)
			  in
			      (activeMoves, frozenMoves, freezeWL, simplifyWL)
			  end)
			  (activeMoves, frozenMoves, freezeWL, simplifyWL)
			  moves
	    in 
		{selectStack=selectStack,
		 coalescedNodes=coalescedNodes,
		 degreeTable=degreeTable,
		 moveTable=moveTable,
		 adjTable=adjTable,
		 adjSetTable=adjSetTable,
		 aliasTable=aliasTable,
		 simplifyWL=simplifyWL,
		 spillWL=spillWL,
		 freezeWL=freezeWL,
		 activeMoves=activeMoves,
		 workListMoves=workListMoves,
		 frozenMoves=frozenMoves,
		 constrainedMoves=constrainedMoves,
		 coalescedMoves=coalescedMoves}
	    end

	fun freeze {selectStack,
		    coalescedNodes,
		    degreeTable,
		    moveTable,
		    adjTable,
		    adjSetTable,
		    aliasTable,
		    simplifyWL,
		    spillWL,
		    freezeWL,
		    activeMoves,
		    workListMoves,
		    frozenMoves,
		    constrainedMoves,
		    coalescedMoves} =
	    let
		val _ = ErrorMsg.debug "In Freeze"
		val (freezeWL,u) = pop freezeWL
		val simplifyWL = push (simplifyWL, u)
		val freezeMoves = freezeMoves {selectStack=selectStack,
						coalescedNodes=coalescedNodes,
						degreeTable=degreeTable,
						moveTable=moveTable,
						adjTable=adjTable,
						adjSetTable=adjSetTable,
						aliasTable=aliasTable,
						simplifyWL=simplifyWL,
						spillWL=spillWL,
						freezeWL=freezeWL,
						activeMoves=activeMoves,
						workListMoves=workListMoves,
						frozenMoves=frozenMoves,
						constrainedMoves=constrainedMoves,
						coalescedMoves=coalescedMoves}
	    in
		freezeMoves u
	    end

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
	    
	fun decrementDegree {selectStack,
			     coalescedNodes,
			     degreeTable,
			     moveTable,
			     adjTable,
			       adjSetTable,
			       aliasTable,
			       simplifyWL,
			       spillWL,
			       freezeWL,
			       activeMoves,
			       workListMoves,
			       frozenMoves,
			       constrainedMoves,
			       coalescedMoves} node =
	    let
		val adjNodes = adjacent (selectStack, coalescedNodes, adjTable) node
		val d = lookup degreeTable node
		val degreeTable = enter degreeTable (node, d-1)
		val (simplifyWL,
		     spillWL,
		     freezeWL,
		     (activeMoves,
		      workListMoves)) =
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
		 degreeTable=degreeTable,
		 moveTable=moveTable,
		 adjTable=adjTable,
		 adjSetTable=adjSetTable,
		 aliasTable=aliasTable,
		 simplifyWL=simplifyWL,
		 spillWL=spillWL,
		 freezeWL=freezeWL,
		 activeMoves=activeMoves,
		 workListMoves=workListMoves,
		 frozenMoves=frozenMoves,
		 constrainedMoves=constrainedMoves,
		 coalescedMoves=coalescedMoves}
	    end
	    
	fun combine (worklists as {selectStack,
				  coalescedNodes,
				  degreeTable,
				  moveTable,
				  adjTable,
				  adjSetTable,
				  aliasTable,
				  simplifyWL,
				  spillWL,
				  freezeWL,
				  activeMoves,
				  workListMoves,
				  frozenMoves,
				  constrainedMoves,
				  coalescedMoves})
		    (u, v) =
	    let
		val _ = ErrorMsg.debug "In combine"
		fun addEdge (degreeTable, adjTable, adjSetTable) (u, v) =
		    let
			val adjSetTable = if not (inAdjSet adjSetTable (u,v)) andalso
					      not (IGraph.eq (u,v))
					   then Adj.Table.insert(adjSetTable, (u,v), ())
					   else adjSetTable
			val adjU = lookup adjTable u
			val adjV = lookup adjTable v
			val degU = lookup degreeTable u
			val degV = lookup degreeTable v
			val (adjTable, degreeTable) =
			    if not (member precolored u)
			    then (IGraph.Table.enter(adjTable, u, v::adjU),
				  IGraph.Table.enter(degreeTable, u, degU+1))
			    else (adjTable, degreeTable)
			val (adjTable, degreeTable) =
			    if not (member precolored v)
			    then (IGraph.Table.enter(adjTable, v, u::adjV),
				  IGraph.Table.enter(degreeTable, v, degV+1))
			    else (adjTable, degreeTable)
		    in
			(degreeTable, adjTable, adjSetTable)
		    end 
		val nodeMoves = nodeMoves (activeMoves,
					   workListMoves,
					   moveTable)
		val (freezeWL, spillWL) =
		    if member freezeWL v
		    then (difference(freezeWL,[v]), spillWL)
		    else (freezeWL, difference(spillWL,[v]))
		val coalescedNodes = v::coalescedNodes
		val aliasTable = IGraph.Table.enter(aliasTable, v, u)
		val moveTable =
		    let 
			val nodeMovesu = nodeMoves u
			val nodeMovesv = nodeMoves v
			val un = MoveSet.union(nodeMovesu, nodeMovesv)
		    in
			IGraph.Table.enter(moveTable, u, un)
		    end
		val (activeMoves, workListMoves) =
		    enableMoves (activeMoves, workListMoves, moveTable) [v]
		val adjNodes = adjacent (selectStack, coalescedNodes, adjTable) v
		val {selectStack,
		     coalescedNodes,
		     degreeTable,
		     moveTable,
		     adjTable,
		     adjSetTable,
		     aliasTable,
		     simplifyWL,
		     spillWL,
		     freezeWL,
		     activeMoves,
		     workListMoves,
		     frozenMoves,
		     constrainedMoves,
		     coalescedMoves} =
		    foldl (fn (t, {selectStack,
				   coalescedNodes,
				   degreeTable,
				   moveTable,
				   adjTable,
				   adjSetTable,
				   aliasTable,
				   simplifyWL,
				   spillWL,
				   freezeWL,
				   activeMoves,
				   workListMoves,
				   frozenMoves,
				   constrainedMoves,
				   coalescedMoves}) =>
			      let
				  val (degreeTable,adjTable,adjSetTable) =
				      addEdge (degreeTable,
					       adjTable,
					       adjSetTable) (t, u)
				  val worklists = decrementDegree
						       {selectStack=selectStack,
							coalescedNodes=coalescedNodes,
							degreeTable=degreeTable,
							moveTable=moveTable,
							adjTable=adjTable,
							adjSetTable=adjSetTable,
							aliasTable=aliasTable,
							simplifyWL=simplifyWL,
							spillWL=spillWL,
							freezeWL=freezeWL,
							activeMoves=activeMoves,
							workListMoves=workListMoves,
							frozenMoves=frozenMoves,
							constrainedMoves=constrainedMoves,
							coalescedMoves=coalescedMoves}
						       t
			      in
				  worklists
			      end )
			  {selectStack=selectStack,
			   coalescedNodes=coalescedNodes,
			   degreeTable=degreeTable,
			   moveTable=moveTable,
			   adjTable=adjTable,
			   adjSetTable=adjSetTable,
			   aliasTable=aliasTable,
			   simplifyWL=simplifyWL,
			   spillWL=spillWL,
			   freezeWL=freezeWL,
			   activeMoves=activeMoves,
			   workListMoves=workListMoves,
			   frozenMoves=frozenMoves,
			   constrainedMoves=constrainedMoves,
			   coalescedMoves=coalescedMoves}
			  adjNodes
	
		val (freezeWL, spillWL) =
		    if lookup degreeTable (u) >= numregs
		       andalso
		       member freezeWL u
		    then
			let
			    val _ = ErrorMsg.debug ("in combine adding to spillWL: "^(IGraph.nodename u))
			    val freezeWL = difference (freezeWL, [u])
			    val spillWL = u::spillWL
			in
			    (freezeWL, spillWL)
			end
		    else (freezeWL, spillWL)
	    in
		{selectStack=selectStack,
		 coalescedNodes=coalescedNodes,
		 degreeTable=degreeTable,
		 moveTable=moveTable,
		 adjTable=adjTable,
		 adjSetTable=adjSetTable,
		 aliasTable=aliasTable,
		 simplifyWL=simplifyWL,
		 spillWL=spillWL,
		 freezeWL=freezeWL,
		 activeMoves=activeMoves,
		 workListMoves=workListMoves,
		 frozenMoves=frozenMoves,
		 constrainedMoves=constrainedMoves,
		 coalescedMoves=coalescedMoves}
	    end
	    
	fun simplify (worklists as {selectStack,
				    coalescedNodes,
				    degreeTable,
				    moveTable,
				    adjTable,
				    adjSetTable,
				    aliasTable,
				    simplifyWL,
				    spillWL,
				    freezeWL,
				    activeMoves,
				    workListMoves,
				    frozenMoves,
				    constrainedMoves,
				    coalescedMoves}) =
	    let
		val _ = ErrorMsg.debug "In simplify"
		val (simplifyWL, n) = pop simplifyWL
		val selectStack = push(selectStack, n)
		val adjNodes = adjacent (selectStack, coalescedNodes, adjTable) n
		val {selectStack=selectStack,
		     coalescedNodes=coalescedNodes,
		     degreeTable=degreeTable,
		     moveTable=moveTable,
		     adjTable=adjTable,
		     adjSetTable=adjSetTable,
		     aliasTable=aliasTable,
		     simplifyWL=simplifyWL,
		     spillWL=spillWL,
		     freezeWL=freezeWL,
		     activeMoves=activeMoves,
		     workListMoves=workListMoves,
		     frozenMoves=frozenMoves,
		     constrainedMoves=constrainedMoves,
		     coalescedMoves=coalescedMoves} =
		    foldl (fn (node, worklists) =>
			      (decrementDegree worklists node))
			  {selectStack=selectStack,
			   coalescedNodes=coalescedNodes,
			   degreeTable=degreeTable,
			   moveTable=moveTable,
			   adjTable=adjTable,
			   adjSetTable=adjSetTable,
			   aliasTable=aliasTable,
			   simplifyWL=simplifyWL,
			   spillWL=spillWL,
			   freezeWL=freezeWL,
			   activeMoves=activeMoves,
			   workListMoves=workListMoves,
			   frozenMoves=frozenMoves,
			   constrainedMoves=constrainedMoves,
			   coalescedMoves=coalescedMoves}
			  adjNodes
	    in
		{selectStack=selectStack,
		 coalescedNodes=coalescedNodes,
		 degreeTable=degreeTable,
		 moveTable=moveTable,
		 adjTable=adjTable,
		 adjSetTable=adjSetTable,
		 aliasTable=aliasTable,
		 simplifyWL=simplifyWL,
		 spillWL=spillWL,
		 freezeWL=freezeWL,
		 activeMoves=activeMoves,
		 workListMoves=workListMoves,
		 frozenMoves=frozenMoves,
		 constrainedMoves=constrainedMoves,
		 coalescedMoves=coalescedMoves}
	    end
	fun selectSpill ({selectStack,
			  coalescedNodes,
			  degreeTable,
			  moveTable,
			  aliasTable,
			  simplifyWL,
			  adjTable,
			  adjSetTable,
			  spillWL,
			  freezeWL,
			  activeMoves,
			  workListMoves,
			  frozenMoves,
			  constrainedMoves,
			  coalescedMoves}) =
	    let
		(* TODO: we should call spill cost *)
		val (spillWL, node) = pop spillWL
		val simplifyWL = push(simplifyWL, node)
	    in
		freezeMoves {selectStack=selectStack,
			     coalescedNodes=coalescedNodes,
			     degreeTable=degreeTable,
			     moveTable=moveTable,
			     adjTable=adjTable,
			     adjSetTable=adjSetTable,
			     aliasTable=aliasTable,
			     simplifyWL=simplifyWL,
			     spillWL=spillWL,
			     freezeWL=freezeWL,
			     activeMoves=activeMoves,
			     workListMoves=workListMoves,
			     frozenMoves=frozenMoves,
			     constrainedMoves=constrainedMoves,
			     coalescedMoves=coalescedMoves} node
	    end
	fun coalesce {selectStack,
		      coalescedNodes,
		      degreeTable,
		      moveTable,
		      adjTable,
		      adjSetTable,
		      aliasTable,
		      simplifyWL,
		      spillWL,
		      freezeWL,
		      activeMoves,
		      workListMoves,
		      frozenMoves,
		      constrainedMoves,
		      coalescedMoves} =
	    let
		val _ = ErrorMsg.debug "In coalesce"
		fun head se =
		    let
			val l = MoveSet.listItems se
			val h = hd l
		    in
			(MoveSet.delete(se, h), h)
		    end
		val (workListMoves, m as (x, y)) = head workListMoves
		fun addWorklist (freezeWL, simplifyWL, degreeTable) u =
		    let
			val moveRelated = moveRelated (activeMoves, workListMoves, moveTable)
			val degree = lookup degreeTable
		    in
			if not (member precolored u) andalso
			   not (moveRelated (u)) andalso
			   degree(u) < numregs
			then (ErrorMsg.debug ("in addWorklist adding to simplifyWL: "^(IGraph.nodename u)); (difference(freezeWL, [u]),
			      push(simplifyWL, u)))
			else (freezeWL, simplifyWL)
		    end 
		val getAlias = getAlias (coalescedNodes, lookup aliasTable)
		val x = getAlias x
		val y = getAlias y
		val (u, v) = if member precolored y
			     then (y, x)
			     else (x, y)
		val adjacent = adjacent (selectStack, coalescedNodes, adjTable) 
	    in 
		if IGraph.eq(u, v)
		then let
			val coalescedMoves = MoveSet.add(coalescedMoves,m)
			val (freezeWL, simplifyWL) = addWorklist (freezeWL, simplifyWL, degreeTable) u 
		    in
			{selectStack=selectStack,
			 coalescedNodes=coalescedNodes,
			 degreeTable=degreeTable,
			 moveTable=moveTable,
			 adjTable=adjTable,
			 adjSetTable=adjSetTable,
			 aliasTable=aliasTable,
			 simplifyWL=simplifyWL,
			 spillWL=spillWL,
			 freezeWL=freezeWL,
			 activeMoves=activeMoves,
			 workListMoves=workListMoves,
			 frozenMoves=frozenMoves,
			 constrainedMoves=constrainedMoves,
			 coalescedMoves=coalescedMoves} 
		    end
		else if (member precolored v) orelse
			(inAdjSet adjSetTable (u,v))
		then let
			val _ = ErrorMsg.debug ("Constrain due to "^(if (member precolored v)
								       then "precolored"
								       else "adjacent")^String.concat ["(",(IGraph.nodename u),",",IGraph.nodename v,") "])
			val constrainedMoves = MoveSet.add(constrainedMoves, m)
			val (freezeWL, simplifyWL) = addWorklist (freezeWL, simplifyWL, degreeTable) u
			val (freezeWL, simplifyWL) = addWorklist (freezeWL, simplifyWL, degreeTable) v
		    in 
			{selectStack=selectStack,
			 coalescedNodes=coalescedNodes,
			 degreeTable=degreeTable,
			 moveTable=moveTable,
			 adjTable=adjTable,
			 adjSetTable=adjSetTable,
			 aliasTable=aliasTable,
			 simplifyWL=simplifyWL,
			 spillWL=spillWL,
			 freezeWL=freezeWL,
			 activeMoves=activeMoves,
			 workListMoves=workListMoves,
			 frozenMoves=frozenMoves,
			 constrainedMoves=constrainedMoves,
			 coalescedMoves=coalescedMoves}
		    end
		else if (member precolored u) andalso
			(List.all (fn t => OK(t, u,
					 lookup degreeTable,
					 inAdjSet adjSetTable)) (adjacent v)) orelse
			not (member precolored u)  andalso
			conservative(union((adjacent u), (adjacent v)),
				     lookup degreeTable)
		then let
			val coalescedMoves = MoveSet.add(coalescedMoves,m)
			val {selectStack,
			     coalescedNodes,
			     degreeTable,
			     moveTable,
			     adjTable,
			     adjSetTable,
			     aliasTable,
			     simplifyWL,
			     spillWL,
			     freezeWL,
			     activeMoves,
			     workListMoves,
			     frozenMoves,
			     constrainedMoves,
			     coalescedMoves} = combine {selectStack=selectStack,
							coalescedNodes=coalescedNodes,
							degreeTable=degreeTable,
							moveTable=moveTable,
							adjTable=adjTable,
							adjSetTable=adjSetTable,
							aliasTable=aliasTable,
							simplifyWL=simplifyWL,
							spillWL=spillWL,
							freezeWL=freezeWL,
							activeMoves=activeMoves,
							workListMoves=workListMoves,
							frozenMoves=frozenMoves,
							constrainedMoves=constrainedMoves,
							coalescedMoves=coalescedMoves}
						       (u,v)
			val (freezeWL, simplifyWL) = addWorklist (freezeWL, simplifyWL, degreeTable) u
		    in
			{selectStack=selectStack,
			 coalescedNodes=coalescedNodes,
			 degreeTable=degreeTable,
			 moveTable=moveTable,
			 adjTable=adjTable,
			 adjSetTable=adjSetTable,
			 aliasTable=aliasTable,
			 simplifyWL=simplifyWL,
			 spillWL=spillWL,
			 freezeWL=freezeWL,
			 activeMoves=activeMoves,
			 workListMoves=workListMoves,
			 frozenMoves=frozenMoves,
			 constrainedMoves=constrainedMoves,
			 coalescedMoves=coalescedMoves}
		    end
		else let
			val activeMoves = MoveSet.add(activeMoves, m)
		    in
			{selectStack=selectStack,
			 coalescedNodes=coalescedNodes,
			 degreeTable=degreeTable,
			 moveTable=moveTable,
			 adjTable=adjTable,
			 adjSetTable=adjSetTable,
			 aliasTable=aliasTable,
			 simplifyWL=simplifyWL,
			 spillWL=spillWL,
			 freezeWL=freezeWL,
			 activeMoves=activeMoves,
			 workListMoves=workListMoves,
			 frozenMoves=frozenMoves,
			 constrainedMoves=constrainedMoves,
			 coalescedMoves=coalescedMoves}
		    end 
	    end 
	val _ = ErrorMsg.debug "In Color\n"
	fun mainLoop (worklists as {selectStack,
				    simplifyWL,
				    spillWL,
				    freezeWL,
				    workListMoves,
				    degreeTable,
				    adjTable,
				    moveTable,
				    activeMoves,
				    frozenMoves, 
				    constrainedMoves,
				    coalescedMoves,
				    coalescedNodes,
				    aliasTable,...}) =
	    let
		val _ = ErrorMsg.debug "in mainLoop"
		val _ = print ("Simplify", simplifyWL) 
		val _ = print ("Spill", spillWL)
		val _ = print ("Freeze", freezeWL)
		val _ = print ("Select", selectStack)
		val _ = printMoves ("workListMoves", (MoveSet.listItems workListMoves))
		val _ = printMoves ("activeMoves", (MoveSet.listItems activeMoves))
		val _ = printMoves ("frozenMoves", (MoveSet.listItems frozenMoves))
		val _ = printMoves ("constrainedMoves", (MoveSet.listItems constrainedMoves))
		val _ = printMoves ("coalescedMoves", (MoveSet.listItems coalescedMoves))
		val _ = print ("coalescedNodes", coalescedNodes)
		
		val worklists =
		    if not (null simplifyWL)
		    then simplify worklists
		    else if not (MoveSet.isEmpty workListMoves)
		    then (coalesce worklists)
		    else if not (null freezeWL)
		    then (freeze worklists)
		    else if not (null spillWL)
		    then selectSpill worklists
		    else worklists
			 
		val {simplifyWL,
		     spillWL,
		     freezeWL,
		     workListMoves,
		     selectStack, coalescedNodes, aliasTable, ...} = worklists

	    in
		if (null simplifyWL) andalso
		   (null spillWL) andalso
		   (null freezeWL) andalso
		   (MoveSet.isEmpty workListMoves)
		then (selectStack, coalescedNodes, aliasTable)
		else mainLoop worklists
	    end

	val adjTable =
	    foldl (fn (node, table) => 
		      IGraph.Table.enter(table,
					 node,
					 (IGraph.adj node)))
		  IGraph.Table.empty
		  nodes

	val adjSetTable =
	    foldl (fn (node, adjSet) =>
		      let
			  val adjNodes = lookup adjTable node
		      in 
			  foldl (fn (adj, adjSet) =>
				    Adj.Table.insert(adjSet, (node, adj), ())) adjSet adjNodes
		      end)
		  Adj.Table.empty
		  nodes
		  
	val moveTable =
	    foldl (fn (move as (n1,n2), table) =>
		      let
			  val table =
			      case IGraph.Table.look(table, n1)
			       of SOME moveset => 
				  IGraph.Table.enter
				      (table, n1, MoveSet.add(moveset, move))
				| NONE => IGraph.Table.enter
					      (table, n1,
					       MoveSet.singleton(move))
			  val table =
			      case IGraph.Table.look(table, n2)
			       of SOME moveset => 
				  IGraph.Table.enter
				      (table, n2, MoveSet.add(moveset, move))
				| NONE => IGraph.Table.enter
					      (table, n2,
					       MoveSet.singleton(move))
		      in
			  table
		      end)
		  IGraph.Table.empty
		  moves
	val _ = ErrorMsg.debug "moves"
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
	val aliasTable = IGraph.Table.empty
	val activeMoves = MoveSet.empty
	val workListMoves = MoveSet.addList(MoveSet.empty, moves)
	val frozenMoves = MoveSet.empty
	val coalescedMoves = MoveSet.empty
	val constrainedMoves = MoveSet.empty
	val coalescedNodes = []
			     
	val _ = print ("Precolored ", precolored)
	val _ = print ("uncolored ", uncolored)
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
	    
	val _ = ErrorMsg.debug "In Color4\n"
	val (simplifyWL, spillWL, freezeWL) = makeWorklist(uncolored)
	val _ = print ("Initial Simplify", simplifyWL)
	val _ = print ("Initial Spill", spillWL)
	val _ = print ("Initial Freeze", freezeWL)
		
	val initWorklist =  {selectStack = [],
			     coalescedNodes=coalescedNodes,
			     degreeTable=degreeTable,
			     moveTable=moveTable,
			     adjTable=adjTable,
			     adjSetTable=adjSetTable,
			     aliasTable=aliasTable,
			     simplifyWL=simplifyWL,
			     spillWL=spillWL,
			     freezeWL=freezeWL,
			     activeMoves=activeMoves,
			     workListMoves=workListMoves,
			     frozenMoves=frozenMoves,
			     constrainedMoves=constrainedMoves,
			     coalescedMoves=coalescedMoves}

	val (selectStack, coalescedNodes, aliasTable) = mainLoop initWorklist
	val _ = degreeInvariant (simplifyWL,
				 spillWL,
				 freezeWL,
				 precolored,
				 lookup adjTable,
				 lookup degreeTable)
	val _ = simplifyWLInvariant (simplifyWL,
				     activeMoves,
				     workListMoves,
				     lookupSet moveTable,
				     lookup degreeTable)

	val _ = freezeWLInvariant (freezeWL,
				   activeMoves,
				   workListMoves,
				   lookupSet moveTable,
				   lookup degreeTable)
		
	val _ = spillWLInvariant(spillWL, lookup degreeTable)
	val _ = ErrorMsg.debug "passed invariant checks"

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
			val _ = ErrorMsg.debug ("Node: "^(IGraph.nodename head))
			val _ = ErrorMsg.debug ("Adjacent Nodes: "^(Int.toString (length usedColors)))
			val _ = ErrorMsg.debug ("Used colors: "^(String.concat (map (fn s=> s^" ") usedColors)))
			val okColors = differenceReg(registers, usedColors)
			(*			    val _ = ErrorMsg.debug ("Length of okColors"^
									      (Int.toString (length okColors))) *)
			val _ = ErrorMsg.debug ("OK colors: "^(String.concat (map (fn s=> s^" ") okColors)))
			val (color, spilledNodes) = if (null okColors)
						      then (color, head::spilledNodes)
						      else  let val reg = (hd okColors) in
								(ErrorMsg.debug ("Assigning temp "^(Temp.makestring temp)^" register "^reg);
								 (Temp.Table.enter
								      (color, temp, reg),
								  spilledNodes)) end
		    in
			loop(tail, color, spilledNodes)
		    end
		val (color, spilledNodes) = loop(selectStack, initial, [])
		val color = foldl (fn (n, color) => 
				      let val tempN = gtemp n
					  val alias = 
					      case IGraph.Table.look
						       (aliasTable, n)
					       of SOME node => node
						| NONE =>
						  ErrorMsg.impossible 
						  "Coalesced node not aliased"
					  val colorN = 
					      case nodeColor color alias
					       of SOME c => c
						| NONE =>
						  ErrorMsg.impossible
						  "Coalesced node not colored"
				      in Temp.Table.enter(color, tempN, colorN) 
				      end)
				  color
				  coalescedNodes 
	    in
		(color, spilledNodes)
	    end
	val (coloring, spilledNodes) = assignColors(selectStack)
	val spilledTemps = map gtemp spilledNodes
			   
	val _ = ErrorMsg.debug "Got to the end"
    in
	(*Temporary*)
	(coloring, spilledTemps)
    end

end


