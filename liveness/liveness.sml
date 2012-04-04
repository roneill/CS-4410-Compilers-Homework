signature LIVENESS =
sig
    structure IGraph : GRAPH
    datatype igraph = 
	 IGRAPH of {graph: IGraph.graph,
		    tnode:Temp.temp -> IGraph.node,
		    gtemp: IGraph.node -> Temp.temp,
		    moves: (IGraph.node * Graph.node) list}
val interferenceGraph :
    Flow.flowgraph ->
    igraph * (Flow.Graph.node -> Temp.temp list)
    
val show: TextIO.outstream * igraph -> unit

end

structure Liveness : LIVENESS =
struct
		     
structure Flow = Flow
structure T = Flow.Graph.Table
structure S = Flow.Set
structure IGraph = Graph

structure MoveTable = BinaryMapFn(struct
        type ord_key = (Temp.temp * Temp.temp)
        val compare = (fn ((l1,l2),(r1,r2)) =>
			  if (l1 = r1) andalso (l2 = r2)
			  then EQUAL
			  else LESS (*TODO*)
				  end)
datatype igraph = 
	 IGRAPH of {graph: IGraph.graph,
		    tnode: Temp.temp -> IGraph.node,
		    gtemp: IGraph.node -> Temp.temp,
		    moves: (IGraph.node * Graph.node) list}
		   
type liveSet = unit Temp.Table.table * Temp.temp list
type liveMap = liveSet T.table
	
fun interferenceGraph (Flow.FGRAPH{control, def, use, ismove}) = 
    let
	val nodes = rev (Flow.Graph.nodes control) (* start at the bottom of the nodes *)
	val liveIn = foldl (fn (node, table) => 
			       T.enter(table, node, (Flow.Set.empty)))
		     T.empty
		     nodes
	val liveOut = foldl (fn (node, table) => 
			       T.enter(table, node, 
						      (Flow.Set.empty)))
		     T.empty
		     nodes
	fun computeLiveness (liveInTable, liveOutTable) =
	    let 
		val (liveInTable', liveOutTable', changed) =
		    iterate(nodes, liveOutTable, liveOutTable, false)
	    in
		if changed
		then computeLiveness (liveInTable', liveOutTable')
		else (liveInTable', liveOutTable')
	    end
	and iterate (nil, liveInTable, liveOutTable, changed) =
	    (liveInTable, liveOutTable, changed)
	  | iterate (node::tail, liveInTable, liveOutTable, changed) =
	    let 
		val liveIn' = getOpt(T.look(liveInTable, node), Flow.Set.empty)
		val liveOut' =  getOpt(T.look(liveOutTable, node), Flow.Set.empty)
		val uses = getOpt(T.look(use, node), Flow.Set.empty)
		val defs = getOpt(T.look(def, node), Flow.Set.empty)
		val liveIn = Flow.Set.union(uses,
					    Flow.Set.difference(liveOut', defs))
		val liveOut = foldl (fn (s, ins) => 
					Flow.Set.union(getOpt(T.look(liveInTable, s),
							      Flow.Set.empty),ins))
				    (Flow.Set.empty)
				    (Flow.Graph.succ(node))
		val changed' = changed orelse (not(Flow.Set.equal(liveIn',liveIn) andalso
						    Flow.Set.equal(liveOut', liveOut)))
		val liveInTable' = T.enter(liveInTable, node, liveIn)
		val liveOutTable' = T.enter(liveOutTable, node, liveOut)
	    in
		iterate(tail, liveInTable', liveOutTable', changed)
	    end
	val (_, liveMap) = computeLiveness(liveIn, liveOut)
	val graph = IGraph.newGraph()
	(* Make nodes in the interference graph *)
	fun makeINodes (fnode, (node2temp, temp2node)) =
	    let 
		val defSet = getOpt(T.look(def, fnode), Flow.Set.empty)
		fun makeNode (temp, (node2temp, temp2node)) =
		    let
			val node = IGraph.newNode(graph)
		    in
			(T.enter(node2temp, fnode, temp),
			 Temp.Table.enter(temp2node, temp, fnode))
		    end
		val (node2temp',temp2node') = foldl makeNode (node2temp, temp2node) (Flow.Set.listItems defSet)
	    in 
		 (node2temp',temp2node')
	    end
	val emptyTempTable: Temp.temp Flow.Graph.Table.table = T.empty
	val emptyNodeTable: IGraph.node Flow.Graph.Table.table = T.empty				     
	val (node2temp, temp2node) = foldl makeINodes (T.empty, Temp.Table.empty) nodes
	fun tnode temp =
	    case Temp.Table.look(temp2node, temp)
		 of SOME node => node
		  | NONE => ErrorMsg.impossible "Temporary not in node table"
	fun gtemp node = case T.look(node2temp, node)
			  of SOME temp => temp
			   | NONE => ErrorMsg.impossible "Node not in temp table"
	fun makeEdges (fnode) = 
	    let
		val defSet = getOpt(T.look(def, fnode), Flow.Set.empty)
		val liveSet = getOpt(T.look(liveMap, fnode), Flow.Set.empty)
		fun ismovep () = getOpt(T.look(ismove, fnode), false) 
		fun moveusep temp =
		    let
			val uses = getOpt((T.look(use, fnode)), Flow.Set.empty)
		    in
			Flow.Set.member(uses, temp)
		    end 
	        fun makeEdge (t1, t2) =
		    if t1=t2 orelse (ismovep() andalso (moveusep t2))
		    then ()
		    else
			let
			    val n1 = tnode(t1)
			    val n2 = tnode(t2)
			in
			    IGraph.mk_edge{from=n1, to=n2}
			end
		fun createMoves (t1, t2, moves) =
		    if t1=t2 orelse (ismovep() andalso (moveusep t2))
		    then
			let
			    val n1 = tnode(t1)
			    val n2 = tnode(t2)
			in
			    (n1, n2)::moves
			end
		    else
			moves
			
	    in
		app (fn def =>
			(app (fn live =>
				 makeEdge(def, live)) (Flow.Set.listItems liveSet)))
		    (Flow.Set.listItems defSet)
	    end
	val _ = app makeEdges nodes
	fun fnode2temps fnode =
	    (Flow.Set.listItems (getOpt(T.look(liveMap, fnode), Flow.Set.empty)))
    in
	(IGRAPH {graph=graph, tnode=tnode, gtemp=gtemp, moves=[]},
	 fnode2temps)
    end 

fun show (outstream, igraph) = ()

end
