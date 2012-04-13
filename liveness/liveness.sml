signature LIVENESS =
sig
    structure IGraph : GRAPH
    datatype igraph = 
	 IGRAPH of {graph: IGraph.graph,
		    tnode:Temp.temp -> IGraph.node,
		    gtemp: IGraph.node -> Temp.temp,
		    moves: (IGraph.node * IGraph.node) list}
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

(* Move hash table to check for duplicates in the move list *)
structure MoveTable =
BinaryMapFn
    (struct
	 type ord_key = (Temp.temp * Temp.temp)
	 val compare = (fn ((l1,l2),(r1,r2)) =>
			   case Temp.compareTemps(l1,r1)
			    of LESS => LESS
			     | GREATER => GREATER
			     | EQUAL => case Temp.compareTemps(l2,r2)
					 of LESS => LESS
					  | GREATER => GREATER
					  | EQUAL => EQUAL)
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
	(*Debug*)
	fun say s =  TextIO.output(TextIO.stdOut,s)
	fun sayln s= (say s; say "\n")
	fun printNode (node, liveset) = 
	    let 
		val nodestr = Graph.nodename node
		val liveSetstr = String.concat 
				     (map (fn temp => 
					      (Temp.makestring temp)^" ") 
					  (S.listItems liveset))
	    in sayln (nodestr^": {"^liveSetstr^"} ") 
	    end 
	(*Debug printing*)
	fun printLive (liveMap, nodes) =
	    let 
		val liveSets = map (fn node => 
				       getOpt(T.look(liveMap, node), 
					      Flow.Set.empty)) 
				   nodes
	    in
		map printNode (ListPair.zip (nodes, liveSets))
	    end
	(* start at the bottom of the nodes *)
	val nodes = rev (Flow.Graph.nodes control) 
	val liveIn = foldl (fn (node, table) => 
			       T.enter(table, node, (Flow.Set.empty)))
		     T.empty
		     nodes
	val liveOut = foldl (fn (node, table) => 
				T.enter(table, node, (Flow.Set.empty)))
		     T.empty
		     nodes
	fun list2set l = Flow.Set.addList(Flow.Set.empty,l)
	fun computeLiveness (liveInTable, liveOutTable) =
	    let 
		val (liveInTable', liveOutTable', changed) =
		    iterate(nodes, liveInTable, liveOutTable, false)
	    in
		if changed
		then computeLiveness (liveInTable', liveOutTable')
		else (liveInTable', liveOutTable')
	    end
	and iterate (nil, liveInTable, liveOutTable, changed) =
	    (liveInTable, liveOutTable, changed)
	  | iterate (node::tail, liveInTable, liveOutTable, changed) =
	    let 
		val _ = if changed then sayln "changed" else sayln "unchanged"
		val liveIn' = getOpt(T.look(liveInTable, node), Flow.Set.empty)
		val liveOut' =  getOpt(T.look(liveOutTable, node), Flow.Set.empty)
		val uses = list2set(getOpt(T.look(use, node), []))
		val defs = list2set(getOpt(T.look(def, node), []))
		val liveIn = Flow.Set.union(uses,
					    Flow.Set.difference(liveOut', defs))
		val liveOut = foldl (fn (s, ins) => 
					Flow.Set.union(getOpt(T.look(liveInTable, s),
							      Flow.Set.empty),ins))
				    (Flow.Set.empty)
				    (Flow.Graph.succ(node))
		val areBothSetsDifferent = not(Flow.Set.equal(liveIn',liveIn) andalso
					       Flow.Set.equal(liveOut', liveOut))
		val changed' = changed orelse areBothSetsDifferent
		
		val liveInTable' = T.enter(liveInTable, node, liveIn)
		val liveOutTable' = T.enter(liveOutTable, node, liveOut)
	    in
		iterate(tail, liveInTable', liveOutTable', changed')
	    end
	val (_, liveMap) = computeLiveness(liveIn, liveOut)
	val _ = printLive (liveMap, rev(nodes))
	val graph = IGraph.newGraph()
	(* Make nodes in the interference graph *)
	fun makeINodes (fnode, (node2temp, temp2node)) =
	    let 
		val defs = getOpt(T.look(def, fnode), [])
		val uses = getOpt(T.look(use, fnode), [])
		fun makeNode (temp, (node2temp, temp2node)) =
		    case Temp.Table.look(temp2node, temp) 
		     of SOME node => (node2temp, temp2node)
		      | NONE => 
			let
			    val node = IGraph.newNode(graph)
			    val _ = sayln ("Created node: "^(IGraph.nodename node))
			    val node2temp' = T.enter(node2temp, node, temp)
			    val temp2node' = Temp.Table.enter(temp2node, temp, node)
			in
			    (node2temp', temp2node')
			end
		val (node2temp',temp2node') = foldl makeNode (node2temp, temp2node) defs
		val (node2temp',temp2node') = foldl makeNode (node2temp', temp2node') uses
	    in 
		 (node2temp',temp2node')
	    end
	val (node2temp, temp2node) = foldl makeINodes (T.empty, Temp.Table.empty) nodes
	fun tnode temp  =
	    case Temp.Table.look(temp2node, temp)
		 of SOME node => node
		  | NONE => ErrorMsg.impossible ("Temporary "
						 ^(Temp.makestring temp)^
						 " not in node table")
	fun gtemp node = 
	    case T.look(node2temp, node)
			  of SOME temp => temp
			   | NONE => ErrorMsg.impossible ("Node "^
							  (IGraph.nodename node)
							  ^" not in temp table")
	val moves = ref []
	val moveTable = ref MoveTable.empty
	fun inMoveTable (t1,t2) =
	    let 
		val entry = case Temp.compareTemps(t1,t2)
			     of LESS => MoveTable.find(!moveTable, (t1,t2)) 
			      | GREATER => MoveTable.find(!moveTable, (t2,t1))
			      | EQUAL => ErrorMsg.impossible 
					     "Temps should not be equal here"
	    in
		case entry
		 of SOME _ => true
		  | NONE => false
	    end
	fun makeEdges (fnode) = 
	    let
		val defs = getOpt(T.look(def, fnode), [])
		val liveSet = getOpt(T.look(liveMap, fnode), Flow.Set.empty)
		val ismovep = getOpt(T.look(ismove, fnode), false) 
		fun moveusep temp =
		    let
			val uses = list2set(getOpt((T.look(use, fnode)), []))
		    in
			Flow.Set.member(uses, temp)
		    end
		fun nodesAdj (n1, n2) =
		    let
			val adj1 = IGraph.adj n1
		    in
			(List.exists (fn x => IGraph.eq(x, n2)) adj1)
		    end
	        fun makeEdge (t1, t2) =
		    let
			val n1 = tnode(t1)
			val n2 = tnode(t2)
		    in
			if t1=t2 orelse nodesAdj(n1, n2) then ()
			else if (ismovep andalso (moveusep t2))
			then makeMove(t1,t2)
			else ((sayln ("Making edge from "^(IGraph.nodename n1)
				      ^" "^(IGraph.nodename n2)));
			      IGraph.mk_edge{from=n1, to=n2})
		    end
		and makeMove (t1, t2) =
		    if (ismovep andalso (moveusep t2) andalso 
			not(inMoveTable(t1,t2)))
		    then
			let
			    val n1 = tnode(t1)
			    val n2 = tnode(t2)
			in
			    moves := (n1, n2)::(!moves);
			    moveTable := MoveTable.insert(!moveTable, (t1,t2), ())
			end
		    else ()
			
	    in
		map (fn def => (sayln ("Def: "^(Temp.makestring def)))) defs;
		app (fn def =>
			(app (fn live =>
				 makeEdge(def, live))
			     (Flow.Set.listItems liveSet)))
		    defs
	    end
	val _ = app makeEdges nodes
	fun fnode2temps fnode =
	    (Flow.Set.listItems (getOpt(T.look(liveMap, fnode), Flow.Set.empty)))
    in
	(IGRAPH {graph=graph, tnode=tnode, gtemp=gtemp, moves=(!moves)},
	 fnode2temps)
    end 

fun show (outstream,IGRAPH{graph=graph, tnode=tnode, gtemp=gtemp, moves=moves}) =
    let	
    	fun say s =  TextIO.output(outstream,s)
	fun sayln s= (say s; say "\n")

	val nodes = IGraph.nodes graph

	fun printNode (node) =
	    let
		val adjNodes = IGraph.adj node
		val nodeString = IGraph.nodename node
		val temp = gtemp node
		val tempString = Temp.makestring temp 
		val adjStrings = map (fn node => 
					 Temp.makestring (gtemp node)^" ") 
				     adjNodes
		val adjString = "{"^(String.concat adjStrings)^"}"
	    in
		sayln (tempString^" "^adjString)
	    end
	val _ = app printNode nodes
	val _ = app (fn node => sayln (IGraph.nodename node)) nodes
    in
	()
    end
end
