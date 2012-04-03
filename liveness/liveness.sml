signature LIVENESS =
sig
    datatype igraph = 
	 IGRAPH of {graph: Graph.graph,
		    tnode:Temp.temp -> Graph.node,
		    gtemp: Graph.node -> Temp.temp,
		    moves: (Graph.node * Graph.node) list}
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

	      
datatype igraph = 
	 IGRAPH of {graph: Graph.graph,
		    tnode: Temp.temp -> Graph.node,
		    gtemp: Graph.node -> Temp.temp,
		    moves: (Graph.node * Graph.node) list}
		   
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
    in
	()
    end 

fun show (outstream, igraph) = ()



end
