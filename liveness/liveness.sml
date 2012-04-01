signature LIVENESS =
sig
    datatype igraph = 
	 IGRAPH of {graph: IGraph,
		    tnode:Temp.temp -> IGraph.node,
		    gtemp: IGraph.node -> Temp.temp,
		    movesL (IGraph.node * IGraph.node) list}
val interferenceGraph :
    Flow.flowgraph ->
    igraph * (Flow.Graph.node -> Temp.temp list)
    
val show: outstream * igraph -> unit

end

structure Liveness : LIVENESS =
struct
		     
structure Flow
structure ListMergeSort
	  
datatype igraph = 
	 IGRAPH of {graph: IGraph,
		    tnode:Temp.temp -> IGraph.node,
		    gtemp: IGraph.node -> Temp.temp,
		    moves: (IGraph.node * IGraph.node) list}
		   
type liveSet = unit Temp.Table.table * temp list
type liveMap = liveSet Flow.Graph.Table.table

fun union ((_, ltemps), (_,rtemps)) =
    let 
	fun merge (nil, r::rtail, acc) = merge(nil, rtail, r::acc)
	  | merge (l::ltail, nil, acc) = merge(ltail, nil, l::acc)
	  | merge (nil, nil, acc) = rev(acc)
	  | merge (l::ltail, r::rtail, acc) =
	    case Temp.compare (l,r)
	     of LESS => merge (ltail, r::rtail, l::acc)
	      | EQUAL => merge (ltail, rtail, l::acc)
	      | GREATER => merge (l::ltail, rtail, r::acc) 
	    
	val utemps = merge(ltemps, rtemps)

	val ulookup = foldl (fn (temp, table) => 
				Temp.Table.enter(table, temp, ()))
		      Temp.Table.empty
		      utemps

    in 
	(ulookup, utemps)
    end 

fun diff ((_, ltemps), (_,rtemps)) = =
    let
	fun merge (nil, r::rtail, acc) = merge(nil, rtail, acc)
	  | merge (l::ltail, nil, acc) = merge(ltail, nil, l::acc)
	  | merge (nil, nil, acc) = rev(acc)
	  | merge (l::ltail, r::rtail, acc) = 
	    case Temp.compare (l,r)
	     of LESS => merge (ltail, r::rtail, l::acc)
	      | EQUAL => merge (ltail, rtail, acc)
	      | GREATER => merge (l::ltail, rtail, acc)
	val utemps = merge(ltemps, rtemps)

	val ulookup = foldl (fn (temp, table) => 
				Temp.Table.enter(table, temp, ()))
		      Temp.Table.empty
		      utemps
    in 
	(ulookup, utemps)
    end 

fun interferenceGraph ({control, def, use, ismove}) = 
    let
	val nodes = rev (Flow.Graph.nodes control) (* start at the bottom of the nodes *)
	val liveIn = foldl (fn (node, table) => 
			       Flow.Graph.Table.enter(table, node, 
						      (Temp.Table.empty,[])))
		     Flow.Graph.Table.empty
		     nodes
	val liveOut = foldl (fn (node, table) => 
			       Flow.Graph.Table.enter(table, node, 
						      (Temp.Table.empty,[])))
		     Flow.Graph.Table.empty
		     nodes
	fun computeLiveness (node::tail, liveIn, liveOut) =
	    let 
		val liveIn'=liveIn[node]
		val liveOut'=liveOut[node]
		val liveIn=union(Flow.Graph.table.look(use, node),
				 diff(Flow.Graph.table.look(liveOut,node),
				      Flow.Graph.table.look(def,node)))
		val liveOut=foldl (fn (s, ins as (_,intemps)) => 
				      union(liveIn[S],intemps))
				  (Temp.Table.empty,[])
			    Flow.Graph.succ(node)

val show (outstream, igraph) = ()



