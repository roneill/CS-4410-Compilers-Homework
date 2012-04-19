signature NODE_PAIR =
sig
    structure IGraph : GRAPH
    type pair = IGraph.node * IGraph.node 
    val comparePairs: pair * pair -> order
    structure Table : ORD_MAP 
end

structure NodePair : NODE_PAIR =
struct

    structure IGraph = Graph
    type pair = IGraph.node * IGraph.node

    fun comparePairs (pair1 as (l1,l2), pair2 as (r1, r2)) = 
	let
	    fun sort (n1, n2) =
		case IGraph.compare(n1, n2)
		 of LESS => (n1,n2)
		  | GREATER => (n2,n1)
		  | EQUAL => ErrorMsg.impossible "Pair contains equal nodes"

	    val (firstl, secondl) = sort (l1,l2)
	    val (firstr, secondr) = sort (r1,r2)
	in 
	    case IGraph.compare(firstl,firstr)
	     of LESS => LESS
	      | GREATER => GREATER
	      | EQUAL => case IGraph.compare(secondl,secondl)
			  of LESS => LESS
			   | GREATER => GREATER
			   | EQUAL => EQUAL
	end 
    (* Pair hash table to check for duplicates in the pair list *)
    structure Table =
    BinaryMapFn
	(struct
	 type ord_key = pair
	 val compare = comparePairs
	 end)
    

end
