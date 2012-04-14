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
    type allocation = Frame.register Temp.Table.table
		      
    fun color {interference, initial, spillCost, registers } =
	(Frame.tempMap, [])
end
(*
1. Implement Color without spilling or coalescing
 a. 
*)

