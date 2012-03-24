
signature FRAME =
sig type frame
    type access
    type register
    datatype frag = PROC of {body: Tree.stm, frame: frame}
		  | STRING of Temp.label * string
    val RV: Temp.temp
    val FP: Temp.temp
    val newFrame : {name: Temp.label,
		    formals: bool list} -> frame
    val name: frame -> Temp.label
    val formals : frame -> access list
    val allocLocal : frame -> bool -> access
    val wordSize: int
    val exp: access -> Tree.exp -> Tree.exp
    val procEntryExit1 : frame * Tree.stm -> Tree.stm
    val externalCall: string * Tree.exp list -> Tree.exp
    val tempMap: register Temp.Table.table	   
end
