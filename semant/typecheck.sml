
structure TypeCheck : sig val typecheck : string -> unit end =
struct

fun typecheck filename =
    let val ast = Parse.parse(filename)
    in
	Semant.transProg ast
    end
    
end
