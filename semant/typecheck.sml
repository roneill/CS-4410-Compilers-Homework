structure Test : sig val compile : string -> unit end =
struct

fun compile filename =
    let val ast = Parse.parse(filename)
	val fraglist = Semant.transProg ast
    in
	()
    end
    
end
