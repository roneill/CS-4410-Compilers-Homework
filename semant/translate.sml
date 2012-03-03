
signature TRANSLATE =
sig
    type exp
    type level
    type access

    val outermost : level
    val newLevel : {parent:level, name:Temp.label,
		    formals: bool list} -> level
    val formals: level -> access list
    val allocLocal: level -> bool -> access
end

structure Translate : TRANSLATE =
struct
type exp = unit
type level = unit
type access = unit
	   
val outermost = ()

fun newLevel x = ()
fun formals x = [()]
fun allocLocal x = (fn x => ())
	   
end
