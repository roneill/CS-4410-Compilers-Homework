
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
datatype level = LEVEL of {frame: Frame, parent: level}
	       | TOP
type access = level * Frame.access

val outermost = TOP

fun newLevel {parent=parent, name=name, formals=formals} = 
    let
	val frame = Frame.newFrame(name,true::formals)
    in
	LEVEL {frame=frame, parent=parent}
    end

fun formals level =
    case level
     of LEVEL {frame, parent} = 
	let
	    formals = Frame.formals(frame)
	in
	    map (fn formal => (level, formal)) formals
	end
      | TOP = [] (* TODO: Does TOP have formals? Report Error? *)

fun allocLocal lev esc = 
    let
	val frame=(#frame lev)
	val access=Frame.allocLocal frame esc
    in
	(lev, access)
    end
end
