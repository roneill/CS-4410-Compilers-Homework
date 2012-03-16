		  
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
    val simpleVar : access * level -> exp
end

structure Translate : TRANSLATE =
struct

structure Frame = MipsFrame
structure T = Tree
structure Error = ErrorMsg

datatype exp = Ex of Tree.exp
	     | Nx of Tree.stm
	     | Cx of Temp.label * Temp.label -> Tree.stm
						
datatype level = LEVEL of {frame: Frame.frame, parent: level}
	       | TOP
		 
type access = level * Frame.access

val outermost = TOP

fun newLevel {parent=parent, name=name, formals=formals} = 
    let
	val frame = Frame.newFrame{name=name,formals=true::formals}
    in
	LEVEL {frame=frame, parent=parent}
    end

fun formals level =
    case level
     of LEVEL {frame, parent} => 
	let
	    val formals = Frame.formals(frame)
	in
	    map (fn formal => (level, formal)) formals
	end
      | TOP => [] (* TODO: Does TOP have formals? Report Error? *)

fun allocLocal lev esc = 
    case lev
     of LEVEL {frame, parent} => 
	let
	    val access=Frame.allocLocal frame esc
	in
	    (lev, access)
	end
      | TOP =>
	Error.impossible "Tried to allocLocal at the outermost level"
	
fun seq [] = Error.impossible "Tried to make a SEQ from nothing" 
  | seq [a] = a 
  | seq(a::r) = SEQ(a,seq r)
	      
fun unEx (Ex e) = e
  | unEx (Cx genstm) =
    let val r = Temp.newtemp()
	val t = Temp.newlabel() and f = Temp.newlabel()
    in T.ESEQ(seq[T.MOVE(T.TEMP r, T.CONST 1),
		  genstm(t,f),
		  T.LABEL f,
		  T.MOVE(T.TEMP r, T.CONST 0),
		  T.LABEL t],
	      T.TEMP r)
    end
  | unEx (Nx s) = T.ESEQ(s, T.CONST 0)

fun unNx (Ex e) = T.EXP e
  | unNx (Cx genstm) = let val l = Temp.newlabel()
		       in
			   T.SEQ(genstm(l,l),LABEL l)
		       end
  | unNx (Nx s) = s

fun unCx (Ex e) = (fn (t,f) => (T.EXP e)) (*TODO: not sure, come back later*)
  | unCx (Cx genstm) = genstm
  | unCx (Nx _) = Error.impossible "Tried to convert statement to control"

fun simpleVar (access, level) = exp 
		  
end
