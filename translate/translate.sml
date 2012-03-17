		  
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
						
datatype level = LEVEL of {frame: Frame.frame,
			   parent: level} (* consider making this unique *)
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
  | seq(a::r) = T.SEQ(a,seq r)
	      
fun unEx (Ex e) = e
  | unEx (Cx genstm) =
    let val r = Temp.newtemp()
	val t = Temp.newlabel()
	val f = Temp.newlabel()
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
			   T.SEQ(genstm(l,l),T.LABEL l)
		       end
  | unNx (Nx s) = s

fun unCx (Ex e) = (fn (t,f) => T.CJUMP (T.NE, T.CONST 0, e, t,f))
  | unCx (Cx genstm) = genstm
  | unCx (Nx _) = Error.impossible "Tried to convert statement to control"
		  
fun simpleVar ((varlevel,access), curlevel) =
    let
	fun chaseStaticLinks (varlevel, curlevel) =
	    if (curlevel = varlevel)
	    then T.TEMP Frame.FP
	    else case curlevel
		  of LEVEL {frame, parent} => T.MEM (chaseStaticLinks(varlevel, parent))
		   | TOP => (ErrorMsg.impossible "oops")
    in
	Ex(Frame.exp access (chaseStaticLinks(varlevel,curlevel)))
    end

      
fun sunscriptVar (base:exp, index:exp) =
    let
	val base' = unEx base
	val index' = unEx index
    in
	Ex (T.MEM (T.BINOP (T.PLUS, T.MEM(base'), T.BINOP (T.MUL, index', Frame.wordSize))))
    end
    
val fieldVar = subscriptVar

(*fun safeArrayVar*)

fun arith (lexp, rexp, oper) = 
    let
	val lexp' = unEx base
	val rexp' = unEx index
    in
	Ex (BINOP(oper, lexp', rexp'))
    end	       

fun control (lexp, rexp, oper)
    let
	val lexp' = unEx lexp
	val rexp' = unEx rexp
    in
	Cx (fn (t,f) => CJUMP (oper, lexp', rexp', t,f))
    end
    
fun plus (lexp, rexp) =
    arith(lexp, rexp, T.PLUS)

fun minus (lexp, rexp) =
    arith(lexp, rexp, T.MINUS)

fun times (lexp, rexp) =
    arith(lexp, rexp, T.MUL)

fun divide (lexp, rexp) =
    arith(lexp, rexp, T.DIV)

fun eq (lexp, rexp) =
    control(lexp, rexp, T.EQ)
    
fun neq (lexp, rexp) =
    control(lexp, rexp, T.NE)

fun lt (lexp, rexp) =
    control(lexp, rexp, T.LT)

fun le (lexp, rexp) =
    control(lexp, rexp, T.LE)

fun gt (lexp, rexp) =
    control(lexp, rexp, T.GT)

fun ge (lexp, rexp) =
    control(lexp, rexp, T.GE)

fun ifExp (exp1, exp2, exp3)
    let
	val f = unCx exp1
	val exp2' = unEx exp2
	val exp3' = unEx exp3
	val t = Temp.newlabel()
	val f = Temp.newlabel()
	val r = Temp.newtemp()
    in
    end
end

