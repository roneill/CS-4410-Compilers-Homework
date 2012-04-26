		  
signature TRANSLATE =
sig
    type exp
    type level
    type access
    type fraglist
    structure Frame: FRAME
    val procEntryExit: {level: level, body: exp} -> unit
    val getResult: unit -> Frame.frag list 

    val outermost : level
    val newLevel : {parent:level, name:Temp.label,
		    formals: bool list} -> level
    val formals: level -> access list
    val allocLocal: level -> bool -> access
    val simpleVar : access * level -> exp
    val fieldVar: exp * exp -> exp
    val subscriptVar: exp*exp -> exp 
    val plus: exp * exp -> exp 
    val minus: exp * exp -> exp 
    val times: exp * exp -> exp 
    val divide: exp * exp -> exp 
    val eq: exp * exp -> exp 
    val neq: exp * exp -> exp 
    val lt: exp * exp -> exp 
    val le: exp * exp -> exp 
    val gt: exp * exp -> exp 
    val ge: exp * exp -> exp
    val ifExp: exp * exp * exp -> exp
    val newString: string -> exp
    val newRecord: exp list -> exp
    val newArray: exp * exp -> exp
    val newLoop: exp * exp * Temp.label -> exp
    val newBreak: Temp.label -> exp
    val nil: unit -> exp
    val newInt: int -> exp
    val newAssign: exp * exp -> exp
    val NOP: unit -> exp
    val varDecs: exp list -> exp
    val newLet: exp * exp -> exp
    val seqexp: exp list * exp -> exp
    val initResult: unit-> unit
    val callFun: Temp.label * exp list * level * level -> exp
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
			   parent: level,
			   unique: unit ref}
	       | TOP
		 
type access = level * Frame.access
type fraglist = Frame.frag list
		
val outermost = TOP
val result: Frame.frag list ref = ref []

(* Needed to clear result between calls to transProg *)				  
fun initResult () = result := []
				  
fun newLevel {parent=parent, name=name, formals=formals} = 
    let
	val frame = Frame.newFrame{name=name,formals=true::formals}
    in
	LEVEL {frame=frame, parent=parent, unique=ref()}
    end

fun formals level =
    case level
     of LEVEL {frame, parent, unique} => 
	let
	    (*strip the static link*)
	    val formals = tl(Frame.formals(frame)) 
	in
	    map (fn formal => (level, formal)) formals
	end
      | TOP => (ErrorMsg.impossible "Called formals on TOP")

fun allocLocal lev esc = 
    case lev
     of LEVEL {frame, parent, unique} => 
	let
	    val access=Frame.allocLocal frame esc
	in
	    (lev, access)
	end
      | TOP =>
	Error.impossible "Tried to allocLocal at the outermost level"
	
fun seq nil = Error.impossible "Tried to make a SEQ from nothing" 
  | seq(h::nil) = h 
  | seq(h::t) = T.SEQ(h,seq t)
	      
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

fun unCx (Ex e) =
    (case e
      of T.CONST k => if (k = 0)
		      then (fn (t,f) => T.JUMP (T.NAME f,[f]))
		    else (fn (t,f) => T.JUMP (T.NAME t,[t]))
       | _ => fn (t,f) => T.CJUMP (T.NE, T.CONST 0, e, t,f))
		   
  | unCx (Cx genstm) = genstm
  | unCx (Nx _) = Error.impossible "Tried to convert statement to control"

fun chaseStaticLinks (deflevel, curlevel) =
    if (curlevel = deflevel)
    then (T.TEMP Frame.FP)
    else case curlevel
	  of LEVEL {frame, parent, unique} =>
	     (T.MEM (chaseStaticLinks(deflevel, parent)))
	   | TOP => (ErrorMsg.impossible "Called chaseStaticLinks on TOP")
		    
fun simpleVar ((varlevel,access), curlevel) =
    Ex(Frame.exp access (chaseStaticLinks(varlevel, curlevel)))

fun callFun (label, args, expLevel, funLevel) =
    let
	val args = map unEx args
    in
	case funLevel
	  (* Calls to Standard Library 
	   * - do not pass static link as first argument *)
	 of TOP => Ex(T.CALL( T.NAME label, args))
	  (* All other calls to user defined functions*)
	  | LEVEL {frame, parent, unique} =>
	    let 
		val sl = chaseStaticLinks(parent, expLevel)
		val args' = sl::args 
	    in
		Ex (T.CALL(T.NAME label, args'))
	    end
    end

fun subscriptVar (base:exp, index:exp) =
    let
	val base' = unEx base
	val index' = unEx index
    in
	Ex (T.MEM (T.BINOP (T.PLUS, T.MEM(base'), 
			    T.BINOP (T.MUL, index', T.CONST Frame.wordSize))))
    end
    
val fieldVar = subscriptVar
	      
fun arith (lexp, rexp, oper) = 
    let
	val lexp' = unEx lexp
	val rexp' = unEx rexp
    in
	Ex (T.BINOP(oper, lexp', rexp'))
    end	       

fun control (lexp, rexp, oper) =
    let
	val lexp' = unEx lexp
	val rexp' = unEx rexp
    in
	Cx (fn (t,f) => T.CJUMP (oper, lexp', rexp', t,f))
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
    
fun ifExp (exp1, exp2, exp3) =
    let
	val s = unCx exp1
	val join = Temp.newlabel()
	val t = Temp.newlabel()
	val f = Temp.newlabel()
	fun ifExp' (Nx stm2, Nx stm3) = 
	    Nx ( seq [s(t,f),
		      T.LABEL t,
		      stm2,
		      T.JUMP (T.NAME join, [join]),
		      T.LABEL f,
		      stm3,
		      T.LABEL join] )
	  | ifExp' (Cx ctl2, Cx ctl3) =
	    let 
		val y = Temp.newlabel()
		val z = Temp.newlabel()
	    in
		Cx (fn (t,f) => seq [s(y,z), 
				     T.LABEL y,
				     ctl2(t,f),
				     T.LABEL z,
				     ctl3(t,f)])
	    end
	  | ifExp' (Cx ctl2, Ex exp3) =
	    let val ctl3 = unCx (Ex exp3)
	    in
		ifExp' (Cx ctl2, Cx ctl3)
	    end
	  | ifExp' (Ex exp2, Cx ctl3) =
	    let val ctl2 = unCx (Ex exp2)
	    in
		ifExp' (Cx ctl2, Cx ctl3)
	    end
	  | ifExp' (exp2, exp3)  =
	    let
		val r = Temp.newtemp()
		val exp2' = unEx exp2
		val exp3' = unEx exp3
	    in 		
		Ex (T.ESEQ (seq[s(t,f), 
				T.LABEL t, 
				T.MOVE (T.TEMP r, exp2'),
				T.JUMP (T.NAME join, [join]),
				T.LABEL f,
				T.MOVE (T.TEMP r, exp3'),
				T.LABEL join],
			    T.TEMP r))
	    end
    in 
	ifExp' (exp2, exp3)
    end

fun newString (s) =
    let 
	val label = Temp.newlabel()
	val _ = result := Frame.STRING(label, s) :: (!result)
    in
	 Ex (T.NAME label)
    end

fun newRecord (exps) =
    let
	val exps' = map unEx exps 
	val r = Temp.newtemp()
	fun initFields(exps) =
	    let
		val l1 = List.tabulate(length(exps), (fn x => x))
		val pairs =  ListPair.zip(l1, exps)
		fun createMove (i, exp) = 	
		    T.MOVE (T.MEM (T.BINOP (T.PLUS, 
					    T.TEMP r, 
					    T.CONST (i * Frame.wordSize))),
			    exp)
	    in
		seq (map createMove pairs)
	    end
    in
	Ex (T.ESEQ
	    (T.SEQ(T.MOVE (T.TEMP r,
			   Frame.externalCall("tig_malloc",
					      [T.CONST (length(exps) * 
							Frame.wordSize)])),
		   initFields(exps')),
	     T.TEMP r))
    end

fun newArray (len, init) =
    let
	val r = Temp.newtemp()
	val len' = unEx len
	val init' = unEx init
    in
	Ex (T.ESEQ 
	    (T.MOVE (T.TEMP r,
		     Frame.externalCall("tig_initArray", [len',init'])),
	     T.TEMP r))
    end

fun newLoop (test, body, done) = 
    let
	val test' = unCx test
	val body' = unNx body
	val bod = Temp.newlabel()
	val t = Temp.newlabel()
    in 
	 Nx (seq[T.JUMP (T.NAME t, [t]),
		 T.LABEL bod,
		 body',
		 T.LABEL t,
		 test'(bod,done),
		 T.LABEL done])
    end

fun newBreak (loopEnd) =
    Nx ( T.JUMP (T.NAME loopEnd,[loopEnd]))
    
fun nil () = 
    Ex(T.CONST (0))

fun newInt (i) =
    Ex (T.CONST(i))

fun newAssign (lExp, rExp) = 
    let
	val lExp = unEx lExp 
	val rExp = unEx rExp 
    in
	Nx (T.MOVE(lExp, rExp))
    end

(* This should get elimimated by an optimization phase *)
fun NOP () =
    let
	val t = Temp.newtemp()
    in 
	Nx ( T.MOVE (T.TEMP(t),T.TEMP(t)))
    end

fun varDecs [] = NOP()
  | varDecs exps =
    let
	val exps = map unNx (rev exps)
    in
	Nx (seq(exps))
    end

fun seqexp (exps, exp) =
    let
	val stms = map unNx (rev exps)
    in	
	Ex (T.ESEQ(seq(stms), (unEx exp)))
    end
    
fun newLet (varExps, bodyExp) =
    let
	val varExps = unNx varExps
	val bodyExp = unEx bodyExp
    in
	Ex (T.ESEQ(varExps, bodyExp))
    end

fun getResult () = !result

fun procEntryExit {level=LEVEL l, body=b} =
    let
	val bexp = unEx b
	val bstm = T.MOVE (T.TEMP Frame.RV0, bexp)
	val frame = #frame l
	val body = Frame.procEntryExit1(frame,bstm)
	val fragment = Frame.PROC {body=body, frame=frame}
    in
	result := fragment::(!result)
    end
  | procEntryExit {level=TOP, body=_} =
    ErrorMsg.impossible ("procEntryExit called with TOP level")    
end
