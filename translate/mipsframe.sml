
structure MipsFrame : FRAME =
struct

structure T=Tree
structure A=Assem
datatype access = InFrame of int | InReg of Temp.temp
type frame = {name: Temp.label, frameOffset: int ref, formals: access list}
datatype frag = PROC of {body: Tree.stm, frame: frame}
	      | STRING of Temp.label * string
type register = string
    
val wordSize = 4
val maxParamRegsters = 4
val FP = Temp.newtemp()
val RV = Temp.newtemp()

val tempMap = Temp.Table.empty

fun getTemps (num) =
    let
	fun getTemps' (0, temps) = temps
	  | getTemps' (i, temps) = getTemps'(i - 1, Temp.newtemp()::temps)
    in
	getTemps'(num, [])

    end
val FP = Temp.newtemp()
val RV = Temp.newtemp()
val SP = Temp.newtemp()
val RA = Temp.newtemp()
val ZERO = Temp.newtemp()
	     
val specialregs = [FP,RV,SP,RA,ZERO]
val argregs = getTemps(4)
val calleesaves = getTemps(8)
val callersaves = getTemps(10)
	      
val tempMap = foldl Temp.Table.enter' Temp.Table.empty
		    [(ZERO, "$zero"),
		     (FP, "$fp"),
		     (RV, "$v0"),
		     (SP, "$sp"),
		     (RA, "$ra"), 
		     (List.nth(argregs, 0), "$a0"),
		     (List.nth(argregs, 1), "$a1"), 
		     (List.nth(argregs, 2), "$a2"), 
		     (List.nth(argregs, 3), "$a3"),
		     (List.nth(calleesaves, 0), "$s0"),
		     (List.nth(calleesaves, 1), "$s1"), 
		     (List.nth(calleesaves, 2), "$s2"), 
		     (List.nth(calleesaves, 3), "$s3"), 
		     (List.nth(calleesaves, 4), "$s4"),
		     (List.nth(calleesaves, 5), "$s5"),
		     (List.nth(calleesaves, 6), "$s6"), 
		     (List.nth(calleesaves, 7), "$s7"),
		     (List.nth(callersaves, 0), "$t0"),
		     (List.nth(callersaves, 1), "$t1"), 
		     (List.nth(callersaves, 2), "$t2"), 
		     (List.nth(callersaves, 3), "$t3"), 
		     (List.nth(callersaves, 4), "$t4"),
		     (List.nth(callersaves, 5), "$t5"),
		     (List.nth(callersaves, 6), "$t6"), 
		     (List.nth(callersaves, 7), "$t7"), 
		     (List.nth(callersaves, 8), "$t8"),
		     (List.nth(callersaves, 9), "$t9")]

fun tempToString (t) =
    case Temp.Table.look(tempMap, t)
     of SOME s => s
      | NONE => "$"^Temp.makestring(t) 
	      
fun procEntryExit1 (frame, body) = body 
fun newFrame {name, formals} =
    let
	val argumentOffset = ref 0
	fun getArgumentOffset () = 
	    (argumentOffset := !argumentOffset + wordSize;
	     !argumentOffset)
	val usedRegisters = ref 0

	fun allocFormal escape =  
	    if (escape orelse (!usedRegisters >= maxParamRegsters)) then 
		InFrame (getArgumentOffset())
	    else 
		(usedRegisters := !usedRegisters + 1;
		 InReg (Temp.newtemp()))

	val formals' = map allocFormal formals
    in
	{name=name, frameOffset= ref 0, formals=formals'}
    end

fun procEntryExit2(frame, body) =
    body @
    [A.OPER{assem="",
	    src=specialregs@calleesaves,
	    dst=[], jump=SOME[]}]
    
fun allocLocal (frame:frame) escape =
    let
	val frameOffset = (#frameOffset frame)
	val newFrameOffset = !frameOffset - wordSize
    in
	frameOffset := newFrameOffset;
	if escape
	then InReg (Temp.newtemp())
	else InFrame (newFrameOffset)
    end

fun name (frame:frame) = (#name frame)
fun formals (frame:frame) = (#formals frame)

(* fp is either a TEMP(FP) or a series of MEM and + instructins to fetch the frame pointer *)			    
fun exp (InFrame k) fp = T.MEM(T.BINOP(T.PLUS,fp,T.CONST(k)))
  | exp (InReg t) _ = T.TEMP t

(* This function may require extension for machine specific details *) 
fun externalCall (s, args) =
    T.CALL (T.NAME(Temp.namedlabel s), args)

end

