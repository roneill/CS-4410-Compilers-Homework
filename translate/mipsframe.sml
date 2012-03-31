
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
val FP = A.FP
val RV = A.RV
val maxArgRegisters = 4
val tempMap = Temp.Table.empty
	 
(*val tempMap = foldl Temp.Table.enter' Temp.Table.empty
		    [(A.ZERO, "$zero"),
		     (A.FP, "$fp"),
		     (A.RV, "$v0"),
		     (A.SP, "$sp"),
		     (A.RA, "$ra"),
		     (List.nth(A.argregs, 0), "$a0"), 
		     (List.nth(A.argregs, 1), "$a1"), 
		     (List.nth(A.argregs, 2), "$a2"), 
		     (List.nth(A.argregs, 3), "$a3"),
		     (List.nth(A.calleesaves, 0), "$s0"),
		     (List.nth(A.calleesaves, 1), "$s1"), 
		     (List.nth(A.calleesaves, 2), "$s2"), 
		     (List.nth(A.calleesaves, 3), "$s3"), 
		     (List.nth(A.calleesaves, 4), "$s4"),
		     (List.nth(A.calleesaves, 5), "$s5"),
		     (List.nth(A.calleesaves, 6), "$s6"), 
		     (List.nth(A.calleesaves, 7), "$s7"),
		     (List.nth(A.callersaves, 0), "$t0"),
		     (List.nth(A.callersaves, 1), "$t1"), 
		     (List.nth(A.callersaves, 2), "$t2"), 
		     (List.nth(A.callersaves, 3), "$t3"), 
		     (List.nth(A.callersaves, 4), "$t4"),
		     (List.nth(A.callersaves, 5), "$t5"),
		     (List.nth(A.callersaves, 6), "$t6"), 
		     (List.nth(A.callersaves, 7), "$t7"), 
		     (List.nth(A.callersaves, 8), "$t8"),
		     (List.nth(A.callersaves, 9), "$t9")]

fun tempToString (t) =
    case Temp.Table.look(tempMap, t)
     of SOME s => s
      | NONE => "$"^Temp.makestring(t) 
*)	      
fun procEntryExit1 (frame, body) = body 
fun newFrame {name, formals} =
    let
	val argumentOffset = ref 0
	fun getArgumentOffset () = 
	    (argumentOffset := !argumentOffset + wordSize;
	     !argumentOffset)

	fun allocFormal escape =  
	    if escape
	    then InFrame (getArgumentOffset())
	    else (InReg (Temp.newtemp()))

	val formals' = map allocFormal formals
    in
	{name=name, frameOffset= ref 0, formals=formals'}
    end
    
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

