
structure MipsFrame : FRAME =
struct

structure T=Tree
	    
datatype access = InFrame of int | InReg of Temp.temp
type frame = {name: Temp.label, frameOffset: int ref, formals: access list}
datatype frag = PROC of {body: Tree.stm, frame: frame}
	      | STRING of Temp.label * string
val wordSize = 4
val maxParamRegsters = 4
val FP = Temp.newtemp()
val RV = Temp.newtemp()

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
fun externalCall(s, args) =
    T.CALL (T.NAME(Temp.namedlabel s), args)

end

