
structure MipsFrame : FRAME =
struct
datatype access = InFrame of int | InReg of Temp.temp
type frame = {name: Temp.label, frameOffset: int ref, formals: access list}
val wordsize = 4
val maxParamRegsters = 4

fun newFrame {name, formals} =
    let
	val argumentOffset = ref 0
	fun getArgumentOffset () = 
	    (argumentOffset := !argumentOffset + wordsize;
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
	val newFrameOffset = !frameOffset - wordsize
    in
	frameOffset := newFrameOffset;
	if escape
	then InReg (Temp.newtemp())
	else InFrame (newFrameOffset)
    end

fun name (frame:frame) = (#name frame) 
fun formals (frame:frame) = (#formals frame) 
end
