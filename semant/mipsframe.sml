
structure MipsFrame : FRAME =
struct
datatype access = InFrame of int | InReg of Temp.temp
type frame = {name: Temp.label, frameOffset: int ref, formals: access list}
val wordsize = 4
					    
fun newFrame {name, formals} =
    let
	val argument = ref 1
	fun getArgumentOffset () =
	    let
		val i = !argument
	    in
		argument := i+1; i * wordsize
	    end
	val formals' = map (fn escape => if escape
					 then InFrame (getArgumentOffset())
					 else InReg (Temp.newtemp()))
			   formals
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
