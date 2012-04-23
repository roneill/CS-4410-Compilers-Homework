
structure MipsFrame : FRAME =
struct

structure T=Tree
structure A=Assem
datatype access = InFrame of int | InReg of Temp.temp
type frame = {name: Temp.label,
	      frameOffset: int ref,
	      formals: access list}
datatype frag = PROC of {body: Tree.stm, frame: frame}
	      | STRING of Temp.label * string
type register = string
    
val wordSize = 4

val tempMap = Temp.Table.empty

fun getTemps (num) =
    let
	fun getTemps' (0, temps) = temps
	  | getTemps' (i, temps) = getTemps'(i - 1, Temp.newtemp()::temps)
    in
	getTemps'(num, [])
    end
    
val FP = Temp.newtemp()
val RV0 = Temp.newtemp()
val RV1 = Temp.newtemp()
val SP = Temp.newtemp()
val RA = Temp.newtemp()
val GP = Temp.newtemp()
val AT = Temp.newtemp()
val K0 = Temp.newtemp()
val K1 = Temp.newtemp()

val ZERO = Temp.newtemp()
	     
val specialregs = [SP, ZERO, GP, AT, K0, K1, FP]
val argregs = getTemps(4)
val calleesaves = RA::getTemps(8)
val callersaves = RV0::RV1::getTemps(10)

(*val tempRegisterPair =  [(ZERO, "$zero"),
			 (FP, "$fp"),
			 (RV0, "$v0"),
			 (RV1, "$v1"),
			 (SP, "$sp"),
			 (RA, "$ra"),
			 (GP, "$gp"),
			 (AT, "$at"),
			 (K0, "$k0"),
			 (K1, "$k1"),
			 (List.nth(argregs, 0), "$a0"),
			 (List.nth(argregs, 1), "$a1"), 
			 (List.nth(argregs, 2), "$a2"), 
			 (List.nth(argregs, 3), "$a3"),
			 (List.nth(calleesaves, 1), "$s0"),
			 (List.nth(calleesaves, 2), "$s1"), 
			 (List.nth(calleesaves, 3), "$s2"), 
			 (List.nth(calleesaves, 4), "$s3"), 
			 (List.nth(calleesaves, 5), "$s4"),
			 (List.nth(calleesaves, 6), "$s5"),
			 (List.nth(calleesaves, 7), "$s6"), 
			 (List.nth(calleesaves, 8), "$s7"),
			 (List.nth(callersaves, 2), "$t0"),
			 (List.nth(callersaves, 3), "$t1"), 
			 (List.nth(callersaves, 4), "$t2"), 
			 (List.nth(callersaves, 5), "$t3"), 
			 (List.nth(callersaves, 6), "$t4"),
			 (List.nth(callersaves, 7), "$t5"),
			 (List.nth(callersaves, 8), "$t6"), 
			 (List.nth(callersaves, 9), "$t7"), 
			 (List.nth(callersaves, 10), "$t8"),
			 (List.nth(callersaves, 11), "$t9")]*)

val tempRegisterPair =  [(ZERO, "$zero"),
			 (FP, "$fp"),
			 (RV0, "$v0"),
			 (SP, "$sp"),
			 (RA, "$ra"),
			 (GP, "$gp"),
			 (AT, "$at"),
			 (K0, "$k0"),
			 (K1, "$k1"),
			 (List.nth(calleesaves, 1), "$s0"),
			 (List.nth(calleesaves, 2), "$s1"), 
			 (List.nth(calleesaves, 3), "$s2"), 
			 (List.nth(calleesaves, 4), "$s3"), 
			 (List.nth(calleesaves, 5), "$s4"),
			 (List.nth(calleesaves, 6), "$s5"),
			 (List.nth(calleesaves, 7), "$s6"), 
			 (List.nth(calleesaves, 8), "$s7"),
			 (List.nth(callersaves, 2), "$t0"),
			 (List.nth(callersaves, 3), "$t1"),
			 (List.nth(callersaves, 4), "$t2")]
			
val tempMap = foldl Temp.Table.enter' Temp.Table.empty tempRegisterPair

val (registersAsTemps, registers) = ListPair.unzip tempRegisterPair

fun tempToString (t) =
    case Temp.Table.look(tempMap, t)
     of SOME s => s
      | NONE => "$"^Temp.makestring(t) 

fun str i = if (i < 0) 
	    then "-"^(Int.toString (~i))
	    else Int.toString i
	      
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

fun procEntryExit2 (frame, body) =
    body @
    [A.OPER{assem="",
	    src=specialregs@calleesaves,
	    dst=[], jump=SOME[]}]
    
fun procEntryExit3 (frame as {name=name, frameOffset=offset, formals=locals}, body) = 
    {prolog = "PROCEDURE " ^ Symbol.name name ^"\n",
      body = body,
      epilog = "END "^Symbol.name name ^"\n" }
    
fun allocLocal (frame:frame) escape =
    let
	val frameOffset = (#frameOffset frame)
	val newFrameOffset = !frameOffset - wordSize
    in
	if escape
	then (frameOffset := newFrameOffset;
	      InFrame (newFrameOffset))
	else InReg (Temp.newtemp())
    end

fun name (frame:frame) = (#name frame)
fun formals (frame:frame) = (#formals frame)
			    
(* Generates an instruction that loads a variable (given by an access) into a temp *)
fun loadInstr (temp, InFrame k) = A.OPER {assem="lw `d0, "^(str k)^"(`s0)\n",
					  src=[FP],
					  dst=[temp],
					  jump=NONE}
  | loadInstr (temp, InReg t) = A.OPER {assem="move `d0, `s0\n",
					  src=[t],
					  dst=[temp],
					  jump=NONE}
(* Generates an instruction that stores a variable (given by an access) into a temp *)
fun storeInstr (temp, InFrame k) = A.OPER {assem="sw `s0, "^(str k)^"(`s1)\n",
					  src=[temp, FP],
					  dst=[],
					  jump=NONE}
  | storeInstr (temp, InReg t) = A.OPER {assem="move `d0, `s0\n",
					  src=[temp],
					  dst=[t],
					  jump=NONE}

			    
(* fp is either a TEMP(FP) or a series of MEM and + instructins to fetch the frame pointer *)			    
fun exp (InFrame k) fp = T.MEM(T.BINOP(T.PLUS,fp,T.CONST(k)))
  | exp (InReg t) _ = T.TEMP t

(* This function may require extension for machine specific details *) 
fun externalCall (s, args) =
    T.CALL (T.NAME(Temp.namedlabel s), args)

end

