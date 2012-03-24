
structure MipsGen : CODEGEN =
 struct

structure T = Tree
structure A = Assem
structure Frame = MipsFrame	      
 
 fun codegen frame stm =
     let val ilist = ref nil
	 val calldefs = A.RV::A.RA::A.calleesaves
	 fun emit x = ilist := x :: !ilist
	 val int  = Int.toString
	 fun result(gen) = let val t = Temp.newtemp() in gen t; t end
	 fun binopInstr T.PLUS = "add"
	   | binopInstr T.MINUS = "sub"
	   | binopInstr T.DIV = "div"
	   | binopInstr T.MUL = "mul"
	   | binopInstr _ = ErrorMsg.impossible("Unsupported operator")
	 fun munchArgs (args) = [] (*TODO*)
	 fun munchStm (T.SEQ(a,b)) = (munchStm a; munchStm b)
	   | munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS,e1,T.CONST i)),e2)) =
	     emit (A.OPER {assem="sw 's1, "^ int i ^"('s0)\n",
    			   src=[munchExp e1, munchExp e2],
			   dst=[],jump=NONE})
	   | munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS,T.CONST i, e1)), e2)) =
	     emit (A.OPER {assem="sw 's1, "^ int i ^"('s0) \n",
			   src=[munchExp e1, munchExp e2],
			   dst=[],jump=NONE})
	   | munchStm (T.MOVE(T.MEM(T.CONST i), e2)) =
	     emit (A.OPER {assem="sw 's0, "^ int i ^"($r0)\n",
			   src=[munchExp e2],
			   dst=[],jump=NONE})
	   | munchStm (T.MOVE(T.MEM(e1), e2)) =
	     emit (A.OPER {assem="sw 's1, 0('s0)\n",
			   src=[munchExp e1, munchExp e2],
			   dst=[],jump=NONE})
	   | munchStm(T.MOVE(T.TEMP(t), T.CALL(e, args))) =
	     emit (A.OPER {assem="jal 's0\n"^ (*Jump to the function*)
				 "move "^Temp.makestring(t)^", 'd0", (*copy the return value into t*)
			   src=munchExp(e)::munchArgs(args),
			   dst=calldefs,
			   jump=NONE})
	   | munchStm (T.MOVE(T.TEMP i, e2)) =
	     emit (A.OPER {assem="move 'd0, 's0\n",
			   src=[munchExp e2],
			   dst=[i],jump=NONE})
	   | munchStm (T.LABEL lab) =
	     emit (A.LABEL {assem=Temp.toString(lab) ^ ":\n", lab=lab })

	 and munchExp(T.MEM(T.BINOP(T.PLUS, e1, T.CONST i))) =
	     result(fn r => emit (A.OPER
				      {assem="lw 'd0, "^ int i^"('s0)\n",
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.MEM(T.BINOP(T.PLUS, T.CONST i, e1))) =
	     result (fn r => emit(A.OPER
				      {assem="lw 'd0, "^ int i^"('s0)\n",
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.MEM(T.CONST i)) =
	     result(fn r => emit(A.OPER
				     {assem="lw 'd0, "^ int i^"($r0)\n",
				      src=[], dst=[r], jump=NONE}))
	   | munchExp(T.MEM(e1)) =
	     result (fn r => emit(A.OPER
				      {assem="lw 'd0, 0('s0)",
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.BINOP(T.PLUS, e1, T.CONST i)) =
	     result (fn r => emit(A.OPER
				      {assem="addi 'd0, 's0, "^int i,
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.BINOP(T.PLUS, T.CONST i, e1)) =
	     result (fn r => emit(A.OPER
				      {assem="addi 'd0, 's0, "^int i,
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.BINOP(T.MINUS, e1, T.CONST i)) =
	     result (fn r => emit(A.OPER
				      {assem="addi 'd0, 's0, "^int (~i),
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.BINOP(T.MINUS, T.CONST i, e1)) =
	     result (fn r => emit(A.OPER
				      {assem="addi 'd0, 's0, "^int (~i),
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.BINOP(oper, e1, e2)) =
	     result(fn r => emit(A.OPER
				     {assem=binopInstr(oper)^" 'd0, 's0, 's1",
				      src=[munchExp e1, munchExp e2],
				      dst=[r],
				      jump=NONE}))
	   | munchExp(T.CONST i) =
	     result (fn r => emit(A.OPER
				      {assem="li 'd0, "^ int i,
				       src=[], dst=[r], jump=NONE}))
	   | munchExp(T.NAME lab) =
	     result(fn r => emit(A.OPER
				     {assem="la 'd0, "^Temp.toString(lab),
				      src=[],
				      dst=[r],
				      jump=NONE}))
	   | munchExp(T.TEMP t) = t
	   | munchExp _ = Error.impossible(
			  "Could not find matching tile for expression")
     in
	 munchStm stm;
	 rev(!ilist)
     end
 end
