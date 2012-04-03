
structure MipsGen : CODEGEN =
 struct

structure T = Tree
structure A = Assem
structure Frame = MipsFrame	      
 
 fun codegen frame stm =
     let val ilist = ref nil
	 val calldefs = Frame.RV0::Frame.RA::Frame.calleesaves
	 fun emit x = ilist := x :: !ilist
	 val int  = Int.toString
	 fun result(gen) = let val t = Temp.newtemp() in gen t; t end
	 fun binopInstr T.PLUS = "add"
	   | binopInstr T.MINUS = "sub"
	   | binopInstr T.DIV = "div"
	   | binopInstr T.MUL = "mul"
	   | binopInstr _ = ErrorMsg.impossible("Unsupported operator")
	 fun munchArgs (args) =
	     let
		 val numArgs = length args
		 val numArgRegs = length Frame.argregs
		 val stackArgs = if (numArgs > numArgRegs)
				 then (numArgRegs - numArgs)
				 else (0)
		 val growSP = "addi `d0, `d0, -"^(int (Frame.wordSize * stackArgs))^"\n"
		 fun appendInstr(nil, _, str) = str
		   | appendInstr(arg::tail, i, str) =
		     let
			 val offset = ~(i-numArgRegs)*Frame.wordSize
			 val copyToStack = "sw `s"^ int i ^", "^int (offset)^"(`d0)\n"
			 val copyToReg  = "move `d"^(int (i+1)) ^", `s"^ (int i)^"\n"
		     in
			 if (i < numArgRegs)
			 then appendInstr(tail, i+1, copyToReg::str)
			 else appendInstr(tail, i+1, copyToStack::str)
		     end
		 val copyArgs = appendInstr(args, 0, nil)
		 val copyArgs' = if (stackArgs > 0)
				 then growSP::copyArgs
				 else copyArgs
		 val assembly = String.concat(copyArgs')
		 val _ = emit (A.OPER {assem=assembly,
    				       src=map munchExp args,
				       dst=[Frame.SP]@Frame.argregs,
				       jump=NONE})
	     in
		 nil
	     end     
	 and munchStm (T.SEQ(a,b)) = (munchStm a; munchStm b)
	   | munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS,e1,T.CONST i)),e2)) =
	     emit (A.OPER {assem="sw `s1, "^ int i ^"(`s0)\n",
    			   src=[munchExp e1, munchExp e2],
			   dst=[],jump=NONE})
	   | munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS,T.CONST i, e1)), e2)) =
	     emit (A.OPER {assem="sw `s1, "^ int i ^"(`s0) \n",
			   src=[munchExp e1, munchExp e2],
			   dst=[],jump=NONE})
	   | munchStm (T.MOVE(T.MEM(T.CONST i), e2)) =
	     emit (A.OPER {assem="sw `s0, "^ int i ^"($r0)\n",
			   src=[munchExp e2],
			   dst=[],jump=NONE})
	   | munchStm (T.MOVE(T.MEM(e1), e2)) =
	     emit (A.OPER {assem="sw `s1, 0(`s0)\n",
			   src=[munchExp e1, munchExp e2],
			   dst=[],jump=NONE})
	   | munchStm(T.MOVE(T.TEMP(t), T.CALL(e, args))) =
	     emit (A.OPER {assem="jal `s0\n"^ (*Jump to the function*)
				 "move "^Frame.tempToString(t)^", `d0\n", (*copy the return value into t*)
			   src=munchExp(e)::munchArgs(args),
			   dst=calldefs,
			   jump=NONE})
	   | munchStm(T.JUMP (T.NAME l,labels)) =
	     emit (A.OPER {assem="j `j0\n",
			   src=[],
			   dst=[],
			   jump=SOME labels})
	   | munchStm(T.CJUMP (T.EQ, e1, (T.CONST 0), t, f)) =
	     emit (A.OPER {assem="beqz `s0, `j0\n",
			   src=[munchExp e1],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.EQ, (T.CONST 0), e1, t, f)) =
	     emit (A.OPER {assem="beqz `s0, `j0\n",
			   src=[munchExp e1],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.GE, e1, (T.CONST 0), t, f)) =
	     emit (A.OPER {assem="bgez `s0, `j0\n",
			   src=[munchExp e1],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.GE, (T.CONST 0), e1, t, f)) =
	     emit (A.OPER {assem="blez `s0, `j0\n",
			   src=[munchExp e1],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.GT, e1, (T.CONST 0), t, f)) =
	     emit (A.OPER {assem="bgtz `s0, `j0\n",
			   src=[munchExp e1],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.GT, (T.CONST 0), e1, t, f)) =
	     emit (A.OPER {assem="bltz `s0, `j0\n",
			   src=[munchExp e1],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.LE, e1, (T.CONST 0), t, f)) =
	     emit (A.OPER {assem="blez `s0, `j0\n",
			   src=[munchExp e1],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.LE, (T.CONST 0), e1, t, f)) =
	     emit (A.OPER {assem="bgez `s0, `j0\n",
			   src=[munchExp e1],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.LT, e1, (T.CONST 0), t, f)) =
	     emit (A.OPER {assem="bltz `s0, `j0\n",
			   src=[munchExp e1],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.LT, (T.CONST 0), e1, t, f)) =
	     emit (A.OPER {assem="bgtz `s0, `j0\n",
			   src=[munchExp e1],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.NE, e1, (T.CONST 0), t, f)) =
	     emit (A.OPER {assem="bnez `s0, `j0\n",
			   src=[munchExp e1],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.NE, (T.CONST 0), e1, t, f)) =
	     emit (A.OPER {assem="bnez `s0, `j0\n",
			   src=[munchExp e1],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.NE, e1, e2, t, f)) =
	     emit (A.OPER {assem="bne `s0, `s1, `j0\n",
			   src=[munchExp e1, munchExp e2],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.EQ, e1, e2, t, f)) =
	     emit (A.OPER {assem="beq `s0, `s1, `j0",
			   src=[munchExp e1, munchExp e2],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.LT, e1, e2, t, f)) =
	     emit (A.OPER {assem="slt `d0, `s0, `s1\n"^
				 "bgtz `d0, `j0\n" ,
			   src=[munchExp e1, munchExp e2],
			   dst=[Temp.newtemp()],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.GE, e1, e2, t, f)) = 
	     emit (A.OPER {assem="slt `d0, `s0, `s1\n"^
				 "beqz `d0, `j0\n" ,
			   src=[munchExp e1, munchExp e2],
			   dst=[Temp.newtemp()],
			   jump=SOME [t,f]})
	     
	   | munchStm(T.MOVE(T.TEMP t1, T.TEMP t2)) =
	     emit (A.MOVE{assem="",
			      dst=t1,
			      src=t2})
	   | munchStm (T.MOVE(T.TEMP i, e2)) =
	     emit (A.OPER {assem="move `d0, `s0\n",
			   src=[munchExp e2],
			   dst=[i],jump=NONE})
	   | munchStm(T.EXP(T.CALL(e, args))) =
	     emit (A.OPER{assem="jal `s0\n",
			  src=munchExp(e)::munchArgs(args),
			  dst=calldefs,
			  jump=NONE})
	   | munchStm (T.LABEL lab) =
	     emit (A.LABEL {assem=Temp.toString(lab) ^ ":\n", lab=lab })
	   | munchStm x = Error.impossible "unmatched node"

	 and munchExp(T.MEM(T.BINOP(T.PLUS, e1, T.CONST i))) =
	     result(fn r => emit (A.OPER
				      {assem="lw `d0, "^ int i^"(`s0)\n",
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.MEM(T.BINOP(T.PLUS, T.CONST i, e1))) =
	     result (fn r => emit(A.OPER
				      {assem="lw `d0, "^ int i^"(`s0)\n",
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.MEM(T.CONST i)) =
	     result(fn r => emit(A.OPER
				     {assem="lw `d0, "^ int i^"($r0)\n",
				      src=[], dst=[r], jump=NONE}))
	   | munchExp(T.MEM(e1)) =
	     result (fn r => emit(A.OPER
				      {assem="lw `d0, 0(`s0)\n",
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.BINOP(T.PLUS, e1, T.CONST i)) =
	     result (fn r => emit(A.OPER
				      {assem="addi `d0, `s0, "^(int i)^"\n",
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.BINOP(T.PLUS, T.CONST i, e1)) =
	     result (fn r => emit(A.OPER
				      {assem="addi `d0, `s0, "^(int i^"\n"),
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.BINOP(T.MINUS, e1, T.CONST i)) =
	     result (fn r => emit(A.OPER
				      {assem="addi `d0, `s0, -"^(int (i))^"\n",
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.BINOP(oper, e1, e2)) =
	     result(fn r => emit(A.OPER
				     {assem=binopInstr(oper)^" `d0, `s0, `s1\n",
				      src=[munchExp e1, munchExp e2],
				      dst=[r],
				      jump=NONE}))
	   | munchExp(T.CONST i) =
	     result (fn r => emit(A.OPER
				      {assem="li `d0, "^(int i)^"\n",
				       src=[], dst=[r], jump=NONE}))
	   | munchExp(T.NAME lab) =
	     result(fn r => emit(A.OPER
				     {assem="la `d0, "^(Temp.toString(lab))^"\n",
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
