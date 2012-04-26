
structure MipsGen : CODEGEN =
 struct

structure T = Tree
structure A = Assem
structure Frame = MipsFrame	      


fun codegen frame stm =
     let val ilist = ref nil
	 val calldefs = Frame.RA::Frame.RV0::Frame.callersaves
	 fun emit x = ilist := x :: !ilist
	 fun str i = if (i < 0) 
		     then "-"^(Int.toString (~i))
		     else Int.toString i
	 fun result(gen) = let val t = Temp.newtemp() in gen t; t end
	 fun binopInstr T.PLUS = "add"
	   | binopInstr T.MINUS = "sub"
	   | binopInstr T.DIV = "div"
	   | binopInstr T.MUL = "mul"
	   | binopInstr _ = ErrorMsg.impossible("Unsupported operator")
	 fun relop0Instr T.EQ = "beqz"
	   | relop0Instr T.GE = "bgez"
	   | relop0Instr T.LE = "blez"
	   | relop0Instr T.GT = "bgtz"
	   | relop0Instr T.LT = "bltz"
	   | relop0Instr T.NE = "bnez"
	   | relop0Instr _ = ErrorMsg.impossible("Unsupported operator")
	 fun munchArgs (args) =
	     let
		 val numArgs = length args
		 val numArgRegs = length Frame.argregs
		 val growSP = "addi `d0, `d0, -"^
			      (str (Frame.wordSize * numArgs))^"\n"
		 fun appendInstr(nil, _, assem) = assem
		   | appendInstr(arg::tail, i, assem) =
		     let
			 val offset = (i+1)*Frame.wordSize
			 val copyToStack = "sw `s"^ str i ^", "^str (offset)^
					   "(`d0)\n"
			 val copyToReg  = "move `d"^(str (i+1))
					  ^", `s"^ (str i)^"\n"
		     in
			 if (i < numArgRegs)
			 then appendInstr(tail, i+1, copyToReg::assem)
			 else appendInstr(tail, i+1, copyToStack::assem)
		     end
		 val copyArgs = appendInstr(args, 0, nil)
		 val copyArgs' = growSP::copyArgs
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
	     emit (A.OPER {assem="sw `s1, "^ str i ^"(`s0)\n",
    			   src=[munchExp e1, munchExp e2],
			   dst=[],jump=NONE})
	   | munchStm (T.MOVE(T.MEM(T.BINOP(T.PLUS,T.CONST i, e1)), e2)) =
	     emit (A.OPER {assem="sw `s1, "^ str i ^"(`s0) \n",
			   src=[munchExp e1, munchExp e2],
			   dst=[],jump=NONE})
	   | munchStm (T.MOVE(T.MEM(T.CONST i), e2)) =
	     emit (A.OPER {assem="sw `s0, "^ str i ^"($r0)\n",
			   src=[munchExp e2],
			   dst=[],jump=NONE})
	   | munchStm (T.MOVE(T.MEM(e1), e2)) =
	     emit (A.OPER {assem="sw `s1, 0(`s0)\n",
			   src=[munchExp e1, munchExp e2],
			   dst=[],jump=NONE})
	   | munchStm(T.MOVE(T.TEMP(t), T.CALL(e, args))) =
	     emit (A.OPER {assem="jal `s0\n"^ (*Jump to the function*)
				 "move `d0, `s1\n",
			   src=munchExp(e)::Frame.RV0::munchArgs(args),
			   dst=t::calldefs,
			   jump=NONE})
	   | munchStm (T.MOVE(e1, (T.BINOP(T.PLUS, e2, T.CONST i)))) =
	     emit(A.OPER {assem="addi `d0, `s0, "^(str i)^"\n",
			  src=[munchExp e2],
			  dst=[munchExp e1],
			  jump=NONE})
	   | munchStm (T.MOVE(e1, (T.BINOP(T.PLUS, T.CONST i, e2)))) =
	     emit(A.OPER {assem="addi `d0, `s0, "^(str i)^"\n",
			  src=[munchExp e2],
			  dst=[munchExp e1], jump=NONE})
	   | munchStm (T.MOVE(e1, (T.BINOP(T.MINUS, e2, T.CONST i)))) =
	     emit(A.OPER {assem="addi `d0, `s0, -"^(str (i))^"\n",
			  src=[munchExp e2],
			  dst=[munchExp e1], jump=NONE})
	   | munchStm (T.MOVE(e1, (T.BINOP(binop, e2, e3)))) =
	     emit(A.OPER {assem=binopInstr(binop)^" `d0, `s0, `s1\n",
			  src=[munchExp e2, munchExp e3],
			  dst=[munchExp e1], jump=NONE})

	   | munchStm(T.MOVE(T.TEMP t1, T.TEMP t2)) =
	     emit (A.MOVE{assem="move `d0, `s0\n",
			      dst=t1,
			      src=t2})
	   | munchStm(T.MOVE(T.TEMP t1, T.CONST i)) =
	     emit (A.OPER{assem="li `d0, "^(str i)^"\n",
			      dst=[t1],
			      src=[], jump=NONE})
	   | munchStm (T.MOVE(T.TEMP i, e2)) =
	     emit (A.MOVE {assem="move `d0, `s0\n",
			   src=munchExp e2,
			   dst=i})

	   | munchStm(T.JUMP (T.NAME l,labels)) =
	     emit (A.OPER {assem="b `j0\n",
			   src=[],
			   dst=[],
			   jump=SOME labels})
	   | munchStm(T.CJUMP (relop, e1, (T.CONST 0), t, f)) =
	     emit (A.OPER {assem=relop0Instr(relop)^" `s0, `j0\n",
			   src=[munchExp e1],
			   dst=[],
			   jump=SOME [t,f]})
	   (* Commute the relop to reuse the operand*)
	   | munchStm(T.CJUMP (relop, (T.CONST 0), e1, t, f)) =
	     munchStm(T.CJUMP (Tree.commute(relop), e1, (T.CONST 0), t, f))
	   | munchStm(T.CJUMP (T.NE, e1, e2, t, f)) =
	     emit (A.OPER {assem="bne `s0, `s1, `j0\n",
			   src=[munchExp e1, munchExp e2],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.EQ, e1, e2, t, f)) =
	     emit (A.OPER {assem="beq `s0, `s1, `j0\n",
			   src=[munchExp e1, munchExp e2],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.LT, e1, e2, t, f)) =
	     emit (A.OPER {assem="blt `s0, `s1, `j0\n" ,
			   src=[munchExp e1, munchExp e2],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.GE, e1, e2, t, f)) = 
	     emit (A.OPER {assem="bge `s0, `s1, `j0\n" ,
			   src=[munchExp e1, munchExp e2],
			   dst=[],
			   jump=SOME [t,f]})
	   | munchStm(T.CJUMP (T.GT, e1, e2, t, f)) =
	     munchStm(T.CJUMP (T.LT, e1, e2, t, f))
	   | munchStm(T.CJUMP (T.LE, e1, e2, t, f)) =
	     munchStm(T.CJUMP (T.GE, e2, e1, t, f))
	   | munchStm(T.EXP(T.CALL(e, args))) =
	     emit (A.OPER{assem="jal `s0\n",
			  src=munchExp(e)::munchArgs(args),
			  dst=calldefs,
			  jump=NONE})
	   | munchStm(T.EXP(e1)) =
	     emit (A.OPER{assem="",
			  src=[munchExp(e1)],
			  dst=[],
			  jump=NONE})
	   | munchStm (T.LABEL lab) =
	     emit (A.LABEL {assem=Temp.toString(lab) ^ ":\n", lab=lab })
	   | munchStm x = (Printtree.printtree (TextIO.stdOut, x);
			   Error.impossible "unmatched node:")

	 and munchExp(T.CALL(e, args)) =
	     result(fn r => emit (A.OPER
				      {assem="jal `s0\n"^ (*Jump to the function*)
					     "move `d0, `s1\n",
				       (*copy the return values to r *)
				       src=munchExp(e)::Frame.RV0::munchArgs(args),
				       dst=r::calldefs,
				       jump=NONE}))

	   | munchExp(T.MEM(T.BINOP(T.PLUS, e1, T.CONST i))) =
	     result(fn r => emit (A.OPER
				      {assem="lw `d0, "^ str i^"(`s0)\n",
				       src=[munchExp e1], dst=[r], jump=NONE}))

	   | munchExp(T.MEM(T.BINOP(T.PLUS, T.CONST i, e1))) =
	     result (fn r => emit(A.OPER
				      {assem="lw `d0, "^ str i^"(`s0)\n",
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.MEM(T.CONST i)) =
	     result(fn r => emit(A.OPER
				     {assem="lw `d0, "^ str i^"($r0)\n",
				      src=[], dst=[r], jump=NONE}))
	   | munchExp(T.MEM(e1)) =
	     result (fn r => emit(A.OPER
				      {assem="lw `d0, 0(`s0)\n",
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.BINOP(T.PLUS, e1, T.CONST i)) =
	     result (fn r => emit(A.OPER
				      {assem="addi `d0, `s0, "^(str i)^"\n",
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.BINOP(T.PLUS, T.CONST i, e1)) =
	     result (fn r => emit(A.OPER
				      {assem="addi `d0, `s0, "^(str i)^"\n",
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.BINOP(T.MINUS, e1, T.CONST i)) =
	     result (fn r => emit(A.OPER
				      {assem="addi `d0, `s0, -"^(str (i))^"\n",
				       src=[munchExp e1], dst=[r], jump=NONE}))
	   | munchExp(T.BINOP(oper, e1, e2)) =
	     result(fn r => emit(A.OPER
				     {assem=binopInstr(oper)^" `d0, `s0, `s1\n",
				      src=[munchExp e1, munchExp e2],
				      dst=[r],
				      jump=NONE}))
	   | munchExp(T.CONST i) =
	     result (fn r => emit(A.OPER
				      {assem="li `d0, "^(str i)^"\n",
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
