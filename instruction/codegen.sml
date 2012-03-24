
structure MipsGen : CODEGEN =
 struct

structure T = Tree
structure A = Assem
structure Frame = MipsFrame	      
 
 fun codegen frame stm =
     let val ilist = ref nil
	 fun emit x = ilist := x :: !ilist
	 val int  = Int.toString
	 fun result(gen) = let val t = Temp.newtemp() in gen t; t end
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
	   | munchExp(T.CONST i) =
	     result (fn r => emit(A.OPER
				      {assem="li 'd0, "^ int i,
				       src=[], dst=[r], jump=NONE}))
	   | munchExp(T.BINOP(T.PLUS, e1, e2)) =
	     result(fn r => emit(A.OPER
				     {assem="add 'd0, 's0, 's1",
				      src=[munchExp e1, munchExp e2],
				      dst=[r],
				      jump=NONE}))
	   | munchExp(T.TEMP t) = t
     in
	 munchStm stm;
	 rev(!ilist)
     end
 end
