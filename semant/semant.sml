structure A = Absyn
structure S = Symbol
structure Ty = Types
structure Tr = Translate
structure Error = ErrorMsg

signature ENV =
sig
    datatype enventry = VarEntry of {access: Tr.access, ty: Ty.ty}
		      | FunEntry of {level: Tr.level,
				     label: Temp.label,
				     formals: Ty.ty list, result: Ty.ty} 
    val base_tenv: Ty.ty S.table
    val base_venv: enventry S.table
    val toploopEnd: Temp.label
end

structure Env :> ENV =
struct

datatype enventry = VarEntry of {access: Tr.access, ty: Ty.ty}
		  | FunEntry of {level: Tr.level,
				 label: Temp.label,
				 formals: Ty.ty list, result: Ty.ty} 
				
val base_tenv = foldr S.enter' S.empty [ (S.symbol("int"), Ty.INT),
					 (S.symbol("string"), Ty.STRING) ]

val stdlib = map (fn (symbol, formals, result) =>
		     (S.symbol(symbol),
		      FunEntry {level=Tr.outermost,
				label=Temp.newlabel(),
				formals=formals, 
				result=result }))
		 [ ("print", [Ty.STRING], Ty.UNIT),
		   ("flush", [], Ty.UNIT),
		   ("getchar", [], Ty.STRING),
		   ("ord", [Ty.STRING], Ty.INT),
		   ("chr", [Ty.INT], Ty.STRING),
		   ("size", [Ty.STRING], Ty.INT),
		   ("substring", [Ty.STRING, Ty.STRING], Ty.STRING),
		   ("concat", [Ty.INT], Ty.STRING),
		   ("not", [Ty.INT], Ty.INT) ]
    
val base_venv = foldr S.enter' S.empty stdlib
		
val toploopEnd = Temp.newlabel()

end

structure Semant :sig val transProg : A.exp -> Translate.fraglist end =
struct 

type venv = Env.enventry Symbol.table
type tenv = Ty.ty Symbol.table
type expty = {exp:Tr.exp, ty: Ty.ty}

(* Check for proper nesting of break statements *)	      
fun checkInLoop (loopEnd, pos) =
    if  (loopEnd = Env.toploopEnd) 
    then (Error.error pos "break encountered outside of loop")
    else ()

(* Convert Ty to String *)		
fun stringTy (Ty.RECORD _) = "RECORD"
  | stringTy Ty.NIL = "NIL"
  | stringTy Ty.INT = "INT"
  | stringTy Ty.STRING ="STRING"
  | stringTy (Ty.ARRAY _) ="ARRAY"
  | stringTy (Ty.NAME (name, ty)) = ("NAME: " ^ (S.name name)) 
  | stringTy Ty.UNIT = "UNIT"
  | stringTy Ty.TOP = "TOP"
  | stringTy Ty.BOTTOM = "BOTTOM"
  | stringTy Ty.IMMUTABLE_INT = "IMMUTABLE_INT"		 

(* Check to see if an expression evaluates to an int *)				
fun checkInt ({exp, ty}, pos) =
    if Ty.lteq(ty, Types.INT) then ()
    else Error.error(pos) "exp was not an int"

fun checkInt' (ty, pos) =
    if Ty.lteq(ty, Types.INT) then ()
    else Error.error(pos) "exp was not an int"
	 
(* Check to see if an expression evaluates to an unit *)	 
fun checkUnit ({exp, ty}, pos) =
    if Ty.lteq(ty, Types.UNIT) then ()
    else Error.error(pos) "exp was not a unit"

fun checkUnit' (ty, pos) =
    if Ty.lteq(ty, Types.UNIT) then ()
    else Error.error(pos) "exp was not a unit"
	 
fun checkComparable ({exp=lexp, ty=lty},{exp=rexp, ty=rty}, pos) =
    if Ty.lteq(lty, rty) orelse Ty.lteq(rty, lty) then ()
    else Error.error(pos) ("The types "^(stringTy lty)^" and "^
			   (stringTy rty)^" are not comparable")

fun checkComparable' (lty,rty, pos) =
    if Ty.lteq(lty, rty) orelse Ty.lteq(rty, lty) then ()
    else Error.error(pos) ("The types "^(stringTy lty)^" and "^
			   (stringTy rty)^" are not comparable")	 
	 
(* Find the underlying type of a name *)	 
fun actual_ty typ =
    case typ of
	(Ty.NAME (id, ref(SOME(typ')))) => actual_ty typ'
      | anyTy => anyTy;

(* Check for duplicate declarations in mutually recursive types or functions *)
fun checkDuplicateDeclarations (names) = 
    let
	fun checkDuplicates(nil, checkedNames) = ()
	  | checkDuplicates(((name, pos)::tail), checkedNames) =
	    case S.look(checkedNames, name)
	     of SOME dName => (Error.error pos ("duplicate declaration: "
						^(S.name name)))
	      | NONE => checkDuplicates(tail, S.enter(checkedNames,
						      name, ref ()))
    in
	checkDuplicates(names, S.empty)
    end
    
fun transDec (level, loopEnd, exps, venv, tenv,
	      A.VarDec{name, escape, typ=NONE, init, pos}) = 
    let 
	val access = Tr.allocLocal(level) (!escape)
	val {exp, ty} = transExp(level, loopEnd, venv, tenv) init
	val assignExp = Tr.newAssign(Tr.simpleVar(access, level), exp)
    in
	if (ty = Ty.NIL)
	then (Error.error pos "Cannot assign expression to nil")
	else ();
	{tenv=tenv,
	 venv=S.enter(venv, name, Env.VarEntry{access=access, ty=ty}),
	 exps=assignExp::exps}
    end
  | transDec (level, loopEnd, exps, venv, tenv,
	      A.VarDec{name, escape, typ=SOME typ , init, pos}) =
    let
	val access = Tr.allocLocal(level) (!escape)
	val varTy = transTy(tenv, A.NameTy(typ))
	val {exp, ty} = transExp(level, loopEnd, venv, tenv) init
	val assignExp = Tr.newAssign(Tr.simpleVar(access, level), exp)
    in
	if (Ty.lteq ((actual_ty ty),(actual_ty varTy))) then ()
	else Error.error pos ("The types of the expression: "^
			      (stringTy (actual_ty varTy))^
			      " and initializer "^
			      (stringTy (actual_ty ty))^
			      " type do not match");
	{tenv=tenv,
	 venv=S.enter(venv, name, Env.VarEntry{access=access, ty=ty}),
	 exps=assignExp::exps}
    end
  | transDec (level, loopEnd, exps, venv, tenv, A.TypeDec(typedecs)) =
    let
	fun enterTypeHeader ({name, ty, pos}, tenv) =
	    S.enter(tenv, name, Ty.NAME(name,ref NONE))
	val tenv' = foldl enterTypeHeader tenv typedecs
	fun checkTypeBody ({name, ty, pos}) =
	    case S.look(tenv', name)
	     of SOME (Ty.NAME (name, body)) => body := SOME (transTy(tenv', ty))
	      | _ => Error.impossible "Looking up type header failed"

	(* Check for cycles in recursive type name declarations *)	     
	fun checkForCycles (tenv, {name, ty, pos}::tail) =
	    let 
		(* Only check cycles of NAMEs.
		 * Only stop when anyother type is found *)
		fun hasCycle (Ty.NAME (name, body), visited) =
		    (* visited is a table of name's that we've visited *)
		    (case S.look (visited, name)
		      of SOME _ =>
			 (Error.error pos
			   ("cycle inmutually recursive type definition");
			  true)
		       | NONE => hasCycle(getOpt(!body,Ty.BOTTOM),
					  S.enter(visited, name, ref ())))    
		  | hasCycle (_,_) = (false)
			     
	    in
		case S.look (tenv, name)
		 of SOME ty => if (hasCycle (ty,S.empty)) then () 
			       else checkForCycles(tenv, tail)
		  | NONE => Error.impossible "Cyclic type checking error"
	    end
	  | checkForCycles (tenv, nil) = () 
    in
	map checkTypeBody typedecs;
	checkForCycles(tenv', typedecs);
	checkDuplicateDeclarations(map (fn x => (#name x, #pos x)) typedecs);
	{venv=venv, tenv=tenv', exps=exps}
    end
  | transDec(level, loopEnd, exps, venv, tenv, A.FunctionDec(fundecs)) =
    let
	fun getResultTy (result) = case result
				    of SOME(rt, pos) =>
				       (case S.look(tenv, rt)
					 of SOME ty => ty
					  | NONE =>
					    (Error.error pos
						"return type undeclared";
					     Ty.BOTTOM))
				     | NONE => Ty.UNIT 
	fun transparam {name, escape, typ, pos}  =
	    case S.look(tenv, typ)
	     of SOME t => {name=name, ty=t}
	      | NONE => (Error.error pos ("parameter type "^
					  (S.name typ)^
					  " undeclared");
			 {name=name, ty=Ty.BOTTOM})
	fun enterFunHeader ({name,params,body,pos,result}, venv) =
	    let 
		val formals = map (fn p => !(#escape p)) params
		val level' = Tr.newLevel{parent=level, 
					 name=Temp.newlabel(), 
					 formals=formals}
		val result_ty = getResultTy result
		val params' = map transparam params
	    in
		S.enter(venv, name, Env.FunEntry{level=level', 
						 label=Temp.newlabel(),
						 formals= map #ty params',
						 result=result_ty})
	    end
	val venv' = foldl enterFunHeader venv fundecs
	fun checkFunBody ({name=funName,params,body,pos,result}) =
	    let
		val result_ty = getResultTy result
		(* we need to get accesses (Translate.access) for each of
		 *the params. Look up the formals (access list) of the
		 * function from the venv *)
		val level = case S.look(venv',funName) 
			     of SOME (Env.FunEntry {level,
						    label,
						    formals,
						    result}) => 
				level
			      | _ => Error.impossible 
				"checkFunBody did not find function header"
		val formals = Tr.formals level
		val params_access = ListPair.zip(params,formals)
		val params' = map (fn (p,a) => 
				      let
					  val param = transparam p
					  val name = #name param
					  val ty = #ty param
				      in
					{name=name,ty=ty,access=a}
				      end )
				  params_access
		val venv'' =  foldl (fn ({name=varName, ty, access}, venv) => 
					S.enter(venv, 
						varName, 
						Env.VarEntry{access=access,
							     ty=ty}))
				    venv'
				    params'
		val {exp=bodyexp, ty=bodyty} = transExp(level,
							loopEnd,
							venv'',
							tenv) body
	    in
		if (actual_ty bodyty = actual_ty result_ty)
		then (Tr.procEntryExit{level=level,body=bodyexp})
		else (Error.error pos ("return type of body: "^
				       (stringTy (actual_ty bodyty))^
				       " does not match declaration: "^
				       (stringTy (actual_ty result_ty))))
	    end
    in
	map checkFunBody fundecs;
	checkDuplicateDeclarations(map (fn x => (#name x, #pos x)) fundecs);
	{venv=venv', tenv=tenv,  exps=exps}
    end
    
and transDecs (level, loopEnd, venv, tenv, decs) =
    foldr (fn (dec, {venv, tenv, exps}) => 
	      transDec (level, loopEnd, exps, venv, tenv, dec))
	  {venv=venv,tenv=tenv, exps=[]}
	  decs
    
and transTy (tenv, A.NameTy(symbol,pos)) =
    (case S.look(tenv,symbol)
      of SOME ty =>  ty
       | NONE => (Error.error pos ("type "^
				   (S.name symbol)^
				   " not defined"); Ty.INT))
  | transTy (tenv, A.RecordTy(fields)) =
    let
	val flds = map (fn x => (#name x,
				 transTy(tenv, A.NameTy(#typ x, #pos x))))
		       fields 
	val uniq = ref ()
    in
	Ty.RECORD(flds, uniq)
    end
  | transTy (tenv, A.ArrayTy(symbol,pos)) =
    (case S.look(tenv,symbol)
      of SOME ty => Ty.ARRAY(ty, ref ())
       | NONE => (Error.error pos "type not defined"; Ty.INT))
    
and transExp (level, loopEnd, venv, tenv) =
    let fun trexp (A.VarExp var) = trvar var
	  | trexp (A.NilExp) = {exp=(Tr.nil()), ty=Types.NIL}			       
	  | trexp (A.IntExp i) = {exp=(Tr.newInt(i)), ty=Types.INT}
	  | trexp (A.StringExp(s, pos)) = {exp=(Tr.newString(s)),
					   ty=Types.STRING}
	  | trexp (A.CallExp{func, args, pos}) = 
	    (case S.look(venv, func)
	      of SOME (Env.FunEntry{level=funlevel, label, formals, result}) =>
		 let
		     fun compareArgs (formal, arg) =
			 let
			     val actualFormal = actual_ty formal
			     val actualArg = actual_ty arg
			 in
			     if actualFormal = actualArg then ()
			     else (Error.error pos
					       ((stringTy actualFormal)^
						" wrong argument type "^
						(stringTy actualArg)))
			 end
		     val exptyList = map trexp args
		     val argTypes = map #ty exptyList
		     val argExps = map #exp exptyList
		     val pairs = ListPair.zipEq(formals, argTypes)
			 handle UnequalLengths =>
				(Error.error pos
				((S.name func)^
				 " has incorrect number of arguments");
				 [])
		 in
		     map compareArgs pairs;
		     {exp=Tr.callFun(label,
				     argExps,
				     level,
				     funlevel),
		      ty=result}
		 end
	       | _ => (Error.error pos ("function name: "^
					(S.name func)^
					" not declared");
		       {exp=(Tr.NOP()), ty=Ty.UNIT}))
	  | trexp (A.OpExp{left, oper, right, pos}) = 
	    let
		fun checkArithmetic(translate) =
		    let
			val {exp=lexp, ty=lty} = trexp left
			val {exp=rexp, ty=rty} = trexp right
		    in
			(checkInt'(lty, pos);
			 checkInt'(rty, pos);
			 {exp=(translate(lexp, rexp)), ty=Types.INT})
		    end
		     
		fun checkCompat(translate) =
		    let
			val {exp=lexp, ty=lty} = trexp left
			val {exp=rexp, ty=rty} = trexp right
		    in
			(checkComparable'(lty, rty, pos);
			 {exp=(translate(lexp, rexp)), ty=Types.INT})
		    end
	    in
		case oper
		 of A.PlusOp => checkArithmetic(Tr.plus)
		  | A.MinusOp => checkArithmetic(Tr.minus)
		  | A.TimesOp =>  checkArithmetic(Tr.times)
		  | A.DivideOp => checkArithmetic(Tr.divide)
		  | A.EqOp => checkCompat(Tr.eq)
		  | A.NeqOp => checkCompat(Tr.neq)
		  | A.LtOp => checkArithmetic(Tr.lt)
		  | A.LeOp => checkArithmetic(Tr.le)
		  | A.GtOp => checkArithmetic(Tr.gt)
		  | A.GeOp => checkArithmetic(Tr.ge)
	    end
	  | trexp (A.RecordExp{fields, typ, pos}) =
	    let
		val defRecType =
		    case S.look(tenv, typ)
		     of SOME ty => actual_ty ty
		      | NONE => (Error.error pos ("record type: "^(S.name typ)^
						  " not declared");
				 Ty.BOTTOM)
		val defFields =
		    case defRecType
		     of Ty.RECORD (fields, unique) => fields
		      | Ty.BOTTOM => [] (* record error already encountered*)
		      | _ => (Error.error pos
					  ("identifier: "^(stringTy defRecType)^
					   " was not a record");
			      [])
		fun trfield (symbol, exp, pos) : Tr.exp =
		    let
			val {exp=fldExp, ty=fldTy} = trexp exp
			fun lookupFieldTy' (id, nil) =
			    (Error.error pos ("record field: "^(S.name symbol)^
					      " not declared");
			     Ty.BOTTOM)
			  | lookupFieldTy' (id, ((recID, ty)::tail)) =
			    if (id = recID) then ty
			    else lookupFieldTy'(id, tail)
			and lookupFieldTy (id:S.symbol) =
			    if (defFields = nil)
			    then Ty.BOTTOM (* record error already encountered*)
			    else lookupFieldTy' (id, defFields)
			val ty = actual_ty (lookupFieldTy(symbol))
			val fldTy = actual_ty fldTy
		    in
			(if (ty = Ty.BOTTOM)
			then () (* record error already encountered*) 
			else
			    if (Ty.lteq(fldTy,ty))
			    then () (* successful typecheck *)
			    else (Error.error pos
					      ("record field initializer: "
					       ^stringTy fldTy^
					       " does not match defined type: "
					       ^stringTy ty));
			 
			 fldExp)
		    end
		val fieldExps = map trfield fields
	    in
		case fieldExps 
		 of [] => (* record error already encountered*)
		    {exp=Tr.NOP(), ty=defRecType}
		  | _ => {exp=Tr.newRecord(fieldExps), ty=defRecType} 
	    end
	  | trexp (A.SeqExp(nil)) = {exp=(Tr.NOP()), ty=Types.UNIT }
	  | trexp (A.SeqExp [(exp,pos)]) = trexp(exp)
	  | trexp (A.SeqExp(exps)) =
	    let fun checkExps ((exp, pos)::nil, acc) =
		    let
			val {exp=exp', ty=ty'} = trexp(exp)
		    in
			{exp=Tr.seqexp(acc, exp'), ty=ty'}
		    end
		  | checkExps ((exp, pos)::tail, acc) =
		    let
			val {exp=exp', ty=ty'} = trexp(exp)
		    in
			checkExps(tail, exp'::acc)
		    end
	    in
		checkExps(exps, [])
	    end
	  | trexp (A.AssignExp{var, exp, pos}) =
	    let
		val {exp=varExp, ty=varTy} = trvar(var)
		val {exp=expExp, ty=expTy} = trexp(exp)
	    in
		if(Ty.lteq(varTy, expTy)) then ()
		else (Error.error pos ("cannot assign expression of type: "^
				       (stringTy expTy)^
				       " to variable of type: "^
				       (stringTy varTy)));
		{exp=Tr.newAssign(varExp, expExp), ty=Ty.UNIT}
	    end
	  | trexp (A.IfExp {test, then', else'=NONE, pos}) =
	    let
		val {exp=testExp, ty=testTy} = trexp(test)
		val {exp=thenExp, ty=thenTy} = trexp(then')
	    in
		(checkInt'(testTy, pos);
		 checkUnit'(thenTy, pos);
		 {exp=(Tr.ifExp(testExp, thenExp, Tr.NOP())), ty=Types.UNIT })
	    end 
	  | trexp (A.IfExp {test, then', else'=SOME elseBody, pos}) =
	     let
		 val {exp=testExp, ty=testTy} = trexp(test);
		 val {exp=thenExp, ty=thenTy} = trexp(then');
		 val {exp=elseExp, ty=elseTy} = trexp(elseBody);
	     in
		 checkInt'(testTy, pos);
		 if (Ty.lteq(thenTy, elseTy) orelse Ty.lteq(elseTy,thenTy)) then ()
		 else Error.error pos ("the type of the then clause: "^
				       (stringTy thenTy)^
				       " and else clause: "^
				       (stringTy elseTy)^ " do not match");
		 {exp=Tr.ifExp(testExp, thenExp, elseExp),
		  ty=Ty.join(thenTy,elseTy) }
	     end
	  | trexp (A.WhileExp{test, body, pos}) =
	    let 
		val loopEnd = Temp.newlabel();
		val {exp=testexp, ty=testty} =
		    transExp(level, loopEnd, venv, tenv) test
		val {exp=bodyexp, ty=bodyty} =
		    transExp(level, loopEnd, venv, tenv) body
	    in 
		checkInt'(testty, pos);
		checkUnit'(bodyty, pos);
		{exp=Tr.newLoop(testexp, bodyexp, loopEnd), ty=Types.UNIT}
	    end 
	  | trexp (A.ForExp{var, escape,
			    lo, hi, body, pos}) =
	    let
		val vardec = A.VarDec{name=var,
				      escape=escape,
				      typ=SOME (S.symbol("int"), pos),
				      init=lo,
				      pos=pos}
		val limit = A.VarDec{name=S.symbol("limit"),
				     escape=escape,
				     typ=SOME(S.symbol("int"), pos),
				     init=hi,
				     pos=pos}
		val decs = [vardec, limit]
		val aexp = A.AssignExp{var=A.SimpleVar(var,pos),
				       exp=A.OpExp{oper=A.PlusOp, 
						   left=(A.VarExp(
							 A.SimpleVar(var,pos))),  
						   right=A.IntExp(1),
						   pos=pos},
				       pos=pos}
		val wbody = A.SeqExp([(body,pos),(aexp,pos)])
		val whileExp = A.WhileExp{test=A.OpExp{oper=A.LeOp, 
						       left=(A.VarExp(
							     A.SimpleVar(
							     var,pos))),
						       right=A.VarExp(
						       A.SimpleVar
							   (S.symbol("limit"),
							 pos)),
						      pos=pos},
					  body=wbody,
					  pos=pos}
		val letexp = A.LetExp{decs=decs, body=whileExp, pos=pos}
	    in
		trexp(letexp)
	    end
	  | trexp (A.BreakExp pos) = (checkInLoop(loopEnd, pos);
				      {exp=Tr.newBreak(loopEnd), ty
								 =Types.BOTTOM})
	  | trexp (A.LetExp{decs, body,pos}) =
	    let val {venv=venv', tenv=tenv', exps=exps} =
		    transDecs(level, loopEnd, venv,tenv,decs)
		val {exp=bodyExp, ty=bodyTy} =
		    transExp(level,loopEnd, venv', tenv') body
		val exps = Tr.varDecs(exps)
	    in
		{exp=Tr.newLet(exps, bodyExp), ty=bodyTy}
	    end
	  | trexp (A.ArrayExp{typ, size, init, pos}) =
	    let
		val {exp=sizeExp, ty=sizeTy} = trexp size
		val {exp=initExp, ty=initTy} = trexp init
	    in
	    (case S.look(tenv, typ)
	      of SOME ty =>
		 (case actual_ty ty
		   of (Ty.ARRAY(ty, unique)) =>
		      (checkInt'(sizeTy, pos);
		       if ((actual_ty ty) = (actual_ty initTy)) then ()
		       else (Error.error pos ("wrong initial value type of "
					      ^(stringTy initTy)));
		       {exp=Tr.newArray(sizeExp, initExp),
			ty=Ty.ARRAY(ty, unique) })
		    | _ => (Error.error pos ((S.name typ)^" is not array type");
			    {exp=(Tr.NOP()), ty=Ty.BOTTOM }))
	       | NONE => (Error.error pos "Array type not defined";
			  {exp=(Tr.NOP()), ty=Ty.BOTTOM }))
	    end
	and trvar (A.SimpleVar(id, pos)) =
	    (case S.look(venv, id)
	      of SOME (Env.VarEntry{access, ty}) =>
		 {exp=Tr.simpleVar(access, level), ty=actual_ty ty}
	       | _ => (Error.error pos ("undefined variable: " ^ S.name id);
		       {exp=(Tr.NOP()), ty=Types.BOTTOM}))
	  | trvar (A.FieldVar(var, id, pos)) =
	    let
		val {exp=varExp, ty=varTy} = trvar(var)
		(* Get the type, and index in the list of a field *)
		fun getField (fields) = getField'(fields, 0)
		and getField' (nil, index) =
		    (Error.error(pos) ("field: \""^(S.name id)^
				       "\" not found in record");
		     (Ty.BOTTOM, index))
		  | getField' ((name,ty)::tail, index) =
		    if (id = name) then (ty,index)
		    else getField'(tail, index + 1)
	    in
		(case actual_ty varTy
		  of Ty.RECORD (fields,unique) =>
		    let
			val (ty, index) = getField(fields)
		    in
			{exp=Tr.fieldVar(varExp, Tr.newInt(index)), ty=ty}
		    end
		   | _ => (Error.error pos
			   ("Attempt access field of a non-record "^
					(stringTy varTy));
			   {exp=(Tr.NOP()), ty=Ty.BOTTOM}))
	    end
	  | trvar (A.SubscriptVar(var, exp, pos)) =
	    let
		val {exp=varExp, ty=varTy} = trvar(var)
		val {exp=expExp, ty=expTy} = trexp(exp)
	    in
		(checkInt'(expTy,pos);
		 case actual_ty varTy
		  of Ty.ARRAY (ty, unique) =>
		     {exp=Tr.subscriptVar(varExp, expExp), ty=ty}
		   | _ => (Error.error pos ("Attempt to index a non-array "^
					    stringTy varTy);
			   {exp=(Tr.NOP()), ty=Ty.BOTTOM}))
	    end
    in
	trexp
    end
    
fun transProg ast = 
    let
	val _ = Tr.initResult()
	val level = Tr.newLevel{parent=Tr.outermost, 
				name=Temp.newlabel(), 
				formals=[]}
	val _ = FindEscape.findEscape(ast);
	val {exp, ty} =  transExp(level,
				  Env.toploopEnd,
				  Env.base_venv,
				  Env.base_tenv)
				 ast;
	val _ = Tr.procEntryExit{body=exp, level=level}
    in	 
	 Tr.getResult()
    end
end
