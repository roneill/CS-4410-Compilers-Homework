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
    val in_loop: int ref
end

structure Env :> ENV =
struct

datatype enventry = VarEntry of {access: Tr.access, ty: Ty.ty}
		  | FunEntry of {level: Tr.level,
				 label: Temp.label,
				 formals: Ty.ty list, result: Ty.ty} 
				
val base_tenv = foldr S.enter' S.empty [ (S.symbol("int"), Ty.INT),
					 (S.symbol("string"), Ty.STRING) ]

val base_venv = foldr S.enter' S.empty 
		      [ (S.symbol("print"),
			 FunEntry {level=Tr.outermost,
				   label=Temp.newlabel(),
				   formals=[Ty.STRING], 
				   result=Ty.UNIT }),
			(S.symbol("flush"),
			 FunEntry {level=Tr.outermost,
				   label=Temp.newlabel(), 
				   formals=[], 
				   result=Ty.UNIT}),
			(S.symbol("getchar"),
			 FunEntry {level=Tr.outermost,
				   label=Temp.newlabel(),
				   formals=[], 
				   result=Ty.STRING}),
			(S.symbol("ord"),
			 FunEntry {level=Tr.outermost, 
				   label=Temp.newlabel(),
				   formals=[Ty.STRING], 
				   result=Ty.INT}),
			(S.symbol("chr"),
			 FunEntry {level=Tr.outermost, 
				   label=Temp.newlabel(),
				   formals=[Ty.INT], 
				   result=Ty.STRING}),
			(S.symbol("size"),
			 FunEntry {level=Tr.outermost, 
				   label=Temp.newlabel(),
				   formals=[Ty.STRING], 
				   result=Ty.INT}),
			(S.symbol("substring"),
			 FunEntry {level=Tr.outermost,
				   label=Temp.newlabel(), 
				   formals=[Ty.STRING, Ty.INT, Ty.INT],
				   result=Ty.STRING}),
			(S.symbol("concat"),
			 FunEntry {level=Tr.outermost,
				   label=Temp.newlabel(), 
				   formals=[Ty.STRING, Ty.STRING],
				   result=Ty.STRING}),
			(S.symbol("not"),
			 FunEntry {level=Tr.outermost, 
				   label=Temp.newlabel(),
				   formals=[Ty.INT], 
				   result=Ty.INT}),
			(S.symbol("exit"),
			 FunEntry {level=Tr.outermost,
				   label=Temp.newlabel(), 
				   formals=[Ty.INT], 
				   result=Ty.UNIT}) ]
val in_loop = ref 0
end

structure Semant :sig val transProg : A.exp -> unit end =
struct 

type venv = Env.enventry Symbol.table
type tenv = Ty.ty Symbol.table
type expty = {exp:Tr.exp, ty: Ty.ty}

(* Check for proper nesting of break statements *)	      
fun checkInLoop (pos) =
    if !Env.in_loop > 0 then ()
    else Error.error pos "break encountered outside of loop"

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

(* Get the type of a field *)    
fun getType (nil, id, pos) = (Error.error(pos)
					 ("field: \""^
					  (S.name id)^
					  "\" not found in record"); Ty.BOTTOM)
  | getType ((name,ty)::tail, id, pos) = if (id = name) then ty
					 else getType(tail, id, pos)

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
    
fun transDec (level,venv, tenv, A.VarDec{name, escape, typ=NONE, init, pos}) = 
    let 
	val access = Tr.allocLocal(level) (!escape)
	val {exp, ty} = transExp(level,venv, tenv) init
    in
	if (ty = Ty.NIL)
	then (Error.error pos "Cannot assign expression to nil")
	else ();
	{tenv=tenv, venv=S.enter(venv, name, Env.VarEntry{access=access, ty=ty})}
    end
  | transDec (level, venv, tenv, A.VarDec{name, escape, typ=SOME typ , init, pos}) =
    let
	val access = Tr.allocLocal(level) (!escape)
	val varTy = transTy(tenv, A.NameTy(typ))
	val {exp, ty} = transExp(level, venv, tenv) init
    in
	if (Ty.lteq ((actual_ty ty),(actual_ty varTy))) then ()
	else Error.error pos ("The types of the expression: "^
			      (stringTy (actual_ty varTy))^
			      " and initializer "^
			      (stringTy (actual_ty ty))^
			      " type do not match");
	{tenv=tenv, venv=S.enter(venv, name, Env.VarEntry{access=access, ty=ty})}
    end
  | transDec (level,venv, tenv, A.TypeDec(typedecs)) =
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
		(* Only check cycles of NAMEs. Only stop when anyother type is found *)
		fun hasCycle (Ty.NAME (name, body), visited) =
		    (* visited is a table of name's that we've visited *)
		    (case S.look (visited, name)
		      of SOME _ =>
			 (Error.error pos
				      ("cycle in mutually recursive type definition");
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
	{venv=venv, tenv=tenv'}
    end
  | transDec(level, venv, tenv, A.FunctionDec(fundecs)) =
    let
	fun getResultTy (result) = case result
				    of SOME(rt, pos) => (* function has return value *)
				       (case S.look(tenv, rt)
					 of SOME ty => ty
					  | NONE =>
					    (Error.error pos
						"return type undeclared";
					     Ty.BOTTOM))
				     | NONE => Ty.UNIT  (* procedure returns no value *)
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
		(* we need to get accesses (Translate.access) for each of the params.
		 * Look up the formals (access list) of the function from the venv *)
		val level = case S.look(venv',funName) 
			     of SOME (Env.FunEntry {level, label, formals, result}) => 
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
		val {exp=bodyexp, ty=bodyty} = transExp(level,venv'', tenv) body
	    in
		if (actual_ty bodyty = actual_ty result_ty) then ()
		else (Error.error pos ("return type of body: "^
				       (stringTy (actual_ty bodyty))^
				       " does not match declaration: "^
				       (stringTy (actual_ty result_ty))))
	    end
    in
	map checkFunBody fundecs;
	checkDuplicateDeclarations(map (fn x => (#name x, #pos x)) fundecs);
	{venv=venv', tenv=tenv}
    end
    
and transDecs (level, venv, tenv, decs) =
    foldl (fn (dec, {venv,tenv}) => 
	      transDec (level,venv,tenv,dec))
	  {venv=venv,tenv=tenv} 
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
    
and transExp (level, venv, tenv) =
    let fun trexp (A.VarExp var) = trvar var
	  | trexp (A.NilExp) = {exp=(), ty=Types.NIL}			       
	  | trexp (A.IntExp i) = {exp=(), ty=Types.INT}
	  | trexp (A.StringExp(s, pos)) = {exp=(), ty=Types.STRING}
	  | trexp (A.CallExp{func, args, pos}) = 
	    (case S.look(venv, func)
	      of SOME (Env.FunEntry{level, label, formals, result}) =>
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
		     val argTypes = map (fn arg => (#ty (trexp arg))) args
		     val pairs = ListPair.zipEq(formals, argTypes)
			 handle UnequalLengths =>
				(Error.error pos
					     ((S.name func)^
					      " has incorrect number of arguments");
				 [])
		 in
		     map compareArgs pairs;
		     {exp=(), ty=result}
		 end
	       | _ => (Error.error pos ("function name: "^
					(S.name func)^
					" not declared");
		       {exp=(), ty=Ty.UNIT}))
	  | trexp (A.OpExp{left, oper, right, pos}) = 
	    let
		fun checkArithmetic(translate) =
		    let
			val {exp=lexp, ty=lty} = trexp left
			val {exp=rexp, ty=rty} = trexp right
		    in
			(checkInt'(lty, pos);
			 checkInt'(rty, pos);
		    end
		     {exp=(translate(lexp, rexp)), ty=Types.INT})
		fun checkCompat(translate) =
		    let
			val {exp=lexp, ty=lty} = trexp left
			val {exp=rexp, ty=rty} = trexp right
		    in
			(checkComparable(lty, rty, pos);
			 {exp=(translate(lexp, rexp)), ty=Types.INT})
		    end
		    
		    (checkComparable(trexp left, trexp right, pos);
		     {exp=(), ty=Types.INT})
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
	    (case S.look(tenv, typ)
	      of SOME ty =>
		 (case actual_ty ty
		   of (Ty.RECORD(recFields, unique)) =>
		      (let fun lookupID (id, nil) =
			       (Error.error pos "element not found"; NONE)
			     | lookupID (id, ((recID, ty)::tail)) =
			       if (id = recID) then SOME ty
			       else lookupID(id, tail)
			   and loopFields nil = ()
			     | loopFields ((symbol, exp, pos)::tail) =
			       case lookupID(symbol, recFields)
				of SOME ty => if (ty = #ty(trexp exp)) then ()
					      else loopFields(tail)
				 | NONE => (Error.error pos ("record field: "^
							     (S.name symbol)^
							     " not declared"))
		       in
			   loopFields(fields)
		       end;
		       {exp=(), ty=(Ty.RECORD(recFields, unique))})
		    | _ => (Error.error pos ("identifier: "^
					     (stringTy ty)^
					     " was not a record");
			    {exp=(), ty=Ty.INT}))
	       | NONE => (Error.error pos ("record type: "^
					   (S.name typ)^
					   " not declared");
			  {exp=(), ty=Ty.INT}))
	  | trexp (A.SeqExp(exps)) =
	    let fun checkExps nil = {exp=(), ty=Types.UNIT }
		  | checkExps ((exp, pos)::nil) = trexp(exp)
		  | checkExps ((exp, pos)::tail) = (trexp(exp); checkExps(tail))
	    in
		checkExps(exps)
	    end
	  | trexp (A.AssignExp{var, exp, pos}) =
	    let
		val varType = #ty (trvar(var))
		val expType = #ty (trexp(exp))
	    in
		if(Ty.lteq(expType,varType)) then ()
		else (Error.error pos ("cannot assign expression of type: "^
				       (stringTy expType)^
				       " to variable of type: "^
				       (stringTy varType)));
		{exp=(), ty=Ty.UNIT}
	    end
	  | trexp (A.IfExp {test, then', else'=NONE, pos}) =
	    (checkInt (trexp(test), pos);
	     checkUnit(trexp(then'), pos);
	     {exp=(), ty=Types.UNIT })
	  | trexp (A.IfExp {test, then', else'=SOME elseBody, pos}) =
	    (checkInt (trexp(test), pos);
	     let
		 val {exp=thenExp, ty=thenTy} = trexp(then');
		 val {exp=elseExp, ty=elseTy} = trexp(elseBody);
	     in
		 if (Ty.lteq(thenTy, elseTy) orelse Ty.lteq(elseTy,thenTy)) then ()
		 else Error.error pos ("the type of the then clause: "^
				       (stringTy thenTy)^
				       " and else clause: "^
				       (stringTy elseTy)^ " do not match");
		 {exp=(), ty=Ty.join(thenTy,elseTy) }
		 
	     end)
	  | trexp (A.WhileExp{test, body, pos}) =
	    (checkInt(trexp(test), pos);
	     Env.in_loop := !Env.in_loop + 1;
	     checkUnit(trexp body, pos);
	     Env.in_loop := !Env.in_loop - 1;
	     {exp=(), ty=Types.UNIT })
	  | trexp (A.ForExp{var, escape,
			    lo, hi, body, pos}) =
	    (checkInt(trexp(lo), pos);
	     checkInt(trexp(hi), pos);
	     let
		 val access = Tr.allocLocal level (!escape)
		 val venv' = S.enter(venv, var, Env.VarEntry{access=access,
							     ty=Ty.IMMUTABLE_INT})
	     in
		 Env.in_loop := !Env.in_loop + 1;
		 checkUnit((transExp(level, venv', tenv) body), pos);
		 Env.in_loop := !Env.in_loop - 1;
		 {exp=(), ty=Types.UNIT }
	     end)
	  | trexp (A.BreakExp pos) = (checkInLoop(pos);
				      {exp=(), ty=Types.BOTTOM})
	  | trexp (A.LetExp{decs, body,pos}) =
	    let val {venv=venv', tenv=tenv'} = transDecs(level, venv,tenv,decs)
	    in
		transExp(level, venv', tenv') body
	    end
	  | trexp (A.ArrayExp{typ, size, init, pos}) =
	    (case S.look(tenv, typ)
	      of SOME ty =>
		 (case actual_ty ty
		   of (Ty.ARRAY(ty, unique)) =>
		      (checkInt(trexp(size), pos);
		       if ((actual_ty ty) = (actual_ty (#ty (trexp(init))))) then ()
		       else (Error.error pos ("wrong initial value type of "
					      ^(stringTy (#ty (trexp(init))))));
		       {exp=(), ty=Ty.ARRAY(ty, unique) })
		    | _ => (Error.error pos ((S.name typ)^" is not array type");
			    {exp=(), ty=Ty.BOTTOM }))
	       | NONE => (Error.error pos "Array type not defined";
			  {exp=(), ty=Ty.BOTTOM }))
	and trvar (A.SimpleVar(id, pos)) =
	    (case S.look(venv, id)
	      of SOME (Env.VarEntry{access, ty}) => {exp=(), ty=actual_ty ty}
	       | _ => (Error.error pos ("undefined variable: " ^ S.name id);
		       {exp=(), ty=Types.BOTTOM}))
	  | trvar (A.FieldVar(var, id, pos)) =
	    let
		val {exp=varExp, ty=varTy} = trvar(var)
	    in
		(case actual_ty varTy
		  of Ty.RECORD (fields,unique) => {exp=(),
						   ty=getType(fields, id, pos)}
		   | _ => (Error.error pos
				       ("Attempt access field of a non-record "^
					(stringTy varTy));
			   {exp=(), ty=Ty.BOTTOM}))
	    end
	  | trvar (A.SubscriptVar(var, exp, pos)) =
	    let
		val {exp=varExp, ty=varTy} = trvar(var)
	    in
		(checkInt(trexp(exp),pos);
		 case actual_ty varTy
		  of Ty.ARRAY (ty, unique) => {exp=(), ty=ty}
		   | _ => (Error.error pos ("Attempt to index a non-array "^
					    stringTy varTy);
			   {exp=(), ty=Ty.BOTTOM}))
	    end
    in
	trexp
    end
    
fun transProg ast = 
    let 
	val level = Tr.newLevel{parent=Tr.outermost, 
				name=Temp.newlabel(), 
				formals=[]}
    in
	(FindEscape.findEscape(ast);
	 transExp(level,Env.base_venv, Env.base_tenv) ast;
	 ())
    end
end
