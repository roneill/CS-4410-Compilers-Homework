structure A = Absyn
structure S = Symbol
structure Ty = Types
structure Error = ErrorMsg	       

signature ENV =
sig
   (* Don't know why we need this yet
    type access  
    type ty *)

    datatype enventry = VarEntry of {ty: Ty.ty}
		      | FunEntry of {formals: Ty.ty list, result: Ty.ty}
    val base_tenv: Ty.ty S.table
    val base_venv: enventry S.table
end

structure Env :> ENV =
struct

  datatype enventry = VarEntry of {ty: Ty.ty}
		      | FunEntry of {formals: Ty.ty list, result: Ty.ty}
       
  val base_tenv = foldr S.enter' S.empty [ (S.symbol("int"), Ty.INT),
					   (S.symbol("string"), Ty.STRING) ]

  val base_venv = foldr S.enter' S.empty 
		  [ (S.symbol("print"), FunEntry {formals=[Ty.STRING], result=Ty.UNIT }),
		    (S.symbol("flush"), FunEntry {formals=[], result=Ty.UNIT}),
		    (S.symbol("getchar"), FunEntry {formals=[], result=Ty.STRING}),
		    (S.symbol("ord"), FunEntry {formals=[Ty.STRING], result=Ty.INT}),
		    (S.symbol("chr"), FunEntry {formals=[Ty.INT], result=Ty.STRING}),
		    (S.symbol("size"), FunEntry {formals=[Ty.STRING], result=Ty.INT}),
		    (S.symbol("substring"), FunEntry {formals=[Ty.STRING, Ty.INT, Ty.INT], result=Ty.STRING}),
		    (S.symbol("concat"), FunEntry {formals=[Ty.STRING, Ty.STRING], result=Ty.STRING}),
		    (S.symbol("not"), FunEntry {formals=[Ty.INT], result=Ty.INT}),
		    (S.symbol("exit"), FunEntry {formals=[Ty.INT], result=Ty.UNIT}) ]
end

structure Translate = struct
type exp = unit
end

structure Semant :sig val transProg : A.exp -> unit end =
struct 
    
type venv = Env.enventry Symbol.table
type tenv = Ty.ty Symbol.table
type expty = {exp:Translate.exp, ty: Ty.ty}

(*dummy symbol inserted into the tenv upon entering a loop, used for checking break statements.
  Tiger does not allow identifiers starting with underscores so this will not cause conflicts 
  with user defined types.*)
val in_loop = S.symbol("__in_loop")

fun checkInLoop (tenv, pos) =
    case S.look(tenv, in_loop) 
      of SOME _ => ()
       | NONE => (Error.error pos "break encountered outside of loop")

fun checkInt ({exp, ty}, pos) =
    if Ty.lteq(ty, Types.INT) then ()
    else Error.error(pos) "exp was not an int"

fun checkUnit ({exp, ty}, pos) =
    if Ty.lteq(ty, Types.UNIT) then ()
    else Error.error(pos) "exp was not a unit"
	 
fun checkCompatible ({exp=lexp, ty=lty},{exp=rexp, ty=rty}, pos) =
    if Ty.compatible(lty, rty) then ()
    else Error.error(pos) "types are not compatible"

(*TODO use this in Ty.compatible???*)
fun actual_ty typ =
    case typ of
	(Ty.NAME (id, ref(SOME(typ')))) => actual_ty typ'
      | anyTy => anyTy;
    (*TODO: Is it ok for a variable to have UNIT type?*)

fun getType (nil, id, pos) = (Error.error(pos) "field not found in record"; Ty.INT)
  | getType ((name,ty)::tail, id, pos) = if (id = name) then ty else getType(tail, id, pos)								     

fun checkDuplicateDeclarations (names) = 
    let
	fun checkDuplicates(nil, checkedNames) = ()
	  | checkDuplicates(((name, pos)::tail), checkedNames) =
	    case S.look(checkedNames, name)
	     of SOME dName => (Error.error pos "duplicate declaration found" )
	      | NONE => checkDuplicates(tail, S.enter(checkedNames, name, ref ()))
    in
	checkDuplicates(names, S.empty)
    end	
								     
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

fun transDec (venv, tenv, A.VarDec{name, escape, typ=NONE, init, pos}) = 
    let val {exp, ty} = transExp(venv, tenv) init
    in
	if (ty = Ty.NIL) then (Error.error pos "Cannot assign expression to nil")
	else ();
	{tenv=tenv, venv=S.enter(venv, name, Env.VarEntry{ty=ty})}
    end
  | transDec (venv, tenv, A.VarDec{name, escape, typ=SOME typ , init, pos}) =
    let
	val varTy = transTy(tenv, A.NameTy(typ))
	val {exp, ty} = transExp(venv, tenv) init
    in
	if (Ty.lteq ((actual_ty ty),(actual_ty varTy))) then ()
	else Error.error pos ("var type " ^ (stringTy varTy)  ^ " and initializer " ^ (stringTy ty)  ^ " type do not match");
	{tenv=tenv, venv=S.enter(venv, name, Env.VarEntry{ty=ty})}
    end
  | transDec (venv, tenv, A.TypeDec(typedecs)) =
    let
	fun enterTypeHeader ({name, ty, pos}, tenv) = S.enter(tenv, name, Ty.NAME(name,ref NONE))
	val tenv' = foldl enterTypeHeader tenv typedecs
	fun checkTypeBody ({name, ty, pos}) =
	    case S.look(tenv', name)
	     of SOME (Ty.NAME (name, body)) => body := SOME (transTy(tenv', ty))
	      | _ => Error.impossible "Looking up type header failed"
	fun checkForCycles tenv {name, ty, pos} =
	    let 
		fun checkForCycles' (ty, visited) =
		    case ty
		     of (Ty.NAME (name, body)) =>
			(case S.look (visited, name)
			  of SOME _ => Error.error pos ("cycle detected")
			   | NONE => checkForCycles'(getOpt(!body,Ty.INT), S.enter(visited, name, ref ())))
		      | _ => ()
			     
	    in
		case S.look (tenv, name)
		 of SOME ty => checkForCycles' (ty,S.empty)
		  | NONE => Error.impossible "Cyclic type checking error"
	    end
    in
	map checkTypeBody typedecs;
	map (checkForCycles tenv') typedecs;
	checkDuplicateDeclarations(map (fn x => (#name x, #pos x)) typedecs);
	{venv=venv, tenv=tenv'}
    end
  (* TODO: lists of functions, recursive functions, what is etc?*)
  | transDec(venv, tenv, A.FunctionDec(fundecs)) =
    let
	fun getResultTy (result) = case result
				    of SOME(rt, pos) =>
				       (case S.look(tenv, rt)
					 of SOME ty => ty
					  | NONE => (Error.error pos "return type undeclared"; Ty.INT))
				     | NONE => Ty.UNIT
	fun transparam {name, escape, typ, pos} =
	    case S.look(tenv, typ)
	     of SOME t => {name=name, ty=t}
	      | NONE => (Error.error pos ("parameter type "^(S.name typ)^" undeclared"); {name=name, ty=Ty.INT})
	fun enterFunHeader ({name,params,body,pos,result}, venv) =
	    let val result_ty = getResultTy result
		val params' = map transparam params
	    in
		S.enter(venv, name, Env.FunEntry{formals= map #ty params', result=result_ty})
	    end
	val venv' = foldl enterFunHeader venv fundecs
	fun checkFunBody ({name,params,body,pos,result}) =
	    let
		val result_ty = getResultTy result
		fun enterparam ({name, ty}, venv) =
		    S.enter(venv, name, Env.VarEntry{ty=ty})
		val params' = map transparam params
		val venv'' =  foldl enterparam venv' params'
		val {exp=bodyexp, ty=bodyty} = transExp(venv'', tenv) body
	    in
		if (actual_ty bodyty = actual_ty result_ty) then ()
		else (Error.error pos ((stringTy bodyty)^"Return type of body does not match declaration"))
	    end
    in
	map checkFunBody fundecs;
	checkDuplicateDeclarations(map (fn x => (#name x, #pos x)) fundecs);
	{venv=venv', tenv=tenv}
    end

and transDecs (venv, tenv, decs) =
    let
	fun transDec' (dec, {venv,tenv}) =
	    transDec (venv,tenv,dec)
    in
	foldl transDec' {venv=venv,tenv=tenv} decs
    end
and transTy (tenv, A.NameTy(symbol,pos)) =
    (case S.look(tenv,symbol)
     of SOME ty =>  ty
      | NONE => (Error.error pos ("type "^(S.name symbol)^" not defined"); Ty.INT) (*TODO*))
  | transTy (tenv, A.RecordTy(fields)) =
    let
	val flds = map (fn x => (#name x, transTy(tenv, A.NameTy(#typ x, #pos x)))) fields 
	val uniq = ref ()
    in
	Ty.RECORD(flds, uniq)
    end
  | transTy (tenv, A.ArrayTy(symbol,pos)) =
    (case S.look(tenv,symbol)
     of SOME ty => Ty.ARRAY(ty, ref ())
      | NONE => (Error.error pos "type not defined"; Ty.INT) (*TODO*))
    
and transExp (venv, tenv) =
    let fun trexp (A.VarExp var) = trvar var
	  | trexp (A.NilExp) = {exp=(), ty=Types.NIL}			       
	  | trexp (A.IntExp i) = {exp=(), ty=Types.INT}
	  | trexp (A.StringExp(s, pos)) = {exp=(), ty=Types.STRING}
	  | trexp (A.CallExp{func, args, pos}) =
	    (case S.look(venv, func)
	      of SOME (Env.FunEntry{formals, result}) =>
		 (*TODO: use high order functions*)
		 (let fun checkFormals (nil, nil) = ()
			| checkFormals (formal::t1, arg::t2) =
			  (if ((actual_ty formal) = (actual_ty (#ty (trexp arg))))
			   then checkFormals (t1, t2)
			   else (Error.error pos ((stringTy formal)^" wrong argument type "^(stringTy (#ty (trexp arg))))))
		  in
		      if (length(formals) = length(args)) then
			  checkFormals (formals, args)
		      else
			  (Error.error pos "Wrong number of arguments")
		  end;
		  {exp=(), ty=result})
	       | NONE => (Error.error pos "function name not declared"; {exp=(), ty=Ty.UNIT})
	    | _ => {exp=(), ty=Ty.UNIT}) (* get rid of *)
	  (* Consider using a case statement*)
	  | trexp (A.OpExp{left, oper=A.PlusOp, right, pos}) =
	    (checkInt(trexp left, pos);
	     checkInt(trexp right, pos);
	     {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.MinusOp, right, pos}) =
	    (checkInt(trexp left, pos);
	     checkInt(trexp right, pos);
	     {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.TimesOp, right, pos}) =
	    (checkInt(trexp left, pos);
	     checkInt(trexp right, pos);
	     {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.DivideOp, right, pos}) =
	    (checkInt(trexp left, pos);
	     checkInt(trexp right, pos);
	     {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.EqOp, right, pos}) =
	    (checkCompatible(trexp left, trexp right, pos);
	    {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.NeqOp, right, pos}) =
	    (checkCompatible(trexp left, trexp right, pos);
	    {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.LtOp, right, pos}) =
	    (checkInt(trexp left, pos);
	     checkInt(trexp right, pos);
	     {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.LeOp, right, pos}) =
	    (checkInt(trexp left, pos);
	     checkInt(trexp right, pos);
	     {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.GtOp, right, pos}) =
	    (checkInt(trexp left, pos);
	     checkInt(trexp right, pos);
	     {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.GeOp, right, pos}) =
	    (checkInt(trexp left, pos);
	     checkInt(trexp right, pos);
	     {exp=(), ty=Types.INT})
	  | trexp (A.RecordExp{fields, typ, pos}) =
	    (case S.look(tenv, typ)
	      of SOME ty =>
		 (case actual_ty ty
		  of (Ty.RECORD(recFields, unique)) =>
		     (* make this better *)
		     (let fun lookupID (id, nil) = (Error.error pos "Element not found"; NONE)
			    | lookupID (id, ((recID, ty)::tail)) = if (id = recID) then SOME ty
								   else lookupID(id, tail)
			  and loopFields nil = ()
			    | loopFields ((symbol, exp, pos)::tail) =
			      case lookupID(symbol, recFields)
			       of SOME ty => if (ty = #ty(trexp exp)) then ()
					     else loopFields(tail)
				| NONE => (Error.error pos "Record field not declared")
		      in
			  loopFields(fields)
		      end;
		      {exp=(), ty=(Ty.RECORD(recFields, unique))})
		     | _ => (Error.error pos "identifier was not a record"; {exp=(), ty=Ty.INT}))
	       | NONE => (Error.error pos "record type not declared"; {exp=(), ty=Ty.INT}))
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
		(* this may not be right *)
		if(Ty.lteq(expType,varType)) then ()
		else (Error.error pos "cannot assign variable to this type");
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
		 if (Ty.compatible(thenTy, elseTy)) then ()
		 else Error.error pos "the types of the then clause and else clause do not match";
		 {exp=(), ty=thenTy }
		 
	     end)
	  | trexp (A.WhileExp{test, body, pos}) =
	    let
		val tenv'=S.enter(tenv, in_loop, Ty.TOP)
	    in 
		checkInt(trexp(test), pos);
		checkUnit(transExp(venv,tenv') body, pos);
		{exp=(), ty=Types.UNIT }
	    end
	  | trexp (A.ForExp{var, escape,
			    lo, hi, body, pos}) =
	    (checkInt(trexp(lo), pos);
	     checkInt(trexp(hi), pos);
	     let
		 val tenv'=S.enter(tenv, in_loop, Ty.TOP)
		 val venv'=S.enter(venv, var, Env.VarEntry{ty=Ty.IMMUTABLE_INT})
	     in
		 (checkUnit((transExp(venv', tenv') body), pos);
		  {exp=(), ty=Types.UNIT })
	     end)
	  | trexp (A.BreakExp pos) = (checkInLoop(tenv,pos);
				      {exp=(), ty=Types.BOTTOM})
	  | trexp (A.LetExp{decs, body,pos}) =
	    let val {venv=venv', tenv=tenv'} = transDecs(venv,tenv,decs)
	    in
		transExp(venv', tenv') body
	    end
	    (* rewrite *)
	  | trexp (A.ArrayExp{typ, size, init, pos}) =
	    (case S.look(tenv, typ)
	      of SOME ty =>
		 (case actual_ty ty
		  of (Ty.ARRAY(ty, unique)) =>
		     (checkInt(trexp(size), pos);
		      if ((actual_ty ty) = (actual_ty (#ty (trexp(init)))))
		      then ()
		      else (Error.error pos ("wrong initial value type of "^(stringTy (#ty (trexp(init))))));
		      {exp=(), ty=Ty.ARRAY(ty, unique) })
		   | _ => (Error.error pos ((S.name typ)^" is not array type");
			   {exp=(), ty=Ty.INT }))
	       | NONE => (Error.error pos "Array type not defined";
			  {exp=(), ty=Ty.INT }))
	    
	and trvar (A.SimpleVar(id, pos)) =
	    (case S.look(venv, id)
	      of SOME (Env.VarEntry{ty}) => {exp=(), ty=actual_ty ty}
	       | NONE => (Error.error pos ("undefined variable " ^ S.name id);
			  {exp=(), ty=Types.INT})
	       | _ => {exp=(), ty=Types.INT}) (* for testing purposes*)
	  | trvar (A.FieldVar(var, id, pos)) =
	    let
		val {exp=varExp, ty=varTy} = trvar(var)
	    in
		(case actual_ty varTy
		  of Ty.RECORD (fields,unique) => {exp=(), ty=getType(fields, id, pos)}
		   | _ => (Error.error pos ("Attempt access field of a non-record " ^ stringTy varTy); {exp=(), ty=Ty.INT}))
	    end
	  | trvar (A.SubscriptVar(var, exp, pos)) =
	    let
		val {exp=varExp, ty=varTy} = trvar(var)
	    in
		(checkInt(trexp(exp),pos);
		 case actual_ty varTy
		  of Ty.ARRAY (ty, unique) => {exp=(), ty=ty}
		   | _ => (Error.error pos ("Attempt index a non-array " ^ stringTy varTy); {exp=(), ty=Ty.INT}))
	    end

(* We have to ensure that var in fieldvar *)
	     
    in
	trexp
    end
    
fun transProg ast = ((transExp(Env.base_venv, Env.base_tenv) ast); ())
    
end
