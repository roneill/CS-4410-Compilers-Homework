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

fun checkInt ({exp, ty}, pos) =
    if ty = Types.INT then ()
    else Error.error(pos) "exp was not an int"

fun checkUnit ({exp, ty}, pos) =
    if ty = Types.UNIT then ()
    else Error.error(pos) "exp was not a unit"

fun actual_ty typ =
    case typ of
	(Ty.NAME (id, ref(SOME(typ')))) => actual_ty typ'
      | anyTy => anyTy;
    (*TODO: Is it ok for a variable to have UNIT type?*)

fun getType (nil, id, pos) = (Error.error(pos) "field not found in record"; Ty.INT)
  | getType ((name,ty)::tail, id, pos) = if (id = name) then ty else getType(tail, id, pos) 
    
    (*just copied from w*)
fun transDec (venv, tenv, A.VarDec{name, escape, typ=NONE, init, pos}) = (*TODO: VarDec with types*)
    let val {exp, ty} = transExp(venv, tenv) init
    in
	{tenv=tenv, venv=S.enter(venv, name, Env.VarEntry{ty=ty})}
    end
  | transDec (venv, tenv, A.TypeDec[{name, ty,pos}]) =
    {venv=venv, tenv=S.enter(tenv, name, transTy(tenv,ty))}
  | transDec(venv, tenv, A.FunctionDec[{name,params,body,pos,result=SOME(rt, rpos)}]) =
    (* TODO: lists of functions, recursive functions, functions with no result, undeclared identifiers(etc),type check body*)
    let val SOME(result_ty) = S.look(tenv, rt)
	fun transparam{name, escape, typ, pos} =
	    case S.look(tenv, typ)
	     of SOME t => {name=name, ty=t}
	val params' = map transparam params
	val venv' = S.enter(venv, name,
				      Env.FunEntry{formals= map #ty params', result=result_ty})
	fun enterparam ({name, ty}, venv) =
	    S.enter(venv, name, Env.VarEntry{ty=ty})
	val venv'' =  foldl enterparam venv' params'
    in
	transExp(venv'', tenv) body;
	{venv=venv', tenv=tenv}
    end

and transDecs (venv, tenv, decs) =
   (* | transDecs(venv, tenv, nil) = ()
    | transDecs(venv,tenv, dec::tail) =
      let
	  val {venv=venv', tenv=tenv'} = transDec(venv, tenv, dec)
      in
	  transDecs(venv', tenv', tail)*)
    let
	fun transDec' (dec, {venv,tenv}) =
	    transDec (venv,tenv,dec)
    in
	foldl transDec' {venv=venv,tenv=tenv} decs
    end
and transTy (tenv, A.NameTy(symbol,pos)) =
    (case S.look(tenv,symbol)
     of SOME ty => ty
      | NONE => (Error.error pos "type TODO not defined"; Ty.INT) (*TODO*))
  | transTy (tenv, A.RecordTy(fields)) =
    let
	val flds = map (fn x => (#name x, transTy(tenv, A.NameTy(#typ x, #pos x)))) fields 
	val uniq = ref ()
    in
	Ty.RECORD(flds, uniq)
    end
  | transTy (tenv, A.ArrayTy(symbol,pos)) =
    (case S.look(tenv,symbol)
     of SOME (Ty.ARRAY (ty,unique)) => (Ty.ARRAY (ty,unique))
      | SOME _ => (Error.impossible "Array type is not an Array in tenv") 
      | NONE => (Error.error pos "type TODO not defined"; Ty.INT) (*TODO*))
    
and transExp (venv, tenv) =
    let fun trexp (A.VarExp var) = trvar var
	  | trexp (A.NilExp) = {exp=(), ty=Types.NIL}			       
	  | trexp (A.IntExp i) = {exp=(), ty=Types.INT}
	  | trexp (A.StringExp(s, pos)) = {exp=(), ty=Types.STRING}
	  | trexp (A.CallExp{func, args, pos}) =
	    (case S.look(venv, func)
	      of SOME (Env.FunEntry{formals, result}) =>
		 (let fun checkFormals (nil, nil) = ()
			| checkFormals (nil, _) =
			  (Error.error pos "Function has more arguments than declaration")
			| checkFormals (_, nil) =
			  (Error.error pos "Function has less arguments than declaration")
			| checkFormals (formal::t1, arg::t2) =
			  (if (formal = #ty (trexp arg))
			   then ()
			   else checkFormals (t1, t2))
		  in
		      checkFormals (formals, args)
		  end;
		  {exp=(), ty=result})
	       | NONE => (Error.error pos "function name not declared"; {exp=(), ty=Ty.UNIT}))
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
	    (checkInt(trexp left, pos);
	     checkInt(trexp right, pos);
	     {exp=(), ty=Types.INT})
	  | trexp (A.OpExp{left, oper=A.NeqOp, right, pos}) =
	    (checkInt(trexp left, pos);
	     checkInt(trexp right, pos);
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
	      of SOME (Ty.RECORD(recFields, unique)) =>
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
	       | NONE => (Error.error pos "record type not declared";{exp=(), ty=Ty.UNIT}))
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
		if(varType = expType) then ()
		else (Error.error pos "cannot assign variable to this type");
		{exp=(), ty=Types.UNIT}
	    end
	  | trexp (A.IfExp {test, then', else'=NONE, pos}) =
	    (checkInt (trexp(test), pos);
	     checkUnit (trexp(then'),pos);
	     {exp=(), ty=Types.UNIT })
	  | trexp (A.IfExp {test, then', else'=SOME elseBody, pos}) =
	    (checkInt (trexp(test), pos);
	     let
		 val {exp=thenExp, ty=thenTy} = trexp(then');
		 val {exp=elseExp, ty=elseTy} = trexp(elseBody);
	     in
		 if (thenTy = elseTy) then ()
		 else Error.error pos "the types of the then clause and else clause do not match";
		 {exp=(), ty=thenTy }
		 
	     end)
	  | trexp (A.WhileExp{test, body, pos}) =
	    (checkInt(trexp(test), pos);
	     checkUnit(trexp(body), pos);
	     {exp=(), ty=Types.UNIT })
	  | trexp (A.ForExp{var, escape,
			    lo, hi, body, pos}) =
	    (checkInt(trexp(lo), pos);
	     checkInt(trexp(hi), pos);
	     let
		 val venv'=S.enter(venv, var, Env.VarEntry{ty=Ty.INT})
	     in
		 (checkUnit((transExp(venv', tenv) body), pos);
		  {exp=(), ty=Types.UNIT })
	     end)
	  | trexp (A.BreakExp pos) = {exp=(), ty=Types.UNIT }
	  | trexp (A.LetExp{decs, body,pos}) =
	    let val {venv=venv', tenv=tenv'} = transDecs(venv,tenv,decs)
	    in
		transExp(venv', tenv') body
	    end
	  | trexp (A.ArrayExp{typ, size, init, pos}) =
	    (case S.look(tenv, typ)
	      of SOME (Ty.ARRAY(ty, unique)) =>
		 (checkInt(trexp(size), pos);
		  if (ty = (#ty (trexp(init))))
		  then ()
		  else (Error.error pos "wrong initial value type");
		  {exp=(), ty=ty })
	       | NONE => (Error.error pos "Array type not defined";
			  {exp=(), ty=Ty.UNIT }))
	    
	and trvar (A.SimpleVar(id, pos)) =
	    (case S.look(venv, id)
	      of SOME (Env.VarEntry{ty}) => {exp=(), ty=actual_ty ty}
	       | NONE => (Error.error pos ("undefined variable " ^ S.name id);
			  {exp=(), ty=Types.INT}))
	  | trvar (A.FieldVar(var, id, pos)) =
	    let
		val {exp=varExp, ty=varTy} = trvar(var)
	    in
		(case varTy
		  of Ty.RECORD (fields,unique) => {exp=(), ty=getType(fields, id, pos)}
		   | _ => (Error.error pos "Attempt access field of a non-record"; {exp=(), ty=Ty.INT}))
	    end
	  | trvar (A.SubscriptVar(var, exp, pos)) =
	    let
		val {exp=varExp, ty=varTy} = trvar(var)
	    in
		(checkInt(trexp(exp),pos);
		 case varTy
		  of Ty.ARRAY (ty, unique) => {exp=(), ty=ty}
		   | _ => (Error.error pos "Attempt index a non-array"; {exp=(), ty=Ty.INT}))
	    end

(* We have to ensure that var in fieldvar *)
	     
    in
	trexp
    end
    
fun transProg ast = ((transExp(Env.base_venv, Env.base_tenv) ast); ())
    
end
