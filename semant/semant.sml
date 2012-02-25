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
	 
fun transExp (venv, tenv) =
    let fun trexp (A.OpExp{left, oper=A.PlusOp, right, pos}) =
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
	    | trexp (A.IntExp i) = {exp=(), ty=Types.INT}
	    | trexp (A.StringExp(s, pos)) = {exp=(), ty=Types.STRING}
	    | trexp (A.NilExp) = {exp=(), ty=Types.NIL}
	    | trexp (A.BreakExp pos) = {exp=(), ty=Types.UNIT }
	    | trexp (A.WhileExp{test, body, pos}) =
	      (checkInt(trexp(test), pos);
	       checkUnit(trexp(body), pos);
	       {exp=(), ty=Types.UNIT })
	    | trexp (A.ForExp{var, escape,
			      lo, hi, body, pos}) =
	      (checkInt(trexp(lo), pos);
	       checkInt(trexp(hi), pos);
	       (*val exptyBody = let
		     val venv'=S.enter(venv, var, VarEntry Ty.INT)
		 in
		     transExp(venv',tenv) body
		 end;
		     checkUnit(exptyBody, pos);*)
	       {exp=(), ty=Types.UNIT })
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
	    | trexp (A.SeqExp(exps)) =
	      let fun checkExps nil = {exp=(), ty=Types.UNIT }
		    | checkExps ((exp, pos)::nil) = trexp(exp)
		    | checkExps ((exp, pos)::tail) = (trexp(exp); checkExps(tail))
	      in
		  checkExps(exps)
	      end
	      
	and trvar (A.SimpleVar(id, pos)) =
	    (case S.look(venv, id)
	      of SOME (Env.VarEntry{ty}) => {exp=(), ty=actual_ty ty}
	       | NONE => (Error.error pos ("undefined variable " ^ S.name id);
			  {exp=(), ty=Types.INT}))
	  (*| trvar (A.FieldVar(v, id, pos)) =
	    (case S.look(venv, v)*)
	      
    in
	trexp
    end

	   (* | trexp (A.RecordExp{fields, tid,  pos}) =
	      let
		  fun checkFields [] = ()
		    | checkFields fields : (symbol * exp * pos) list =
		      let head = hd(fields)
		      in
			  	      
	      (checkType(tid);
	       checkFields(fields);
	       {exp=(), ty=Types.RECORD S.symbol}) *)

fun transProg ast = ((transExp(Env.base_venv, Env.base_tenv) ast); ())
    
end
