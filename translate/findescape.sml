structure FindEscape: sig val findEscape: Absyn.exp -> unit 
		      end =

struct
type depth = int
type escEnv = (depth * bool ref) Symbol.table
 
fun traverseExp(env, d) = 
    let
	fun travexp(Absyn.VarExp(var)) = travvar var
	  | travexp(Absyn.NilExp) = ()
	  | travexp(Absyn.IntExp _) = ()
	  | travexp(Absyn.StringExp(s, pos)) = ()
	  | travexp(Absyn.CallExp{func, args, pos}) = (map travexp args; ())
	  | travexp(Absyn.OpExp{left, oper, right, pos}) = (travexp left;
						   travexp right)
	  | travexp(Absyn.RecordExp{fields, typ, pos}) = 
	    (map (fn (symbol, expression, pos) => travexp expression) fields; ())
	  | travexp(Absyn.SeqExp exps) =
	    (map (fn (exp,pos) => travexp exp) exps; ())
	  | travexp(Absyn.AssignExp {var,exp,pos}) = travexp exp
	  | travexp(Absyn.IfExp {test, then', else', pos}) = 
	    (travexp test;
	     travexp then';
	     case else' 
	      of SOME exp => travexp exp
	       | NONE => ())
	  | travexp(Absyn.WhileExp {test, body, pos}) =
	    (travexp test;
	     travexp body)
	  | travexp(Absyn.ForExp {var, escape, lo, hi, body, pos}) = 
	    (escape := false;
	     travexp lo;
	     travexp hi;
	    let
		val env'=Symbol.enter(env, var, (d,escape))
	    in
		traverseExp(env',d) body
	    end)
	  | travexp(Absyn.BreakExp pos) = ()
	  | travexp(Absyn.LetExp{decs, body, pos}) = 
	    let
		val env' = traverseDecs(env, d) decs
	    in
		traverseExp(env', d) body
	    end
	  | travexp(Absyn.ArrayExp{typ, size, init, pos}) = (travexp size;
							travexp init)

	and travvar(Absyn.SimpleVar(id, pos)) = 
	    (case Symbol.look(env,id)
	      of SOME (depth, escape) => if (d>depth) then(escape := true) else () 
	       | NONE => () (* Undeclared variable checks occur in the typechecker*))
	  | travvar(Absyn.FieldVar(var, id, pos)) = travvar(var)
	  | travvar(Absyn.SubscriptVar(var, exp, pos)) = travvar(var)    
in
	travexp
end

and traverseDecs(env, d) =
    let
	fun travdecs(decs) = foldl travdec env decs
	and travdec(Absyn.FunctionDec(fundecs), env) = 
	    let
		fun travfun {name, params, result, body, pos} =
		    let
			val d' = d + 1
			fun enterparam ({name, escape, typ, pos}, env) =
			    (escape := false; 
			     Symbol.enter(env, name, (d', escape)))
		    	val env' = foldl enterparam env params
		    in 
			traverseExp(env', d') body
		    end 
	    in
		(map travfun fundecs; 
		 env)
	    end 
	  | travdec(Absyn.VarDec {name, escape, typ, init, pos}, env) =
	    (escape := false;
	     Symbol.enter(env, name, (d, escape)))
	  | travdec(Absyn.TypeDec(typedecs),env) = env
    in
	travdecs
    end
fun findEscape(prog) = traverseExp(Symbol.empty, 0) prog 

end
