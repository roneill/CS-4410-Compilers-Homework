
structure FindEscape: sig val findEscape: Absyn.exp -> unit 
		      end =

struct
type depth = int
type escEnv = (depth * bool ref) Symbol.table
 
fun traverseExp(env, d) = 
    let
	fun travexp(A.VarExp(var)) = travvar var
	  | travexp(A.NilExp) = ()
	  | travexp(A.IntExp _) = ()
	  | travexp(A.StringExp(s, pos)) = ()
	  | travexp(A.CallExp{func, args, pos}) = (map travexp args; ())
	  | travexp(A.OpExp{left, oper, right, pos}) = (travexp left;
						   travexp right)
	  | travexp(A.RecordExp{fields, typ, pos}) = 
	    (map (fn (symbol, expression, pos) => travexp expression) fields; ())
	  | travexp(A.SeqExp exps) =
	    (map (fn (exp,pos) => travexp exp) exps; ())
	  | travexp(A.AssignExp {var,exp,pos}) = travexp exp
	  | travexp(A.IfExp {test, then', else', pos}) = 
	    (travexp test;
	     travexp then';
	     case else' 
	      of SOME exp => travexp exp
	       | NONE => ())
	  | travexp(A.WhileExp {test, body, pos}) =
	    (travexp test;
	     travexp body)
	  | travexp(A.ForExp {var, escape, lo, hi, body, pos}) = 
	    (escape := false;
	     travexp lo;
	     travexp hi;
	    let
		val env'=S.enter(env, var, (d,escape))
	    in
		traverseExp(env',d) body
	    end)
	  | travexp(A.BreakExp pos) = ()
	  | travexp(A.LetExp{decs, body, pos}) = 
	    let
		val env' = traverseDecs(env, d) decs
	    in
		traverseExp(env', d) body
	    end
	  | travexp(A.ArrayExp{typ, size, init, pos}) = (travexp size;
							travexp init)

	and travvar(A.SimpleVar(id, pos)) = 
	    (case S.look(env,id)
	      of SOME (depth, escape) => if (d>depth) then escape := true else () 
	       | NONE => () (* Undeclared variable checks occur in the typechecker*))
	  | travvar(A.FieldVar(var, id, pos)) = travvar(var)
	  | travvar(A.SubscriptVar(var, exp, pos)) = travvar(var)    
in
	travexp
end

and traverseDecs(env, d) =
    let
	fun travdecs(decs) = foldl travdec env decs
	and travdec(A.FunctionDec(fundecs), env) = 
	    let
		fun travfun {name, params, result, body, pos} =
		    let
			val d' = d + 1
			fun enterparam ({name, escape, typ, pos}, env) =
			    (escape := false; 
			     S.enter(env, name, (d', escape)))
		    	val env' = foldl enterparam env params
		    in 
			traverseExp(env', d') body
		    end 
	    in
		(map travfun fundecs; 
		 env)
	    end 
	  | travdec(A.VarDec {name, escape, typ, init, pos}, env) =
	    (escape := false;
	     S.enter(env, name, (d, escape)))
	  | travdec(A.TypeDec(typedecs),env) = env
    in
	travdecs
    end
fun findEscape(prog) = traverseExp(S.empty, 0) prog 

end
