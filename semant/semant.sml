structure A = Absyn
structure S = Symbol
structure Ty = Types

signature ENV =
sig
   (* Don't know why we need this yet
    type access *) 
    type ty
    type enventry

    val base_tenv: ty S.table
    val base_venv: enventry S.table
end

structure Env :> ENV =
struct
  
  type ty = Ty.ty
  datatype enventry = ValEntry of {ty: ty}
		      | FunEntry of {formals: ty list, result: ty}
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

structure Semant =
struct 
    type venv = Env.enventry S.table
    type tenv = ty S.table
end
