structure Types =
struct

  type unique = unit ref

  datatype ty = 
            RECORD of (Symbol.symbol * ty) list * unique
          | NIL
          | INT
          | STRING
          | ARRAY of ty * unique
	  | NAME of Symbol.symbol * ty option ref
	  | UNIT

  fun lub (RECORD _, NIL) = NIL
    | lub (NIL, RECORD _) = NIL
    | lub (RECORD(r,u) as r1 , RECORD (r',u') as r2) = if (u=u') then r1 else NIL
    | 
end

