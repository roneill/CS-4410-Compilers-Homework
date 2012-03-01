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
	  | BOTTOM
	  | TOP 

  (* The following relations define a partially ordered latice on our type system *)
  fun glb (RECORD _, NIL) = NIL
    | glb (NIL, RECORD _) = NIL
    | glb (r1 as RECORD(r,u) , r2 as RECORD (r',u')) = if (u=u') then r1 else NIL
    | glb (TOP, a) = a
    | glb (a, TOP) = a
    | glb (a, b) = if (a=b) then a else BOTTOM
					
  fun lub (a, b) = if (a=b) then a else TOP

  fun lessthan (a, b) = (glb(a,b) = a)
		      
  fun compatible (a, b)  = lessthan(b, a) orelse lessthan(a, b)

end

