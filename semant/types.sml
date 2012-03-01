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
    | glb (RECORD(r,u) as r1 , RECORD (r',u') as r2) = if (u=u') then r1 else NIL
    | glb (TOP, a) = a
    | glb (a, TOP) = a
    | glb (a, b) = if (a=b) then a else BOTTOM
					
  fun lub (a, b) = if (a=b) then a else TOP

  fun (a:ty < b:ty) = (glb(a,b) = a)
		      
  fun compatible a b  = (b<a)
end

