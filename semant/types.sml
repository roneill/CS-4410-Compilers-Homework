structure Types =
struct

  type unique = unit ref

  datatype ty = 
            RECORD of (Symbol.symbol * ty) list * unique
          | NIL
          | INT
	  | IMMUTABLE_INT (* used for the counter of a for loop *)
          | STRING
          | ARRAY of ty * unique
	  | NAME of Symbol.symbol * ty option ref
	  | UNIT
	  | BOTTOM
	  | TOP 

  (* The following relations define a partially ordered relation in our type system *)
  fun lteq (NIL, RECORD _) = true
    | lteq (TOP, TOP) = true
    | lteq (BOTTOM, _) = true
    | lteq (IMMUTABLE_INT, INT) = true
    | lteq (RECORD(r,u),RECORD (r',u')) = (u=u') 
    | lteq (ARRAY(ty,u),ARRAY (ty',u')) = (u=u') 
    | lteq (a, b) = (a=b)
  		      
  fun compatible (a, b)  = lteq(b, a) orelse lteq(a, b)

end

