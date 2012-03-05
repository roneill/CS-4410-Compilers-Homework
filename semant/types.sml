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

  (* The following define a partially ordered relation in our type system. These
   * relations partially implement a Lattice structure (meet is not implemented) *)
  
  fun join (NIL, RECORD a) = RECORD a 
    | join (RECORD a, NIL) = RECORD a
    | join (a, BOTTOM) = a
    | join (BOTTOM, a) = a
    | join (IMMUTABLE_INT, INT) = INT
    | join (INT, IMMUTABLE_INT) = INT
    | join (a,b) = if (a=b) then a else TOP
					
  fun lteq (a, b) = (join(a,b) = b)

end

