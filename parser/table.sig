signature TABLE = 
sig
   type key
   type 'a table
   val empty : 'a table
   val enter : 'a table * key * 'a -> 'a table
   val enter' : (key * 'a) * 'a table -> 'a table
   val look  : 'a table * key -> 'a option
   val remove : ('a table * key) -> 'a table
end

