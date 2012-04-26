(* make this an abstraction sometime *)
structure Temp : TEMP =
struct
    type temp = int
    val temps = ref 100
    fun newtemp() = let val t = !temps in temps := t+1; t end

    structure Table = IntMapTable(type key = int
				  fun getInt n = n)

    fun makestring t = "t" ^ Int.toString t

    fun toString l = Symbol.name l

    fun compareLabels (l1, l2) =
	let
	    val s1 = toString(l1)
	    val s2 = toString(l2)
	in
	    String.compare(s1, s2)
	end
	
    fun tempint t = t

    fun compareTemps (t1,t2) =
	Int.compare(tempint t1,
		    tempint t2)

		       
  type label = Symbol.symbol

local structure F = Format
      fun postinc x = let val i = !x in x := i+1; i end
      val labs = ref 0
 in
    fun newlabel() = Symbol.symbol(F.format "L%d" [F.INT(postinc labs)])
    fun namedlabel name = Symbol.symbol ("tig_"^name);
end


end
