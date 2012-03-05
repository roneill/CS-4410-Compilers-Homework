
# Team Members
Robert O'Neill
Allen Lee

## Partially ordered relations between types

   Sometimes we need to check if types are compatible. We do this
   using a partial order relation between our types (similar to a
   lattice but missing the meet relation). For any two types
   , (a,b), the "lteq" function returns true if (a<=b).  When the <=
   relation between a and b hold, we can use type a when we expect
   type b.  This is useful for cases such as:

   	- typechecking BREAK statements
	- assignments to NIL for record types
	- determining the return type of an if then else where one
	  arguments are BREAK or NIL

   

## Cycles in mutually recursive types

   We check for cycles in mutually recursive types by viewing type
   assignments as a directed graph. Each node should have an edge to
   only one other node in the graph. If a node points back to itself,
   there is a cycle. We detect cycles in the graph by marking each
   node we visit when we traverse the graph. If we come across a node
   that is already marked, we know that there is a cycle in
   the graph.

## Checking for break inside inside of for and while

   We added a state variable to our ENV module, in_loop.  This 
   variable is 0 when not in a FOR or WHILE loop, and greater
   than 0 when inside a loop.  Its value represents the number of 
   nested loops of the current state. 