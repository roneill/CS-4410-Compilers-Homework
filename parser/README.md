
# Team Members
Robert O'Neill
Allen Lee

## Shift/reduce conflict resolution

We chose to resolve conflicts by letting ml-yacc shift by default.

1.) The arithmetic and logical operators caused shift/reduce conflicts
    in the following productions:
    - cond_exp 
    - while_exp 
    - for_exp
    - assign_exp
    - array_exp
 
    The parser shifts by default in these situations, which is the
    desired behavior. In this way the expression fully evaluated.

2.) The dangling else resulted in a shift/reduce conflict.
  
    We want to shift in this case so that ELSE binds with the most
    recent IF.

3.) There was a shift/reduce conflict between lvalue and array_exp.

    We originally wrote the lvalue production rules as:

    lvalue_exp: ID                             
	      | lvalue_exp DOT ID            
	      | lvalue_exp LBRACK exp RBRACK 

    We resolved the conflict by adding the production rule:

    ID LBRACK exp RBRACK

4.) In type_decs and fun_decs there are shift/reduce conflicts between:

    type_decs: type_dec                      
	     | type_dec type_decs            

    fun_decs: fun_dec                        
	    | fun_dec fun_decs

    We always want to shift in order to cons consecutive type and function declarations.	    

    
