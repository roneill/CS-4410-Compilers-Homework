
# Team Members
Robert O'Neill
Allen Lee

# Overview
This project implements a primative IR generator with little
optimization. The few cases where we generate optimized IR are as follows. 

## If-Then-Else expressions
We match a special few cases and generate optizimed IR. The cases are:

* the then and else expressions are both statements
* one of or both the then and else expressions are conditionals

## unCx of a Ex (CONST k)

This returns a control jump to either the true or the false labels
depending on whether k is 0. 

## Optimizations left Todo

We introduced a NOP instruction for the translation of the unit
expression, translating if-then, and type checking errors. These will
need to be removed at a later stage in the compiler, prior to
instruction selection.  Simple optimizations like constant folding can
also be done at that time.  