# Lexer README

## Team Members
Robert O'Neill
Allen Lee

## Handling Comments
Our lexer employs lex states and a stack to handle nested Tiger
comments. Our lexer enters a separate state, COMMENT, when entering a
comment. On every comment open (/*), including the first, the current
line number is pushed onto a stack.  On every comment close (*/), the
head of the comment stack is popped.  If input ends before a comment
is closed, an error occurs which reports location of the last unclosed
comment open.  When the first comment open pushed onto the stack is
closed, the lexer re-enters the INITIAL state.

## Handling Errors
Appel's error handling module and line counting machinery is used by
our lexer to report error conditions.  In order for it to function
correctly, we count newlines and keep track of their location in the
byte stream using the provided variables.  We chose to employ more
states to catch and explicitly identify error cases. The error cases
we identify are:

### Errors inside strings
- unprintable characters
- newlines not enclosed in slashes \<...>\
- escape characters not defined in Tiger's specification (\q, \938, etc)
- characters enclosed in \<...>\ which are not formatting characters
- End of File (see section on EOF)

### Errors inside comments
- End of File (see section on EOF)

### Errors in the source body
- invalid characters

## Handling End of File
Encountering End-of-File is an error when inside of a string or inside
of a comment.  In both these cases, our lexer reports the line of the
EOF to Appel's error module, and an error message stating the line of
the opening comment or string.

## Things of interest.
- We created a keyword lookup table to reduce the number of states needed
- When building a string, we cons up a list of characters and then reverse the list
  to get the string representation