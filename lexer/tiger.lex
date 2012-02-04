type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult = (svalue, pos) token

 
val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
val commentStack: int list ref = ref []
val charList: char list ref = ref [];
val lineStart = ref 0;    

fun err(p1) = ErrorMsg.error p1        
			   
fun eof() =
    (if not((!commentStack = [])) then
	 let val line = hd(!commentStack)
	 in
	     err (hd(!linePos))  ("Found EOF in comment beginning at line " ^
				  Int.toString(line))
	 end
     else if not((!charList = [])) then
	 err (hd(!linePos)) ("Found EOF inside of string beginning at line " ^
			     Int.toString(!lineStart))
     else ();
     let val pos = hd(!linePos) in Tokens.EOF(pos,pos) end)

(* Strings can span multiple lines, save
   the position to know where the string started *)	      
fun saveLinePosition () = lineStart := !lineNum

(* Build a string from characters instead using of string concatenation *)			  
fun appendToCharList s =
    case Char.fromString(s)
     of SOME c => (charList := c :: !charList)
      | NONE => ErrorMsg.impossible ("Could not convert " ^ s ^ " to char.")

(* Converts a list of characters into a string token *)		
fun createString yypos  =
    let val s = implode(rev(!charList))
    in
	charList := []; (* Reset charList *)
	Tokens.STRING(s,yypos,yypos+String.size(s))
    end

(* Helper methods for nested comments  *)
    
fun pushCommentStartLine () =
     commentStack := !lineNum :: !commentStack;

fun popCommentStartLine () =
    commentStack := tl(!commentStack);

(* Helper function to convert a string to an integer *)    
fun getInt s =
    getOpt(Int.fromString(s),0);
    
structure KeywordMap = BinaryMapFn(struct
        type ord_key = string
        val compare = String.compare
    end)

(* Lookup table for keywords *)
		       
val empty: (int * int -> (svalue,int) token) KeywordMap.map = KeywordMap.empty;
val keywords  = foldr KeywordMap.insert' empty [
    ("while", Tokens.WHILE),
    ("for", Tokens.FOR),
    ("to", Tokens.TO),
    ("break", Tokens.BREAK),
    ("let", Tokens.LET),
    ("in", Tokens.IN),
    ("end", Tokens.END),
    ("function", Tokens.FUNCTION),
    ("var",	Tokens.VAR),
    ("type", Tokens.TYPE),
    ("array", Tokens.ARRAY),
    ("if", Tokens.IF),
    ("then", Tokens.THEN),
    ("else", Tokens.ELSE),
    ("do", Tokens.DO),
    ("of", Tokens.OF),
    ("nil", Tokens.NIL)];

(* Determines if a matched identifier is also a keyword and returns the
   appropriate token *)    
fun keywordMap(yytext, yypos) =
    case KeywordMap.find(keywords, yytext)
     of SOME keyword => keyword(yypos, yypos + String.size(yytext))
      | NONE => Tokens.ID(yytext, yypos, yypos + String.size(yytext));
			 
%%
%header (functor TigerLexFun(structure Tokens: Tiger_TOKENS));
%s COMMENT STRING ESCAPE FORMAT;
id=[a-zA-Z][a-zA-Z0-9_]*;
int=[0-9]+;
ws=[\ \t];
ctrlEsc=\^[A-Z@\[\]\\\^_\?];
decEsc=[01][0-9][0-9]|2[0-4][0-9]|25[0-5];
formatChar=[\ \t\n\f];
printable=[\032-\126];
validEsc=n|t|\\|\"|{ctrlEsc}|{decEsc};
%%

<INITIAL> \n	      => (lineNum := !lineNum+1;
			  linePos := yypos :: !linePos;
			  continue());
<INITIAL> {ws}        => (continue());
<INITIAL> "/*"        => (YYBEGIN(COMMENT);
			  pushCommentStartLine();
			  continue());
<INITIAL> "\""        => (saveLinePosition();
			  YYBEGIN(STRING);
			  continue());
<INITIAL> ","	      => (Tokens.COMMA(yypos,yypos+1));
<INITIAL> "("         => (Tokens.LPAREN(yypos, yypos+1));
<INITIAL> ")"         => (Tokens.RPAREN(yypos, yypos+1));
<INITIAL> ";"         => (Tokens.SEMICOLON(yypos, yypos+1));
<INITIAL> ":"         => (Tokens.COLON(yypos, yypos+1));
<INITIAL> "["         => (Tokens.LBRACK(yypos, yypos+1));
<INITIAL> "]"         => (Tokens.RBRACK(yypos, yypos+1));
<INITIAL> "{"         => (Tokens.LBRACE(yypos, yypos+1));
<INITIAL> "}"         => (Tokens.RBRACE(yypos, yypos+1));
<INITIAL> "."         => (Tokens.DOT(yypos, yypos+1));
<INITIAL> "+"         => (Tokens.PLUS(yypos, yypos+1));
<INITIAL> "-"         => (Tokens.MINUS(yypos, yypos+1));
<INITIAL> "*"         => (Tokens.TIMES(yypos, yypos+1));
<INITIAL> "/"         => (Tokens.DIVIDE(yypos, yypos+1));
<INITIAL> "="         => (Tokens.EQ(yypos, yypos+1));
<INITIAL> "<>"        => (Tokens.NEQ(yypos, yypos+2));
<INITIAL> "<"         => (Tokens.LT(yypos, yypos+1));
<INITIAL> "<="        => (Tokens.LE(yypos, yypos+2));
<INITIAL> ">"         => (Tokens.GT(yypos, yypos+1));
<INITIAL> ">="        => (Tokens.GE(yypos, yypos+2));
<INITIAL> "&"         => (Tokens.AND(yypos, yypos+1));
<INITIAL> "|"         => (Tokens.OR(yypos, yypos+1));
<INITIAL> ":="        => (Tokens.ASSIGN(yypos, yypos+2));
<INITIAL> {id}        => (keywordMap(yytext, yypos));
<INITIAL> {int}       => (Tokens.INT(getInt(yytext),
				     yypos,
				     yypos+String.size(yytext)));
<INITIAL> .           => (err yypos ("illegal character: " ^ yytext);
			  continue());

<COMMENT> \n          => (lineNum := !lineNum+1;
		          linePos := yypos :: !linePos;
		          continue());
		       
<COMMENT> "*/"        => (popCommentStartLine();
			  if (!commentStack)=[] then YYBEGIN(INITIAL)
			  else ();
		          continue());
		       
<COMMENT> "/*"        => (pushCommentStartLine();
		          continue());
		       
<COMMENT> .           => (continue());
	  
<STRING> \"           => (YYBEGIN(INITIAL);
		          createString(yypos));
			  
<STRING> \\           => (YYBEGIN(ESCAPE);
		       	 continue());

<STRING> {printable}  => (appendToCharList(yytext);
		       	 continue());

<STRING> \n           => (err yypos ("illegal newline inside string ");
			  continue());
    
<STRING> .            => (err yypos ("illegal character inside string " ^ yytext);
			  continue());

<ESCAPE> {validEsc}   => (appendToCharList("\\" ^ yytext); 
                          YYBEGIN(STRING);
			  continue());

<ESCAPE> {formatChar} => (YYBEGIN(FORMAT);
			  continue());
    
<ESCAPE> [0-9]{3}|.   => (err yypos ("illegal escape sequence \\" ^ yytext); 
                          YYBEGIN(STRING);
			  continue());

<FORMAT> \\           => (YYBEGIN(STRING);
			  continue());
    
<FORMAT> \n           => (lineNum := !lineNum+1;
		          linePos := yypos :: !linePos;
		          continue());
    
<FORMAT> {formatChar} => (continue());
    
<FORMAT> .            => (err yypos ("illegal escape sequence" ); 
                          YYBEGIN(STRING);
			  continue());



