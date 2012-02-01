type pos = int
type lexresult = Tokens.token
 
val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
val commentStack: int list ref = ref []
fun err(p1,p2) = ErrorMsg.error p1

fun eof() =
    (if(!commentStack) = [] then ()
     else
	 let val line = hd(!commentStack)  
	    in ErrorMsg.error 4 (* FIX *) ("Found EOF in comment beginning at line " ^ Int.toString(line))
	 end;
     let val pos = hd(!linePos) in Tokens.EOF(pos,pos) end)
    
structure KeywordMap = BinaryMapFn(struct
        type ord_key = string
        val compare = String.compare
    end)

(* Lookup table for keywords *)		       

val keywords  = foldr KeywordMap.insert' KeywordMap.empty [
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

fun keywordMap(yytext, yypos) =
    case KeywordMap.find(keywords, yytext)
     of SOME keyword => keyword(yypos, yypos + String.size(yytext))
      | NONE => Tokens.ID(yytext, yypos, yypos + String.size(yytext));

(* Functions to build a string with characters *)    

structure StringBuilder  = struct
type clr = char list ref;
val charList: clr = ref [];
    
fun appendCharString s =
    case Char.fromString(s)
     of SOME c => charList := c :: !charList
      | NONE => () (* Should never get here *)

fun getString yypos  =
    let val s = implode(rev(!charList))
    in
	charList := []; (* Reset charList *)
	Tokens.STRING(s,yypos,yypos+String.size(s))
    end
    
end

fun getInt s =
    getOpt(Int.fromString(s),0);
    
			 
%%
%s COMMENT STRING ESCAPE;
id=[a-zA-Z][a-zA-Z0-9_]*;
int=[0-9]+;
ws=[\ \t];
ctrlEsc=\^[A-Z@\[\]\\\^_\?];
decEsc=[01][0-9][0-9]|2[0-4][0-9]|25[0-5];
formatChar=\\[\ \t\n\f]+\\;
printable=[\032-\126];
validEsc=n|t|\\|\"|{ctrlEsc}|{decEsc};
%%

<INITIAL> \n	      => (lineNum := !lineNum+1;
			  linePos := yypos :: !linePos;
			  continue());
<INITIAL> {ws}+       => (continue());
<INITIAL> "/*"        => (YYBEGIN(COMMENT); continue());
<INITIAL> "\""        => (YYBEGIN(STRING); continue());
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
<INITIAL> .           => (ErrorMsg.error yypos ("illegal character " ^ yytext);
			  continue());

<COMMENT> \n          => (lineNum := !lineNum+1;
		          linePos := yypos :: !linePos;
		          continue());
		       
<COMMENT> "*/"        => (if (!commentStack)=[] then YYBEGIN(INITIAL) else commentStack := tl(!commentStack);
		          continue());
		       
<COMMENT> "/*"        => (commentStack := !lineNum :: !commentStack;
		          continue());
		       
<COMMENT> .           => (continue());
	  
<STRING> \"           => (YYBEGIN(INITIAL);
		          StringBuilder.getString(yypos)); 
		       
<STRING> \\           => (YYBEGIN(ESCAPE);
		       	 continue());

<STRING> {printable}  => (StringBuilder.appendCharString(yytext);
		       	 continue());
		       
<STRING> {formatChar} => (continue());

<STRING> .            => (ErrorMsg.error yypos ("illegal character inside string " ^ yytext);
			  continue());

<ESCAPE> {validEsc}   => (StringBuilder.appendCharString(yytext); 
                          YYBEGIN(STRING); continue());

<ESCAPE> [0-9]{3}|.   => (ErrorMsg.error yypos ("illegal escape sequence \\" ^ yytext); 
                          YYBEGIN(STRING); continue());



