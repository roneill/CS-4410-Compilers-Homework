type pos = int
type lexresult = Tokens.token
 
val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
val commentStack: int list ref = ref []
val stringAcc: char list ref = ref []
fun err(p1,p2) = ErrorMsg.error p1

fun eof() =
    (if(!commentStack) = [] then ()
     else
	 let val line = hd(!commentStack)  
	    in ErrorMsg.error 4 ("Found EOF in comment beginning at line " ^ Int.toString(line))
	 end;
     let val pos = hd(!linePos) in Tokens.EOF(pos,pos) end)
	
fun keywordMap ("while", yypos)    = Tokens.WHILE(yypos,yypos+5)
  | keywordMap ("for", yypos)      = Tokens.FOR(yypos, yypos+3)
  | keywordMap ("to", yypos)	   = Tokens.TO(yypos, yypos+2)
  | keywordMap ("break", yypos)    = Tokens.BREAK(yypos, yypos+5)
  | keywordMap ("let", yypos)	   = Tokens.LET(yypos, yypos+3)
  | keywordMap ("in", yypos)	   = Tokens.IN(yypos, yypos+2)
  | keywordMap ("end", yypos)	   = Tokens.END(yypos, yypos+3)
  | keywordMap ("function", yypos) = Tokens.FUNCTION(yypos, yypos+8)
  | keywordMap ("var", yypos)	   = Tokens.VAR(yypos, yypos+3)
  | keywordMap ("type", yypos)	   = Tokens.TYPE(yypos, yypos+4)
  | keywordMap ("array", yypos)    = Tokens.ARRAY(yypos, yypos+5)
  | keywordMap ("if", yypos)	   = Tokens.IF(yypos, yypos+5)
  | keywordMap ("then", yypos)	   = Tokens.THEN(yypos, yypos+4)
  | keywordMap ("else", yypos)	   = Tokens.ELSE(yypos, yypos+4)
  | keywordMap ("do", yypos)	   = Tokens.DO(yypos, yypos+2)
  | keywordMap ("of", yypos)	   = Tokens.OF(yypos, yypos+2)
  | keywordMap ("nil", yypos)	   = Tokens.NIL(yypos, yypos+3)
  | keywordMap (yytext, yypos)     = Tokens.ID(yytext, yypos, yypos+String.size(yytext));


%%
%s COMMENT STRING ESCAPE;
id=[a-zA-Z][a-zA-Z0-9_]*;
int=[0-9]+;
ws=[\ \t];
ctrlEsc=\^[A-Z@\[\]\\\^_\?];
decEsc=[01][0-9][0-9]|2[0-4][0-9]|25[0-5];
formatChar=\\[\ \t\n\f]+\\;
printable=[\ !\035-\091\093-\126]+;
validEsc=n|t|\\|\"|{ctrlEsc}|{decEsc};
%%

<INITIAL> \n	=> (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<INITIAL> {ws}+   => (continue());
<INITIAL> "/*"    => (YYBEGIN(COMMENT); continue());
<INITIAL> "\""    => (YYBEGIN(STRING); continue());
<INITIAL> ","	=> (Tokens.COMMA(yypos,yypos+1));
<INITIAL> "("     => (Tokens.RPAREN(yypos, yypos+1));
<INITIAL> ")"     => (Tokens.LPAREN(yypos, yypos+1));
<INITIAL> ";"     => (Tokens.SEMICOLON(yypos, yypos+1));
<INITIAL> ":"     => (Tokens.COLON(yypos, yypos+1));
<INITIAL> "["     => (Tokens.LBRACK(yypos, yypos+1));
<INITIAL> "]"     => (Tokens.RBRACK(yypos, yypos+1));
<INITIAL> "{"     => (Tokens.LBRACE(yypos, yypos+1));
<INITIAL> "}"     => (Tokens.RBRACE(yypos, yypos+1));
<INITIAL> "."     => (Tokens.DOT(yypos, yypos+1));
<INITIAL> "+"     => (Tokens.PLUS(yypos, yypos+1));
<INITIAL> "-"     => (Tokens.MINUS(yypos, yypos+1));
<INITIAL> "*"     => (Tokens.TIMES(yypos, yypos+1));
<INITIAL> "/"     => (Tokens.DIVIDE(yypos, yypos+1));
<INITIAL> "="     => (Tokens.EQ(yypos, yypos+1));
<INITIAL> "<>"    => (Tokens.NEQ(yypos, yypos+2));
<INITIAL> "<"     => (Tokens.LT(yypos, yypos+1));
<INITIAL> "<="    => (Tokens.LE(yypos, yypos+2));
<INITIAL> ">"     => (Tokens.GT(yypos, yypos+1));
<INITIAL> ">="    => (Tokens.GE(yypos, yypos+2));
<INITIAL> "&"     => (Tokens.AND(yypos, yypos+1));
<INITIAL> "|"     => (Tokens.OR(yypos, yypos+1));
<INITIAL> ":="    => (Tokens.ASSIGN(yypos, yypos+2));
<INITIAL> {id}   => (keywordMap(yytext, yypos));
<INITIAL> {int}  => (Tokens.INT(getOpt(Int.fromString(yytext),0), yypos, yypos+String.size(yytext)));
<INITIAL> .       => (ErrorMsg.error yypos ("illegal character " ^ yytext); continue());

<COMMENT> \n => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());

<COMMENT> "*/" => (if (!commentStack)=[] then YYBEGIN(INITIAL) else commentStack := tl(!commentStack); continue());

<COMMENT> "/*" => (commentStack := !lineNum :: !commentStack; continue());

<COMMENT> . => (continue());

<STRING> \" => (YYBEGIN(INITIAL);
		let val s = implode(!stringAcc) in Tokens.STRING(s,yypos,yypos+String.size(s)) end); 
<STRING> {printable} => (stringAcc := (!stringAcc)@explode(yytext); continue());

<STRING> \\ => (YYBEGIN(ESCAPE); continue());

<STRING> {formatChar} => (continue());

<STRING> . => (ErrorMsg.error yypos ("illegal character inside string " ^ yytext); continue());

<ESCAPE> {validEsc} => (stringAcc := (!stringAcc)@(#"\\"::explode(yytext)); 
                        YYBEGIN(STRING); continue());

<ESCAPE> [0-9]{3}|. => (ErrorMsg.error yypos ("illegal escape sequence \\" ^ yytext); 
                        YYBEGIN(STRING); continue());



