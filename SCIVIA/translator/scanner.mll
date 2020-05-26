{ open Parser }
let digits = ['0'-'9']
let sign = 's' | 'u'
let bits = '8' | "64" | "128" | "256"
let exp = ('e'|'E')('+'|'-')?['0'-'9']+
let cstylefloat = ('.'['0'-'9']+exp?|['0'-'9']+('.'['0'-'9']*exp?|exp))
let hexdigit = ['0'-'9''a'-'f''A'-'F']

rule token = parse
  [' ' '\r' '\n' '\t'] { token lexbuf } (* Whitespace *)
| "//"            { comment 1 lexbuf }      (* Comments *)
| "/*"            { multicomment 1 lexbuf }
| "IR:"           { token lexbuf }
| '('             { LPAREN }
| ')'             { RPAREN }
| '{'             { LBRACE }
| '}'             { RBRACE }
| '['             { LBRACK }
| ']'             { RBRACK }
| ';'             { SEMI }
| ':'             { COLON }
| ','             { COMMA }
| "->"            { ARROW }
| ":="            { ASSIGN }
| "True"          { BLIT(true)  }
| "False"         { BLIT(false) }
| "Bool"          { BOOL }
| 's' (bits as b) { INT(int_of_string b) }
| 'u' (bits as b) { UINT(int_of_string b) }
| "function"		  { FUNCTION }
| "for"         { FOR }
| "switch"      { SWITCH }
| "case"        { CASE }
| "default"     { DEFAULT }
| "break"       { BREAK }
| "continue"    { CONTINUE }
| "object"      { OBJECT }
| "code"        { CODE }
| "data"        { DATA }
| "let"         { LET }
| "if"          { IF }
| "hex" '"' (hexdigit+ as h) '"'    { HEXLIT(h) }
| "0x"  hexdigit+ as hn { HEXNUMBER(hn) }
| ['a'-'z' 'A'-'Z' '_' '$']['a'-'z' 'A'-'Z' '0'-'9' '_' '$' '.']*     as lxm { ID(lxm) }
| digits+ as lxm { NUMLIT(int_of_string lxm) }
| cstylefloat as lit { FLIT(float_of_string lit) } 
| '"' (([^'"']*) as s) '"'  { STRLIT(s) }
| eof           { EOF }
| _ as char { raise (Failure("illegal character " ^ Char.escaped char)) }

and code lvl = parse
  '{'           { code (lvl+1) lexbuf}
| '}'           { if lvl=1 then token lexbuf else code (lvl-1) lexbuf}

and comment lvl = parse
  "\n"  { if lvl = 1 then token lexbuf else comment (lvl - 1) lexbuf  }
| _     { comment lvl lexbuf }

and multicomment lvl = parse
  "*/"  { if lvl = 1 then token lexbuf else comment (lvl - 1) lexbuf  }
| _     { multicomment lvl lexbuf }
