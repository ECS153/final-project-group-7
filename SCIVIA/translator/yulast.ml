type typ =
  Bool
| Int of int
| Uint of int
| Id of string

type lit = 
  | HexLit of string
  | HexNum of string
  | StrLit of string
  | NumLit of int
  | BoolLit of bool

type expr = 
  | Id of string
  | FunctionCall of string * expr list
  | Literal of lit

type id = expr

type typedidentifiers = 
| TypedIdentifierList of id list

type targettypedidentifiers =
| NoTarget
| Target of id list

type variabledeclaration = 
  | Bind of typedidentifiers
  | BindAndAssign of typedidentifiers * expr

type stmt =
  | Block of stmt list
  | If of expr * stmt
  | FunctionDefinition of id * id list * targettypedidentifiers * stmt list
  | VariableDeclaration of variabledeclaration
  | Assignment of id list * expr
  | Expression of expr
  | Switch of expr * (lit * stmt) list * stmt list
  | ForLoop of stmt * expr * stmt * stmt
  | Break
  | Continue
  | Leave

type data = 
  | HexData of string * string
  | StrData of string * string
  | Nodata

type code =
  | Stmt of stmt list

type obj = 
  | Object of string * code * obj list
  | Data of string * lit
  | NoObj

type program = obj list
