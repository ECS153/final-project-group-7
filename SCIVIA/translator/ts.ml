open Yulast
(* open Sckspec *)
open Transenv


(* global translation environment instantiation *)
let translatedFuncs : (translatedFuncDetails ref) list ref = ref []

let getTranslatedFuncByYulName name = 
  let ret = List.fold_left (fun acc x -> 
    if (String.equal name (!x).tFuncName) then
      x
    else 
      acc
  ) (List.nth !translatedFuncs 0) !translatedFuncs in
  if String.equal (!ret).tFuncName name then ret
  else raise (TranslationErr ("No matching function for " ^ name))



(* example translation environment, made generic *)
let dummyDetail = 
  let solidityVar1 = {varName = ""; varYulAlias = ""; solType = SolUInt 64;} in
  let soliditySpecs1  = {
    paramList = []; 
    returnV = solidityVar1; 
    pre = [""]; 
    post = [""]; 
    assertions = [""];
  } in
  {funcName = ""; yulAlias = ""; spec = soliditySpecs1;}

let playSpecs =
  let solidityVar1 = {varName = "y"; varYulAlias = ""; solType = SolUInt 64;} in
  let solidityVar2 = {varName = "x"; varYulAlias = ""; solType = SolUInt 64;} in

  let solidityVar3 = {varName = ""; varYulAlias = ""; solType = SolBool;} in
  let solidityVar4 = {varName = "y"; varYulAlias = ""; solType = SolUInt 64;} in
  let soliditySpecs1  = {
    paramList = [solidityVar1]; 
    returnV = solidityVar3; 
    pre = []; 
    post = []; 
    assertions = [];
  } in
  let soliditySpecs2 = {
    paramList = [solidityVar2];
    returnV = solidityVar4;
    pre = ["x < 0"];
    post = ["greaterThanZero(y)"];
    assertions = [];
  } in
  let funcDetail1 = {funcName = "greaterThanZero"; yulAlias = ""; spec = soliditySpecs1;} in 
  let funcDetail2 = {funcName = "foo"; yulAlias = ""; spec = soliditySpecs2;} in 
  {
    gamma = []; 
    funcs = [funcDetail1; funcDetail2]; 
    thisFunc = dummyDetail; 
    builtin = builtInFuncs;
  }

(* core translator code *)
let rec indent lvl = 
  if lvl = 0 then "" else "  "  ^ indent (lvl - 1)

let rec string_of_id_nc smth =
  match smth with
  | Id(s) -> 
    let isKeyword = List.exists (fun x -> (String.equal x s)) whymlKeywords in
    let s = if isKeyword then conflictRenamePrefix ^ s else s in  
    String.map (fun c -> if ( c == '$') then '_' else c) s
  | _ -> raise (TranslationErr "unexpected string of id")

let rec string_of_id smth tenv =
  match smth with
  | Id(s) ->
    let isKeyword = List.exists (fun x -> (String.equal x s)) whymlKeywords in
    let s = if isKeyword then conflictRenamePrefix ^ s else s in 
    if (String.equal s tenv.thisFunc.spec.returnV.varYulAlias) then "!" ^ functionalRet else 
    String.map (fun c -> if ( c == '$') then '_' else c) s
  | _ -> raise (TranslationErr "unexpected string of id")

let rec ts_lit smth = 
  match smth with
    HexLit(s) -> "hex" ^ "\"" ^ s ^ "\""
  | HexNum(h) -> if h == "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" then
                  "0xffffffffffffffff"
                 else
                  h
  | StrLit(s) -> "\"" ^ s ^ "\""
  | NumLit(i) -> if i == 0 then yulHelperConst0
                 else  string_of_int i
  | BoolLit(b) -> let vl = if b then "true" else "false" in "(" ^ yulHelperB2W ^ " " ^ vl ^ ")"
  | _ -> ""

let rec string_of_expr lvl smth tenv =
  let idnt = indent (lvl) in
  match smth with
    FunctionCall(str, explist) ->
      let str = String.map (fun c -> if ( c == '$') then '_' else c) str in
      (* filter the require and asserts*)
      let specs = ["require"; "assert"] in
      let is_spec = List.fold_left 
                            (fun acc x -> (contains str x) || acc) 
                                false specs in
      
      let isBuiltin = List.exists (fun x -> (String.equal x str)) tenv.builtin in
      let isArith = List.exists (fun x -> (String.equal x str)) builtinArith in
      let isBP = List.exists (fun x -> (contains str x)) yulBP in
      let isIdent = List.exists (fun x -> (contains str x)) yulIdentity in
      let isKeyword = List.exists (fun x -> (String.equal x str)) whymlKeywords in
      let str = if isKeyword then conflictRenamePrefix ^ str else str in 
      let str = if isBuiltin then yulSemanticFormalShort ^ "." ^ str else str in

      (if not isBuiltin then
      if isBP then () else
      if isIdent then () else
      let translatedFuncRef = getTranslatedFuncByYulName tenv.thisFunc.yulAlias in
      (!translatedFuncRef).tFuncReferences <- 
        SS.add str (!translatedFuncRef).tFuncReferences);

      let str = if isBP then "Why3Inst.add" else str in
      let isBuiltin = if isBP then true else isBuiltin in
      let isArith = if isBP then true else isArith in

      let rawFuncCall = 
      "(" ^ str ^ " " ^ 
      " " ^ fgDeref ^ " " ^ 
      (String.concat " " (List.map (fun x -> "(" ^ (string_of_expr lvl x tenv) ^ ")") explist)) ^ 
      ")"
      in

      let builtinFuncArg = 
        (String.concat " " (List.map 
        (fun x ->
          match x with 
          | FunctionCall (id, elist) -> if isIdentF id then "(List.Cons " ^ (String.concat "" (List.map (fun x -> (string_of_expr lvl x tenv)) elist)) else "(List.Cons (" ^ (string_of_expr lvl x tenv) ^ ")"
          | _ -> "(List.Cons (" ^ (string_of_expr lvl x tenv) ^ ")" )
        explist)) ^ 
        " List.Nil" ^ 
        (String.concat "" (List.map (fun x -> ")") explist))
      in

      (* let isBuiltin = 
        if isBP then

          true
        else
          isBuiltin
      in *)

      if isIdent then
        idnt ^ (String.concat " " (List.map (fun x -> "(" ^ (string_of_expr lvl x tenv) ^ ")") explist))
      else
        if isBuiltin
        then
          "(" ^ yulStateFunctionGlobal ^ " := " ^ inputFunc ^ " " ^ fgDeref ^ " " ^ builtinFuncArg ^ "; " ^ 
          yulStateFunctionGlobal ^ " := " ^ str ^ " " ^ fgDeref ^ "; " ^ 
          outputFunc ^ " " ^ fgDeref ^
          (* idnt ^ "let " ^ yulStateCur ^ " = " ^ inputFunc ^ " " ^ yulStateCur ^ " " ^ builtinFuncArg ^ " in \n" ^ 
          idnt ^ "let " ^ yulStateCur ^ " = " ^ str ^ " " ^ yulStateCur ^ " in \n" ^ 
          idnt ^ "let rv = " ^ outputFunc ^ " " ^ yulStateCur ^ " in \n" ^  *)
          ")"
        else
          "(" ^ yulStateFunctionGlobal ^ " := " ^ rawFuncCall ^ "; " ^ 
          outputFunc ^ " " ^ fgDeref ^ ")"

        (* idnt ^ "let " ^ yulStateCur ^ " = " ^ rawFuncCall ^ " in \n" ^ 
        idnt ^ "let rv = " ^ outputFunc ^ " " ^ yulStateCur ^ ";" *)

      (* if isBuiltin
      then
        idnt ^ "let " ^ yulStateCur ^ " = " ^ inputFunc ^ " " ^ yulStateCur ^ " " ^ builtinFuncArg ^ " in \n" ^ 
        idnt ^ "let " ^ yulStateCur ^ " = " ^ str ^ " " ^ yulStateCur ^ " in \n" ^ 
        idnt ^ "let rv = " ^ outputFunc ^ " " ^ yulStateCur ^ " in \n" ^ 
        if isArith then
          idnt ^ "assert { 0 <= rv <= 255 };\n"
        else 
          ""
      else
          idnt ^ "let " ^ yulStateCur ^ " = " ^ rawFuncCall ^ " in \n" ^ 
          idnt ^ "let rv = " ^ outputFunc ^ " " ^ yulStateCur ^ " in \n" *)

        (* "(match " ^ rawFuncCall ^ " with | (st, v) -> state_gs := st; v end)" *)
      (* "(let temp_s, temp_v = " ^ rawFuncCall ^ " in (" ^ yulStateFunctionGlobal ^ " := temp_s); temp_v) " *)
  | Id(s) -> 
    (* check the _ret *)
    let isKeyword = List.exists (fun x -> (String.equal x s)) whymlKeywords in
    let s = if isKeyword then conflictRenamePrefix ^ s else s in
    if (String.equal s tenv.thisFunc.spec.returnV.varYulAlias) 
    then "!" ^ functionalRet
    else s
  | Literal(l) -> ts_lit l
  | _ -> ""

let rec ts_ttid_nc idlist =
  match idlist with
    NoTarget -> ""
  | Target(il) -> 
    if (List.length il) == 1 then 
      (string_of_id_nc (List.nth il 0)) 
    else 
      let params = String.concat ", " (List.map (fun x -> string_of_id_nc x) il) in
      "(" ^ params ^ ")"
      (* raise (TranslationErr "unexpected number of returns")   *)

let rec ts_ttid idlist tenv =
  match idlist with
    NoTarget -> ""
  | Target(il) -> 
    if (List.length il) == 1 then 
      (string_of_id (List.nth il 0) tenv) 
    else 
      let params = String.concat ", " (List.map (fun x -> string_of_id_nc x) il) in
      "(" ^ params ^ ")"
      (* raise (TranslationErr "unexpected number of returns")   *)

let string_of_typedidentifiers_nc smth =
  match smth with
    TypedIdentifierList(t) ->
      String.concat ", " (List.map (fun x -> string_of_id_nc x) t)

let string_of_typedidentifiers smth tenv =
  match smth with
    TypedIdentifierList(t) ->
      String.concat ", " (List.map (fun x -> string_of_id x tenv) t)

let ts_variabledeclaration lvl smth tenv isLast = 
  let idnt = indent lvl in
  match smth with
  | Bind(i) -> 
    (* used for memory instantiation *)
    let realName = string_of_typedidentifiers_nc i in
        if (String.equal realName tenv.thisFunc.spec.returnV.varYulAlias) then
          raise (TranslationErr "no bind without assign for return value")
        else
          if isLast then
            "let " ^ realName ^ " = " ^ ts_lit (NumLit 12828) ^ " in ();"
          else
            "let " ^ realName ^ " = " ^ ts_lit (NumLit 12828) ^ " in"
  | BindAndAssign(tid, exp) ->
      if String.equal (string_of_typedidentifiers tid tenv) "return_flag" then
        ""
      else
        let realName = string_of_typedidentifiers_nc tid in
        (* special case of _ret *)
        let isFuncCall = match exp with
        | FunctionCall (_, _) -> true
        | _ -> false
        in
        let prefix = 
            "let rv = " ^ (string_of_expr lvl exp tenv) ^ " in\n"
        in
        let appending = if isLast then " ();" else "" in
          idnt ^ prefix ^
          if (String.equal realName tenv.thisFunc.spec.returnV.varYulAlias) then
            (* idnt ^ "_ret := " ^ "rv" ^ ";" *)
            idnt ^ functionalRet ^ " := " ^ "rv;"
            (* idnt ^ "let " ^ functionalRet ^ " = " ^ "rv" ^ " in" ^ appending *)
            (* idnt ^ "let " ^ yulStateCur ^ " = " ^ "(setRet " ^ yulStateCur ^ " rv) in" ^ appending *)
          else
            idnt ^ "let " ^ realName ^ " = " ^ "rv" ^ " in" ^ appending
(* 
        (* special case of _ret *)
        let realName = string_of_typedidentifiers_nc tid in
        if (String.equal realName tenv.thisFunc.spec.returnV.varYulAlias) then
          "let " ^ yulStateCur ^ " = " ^ "(setRet " ^ yulStateCur ^ " " ^  (string_of_expr exp tenv) ^ ") in ();"
          (* "_ret := " ^ (string_of_expr exp tenv) ^ ";" *)
        else
          if isLast then
            "let " ^ realName ^ " = " ^ (string_of_expr exp tenv) ^ " in ();"
          else
            "let " ^ realName ^ " = " ^ (string_of_expr exp tenv) ^ " in" *)

let rec ts_match_asgn i exp lvl tenv isLast = 
  let idnt = indent lvl in
  (* ignore return_flag, it is dealt with break and setting actual value *)
  if String.equal (string_of_id (List.nth i 0) tenv) "return_flag" then
    ""
  else
    (* special case of _ret *)
    let isFuncCall = match exp with
    | FunctionCall (_, _) -> true
    | _ -> false
    in
    let prefix = 
        "let rv = " ^ (string_of_expr lvl exp tenv) ^ " in\n"
    in
    let appending = if isLast then " ();" else "" in
    idnt ^ prefix ^
    let str_i = (String.concat ", " (List.map (fun x -> string_of_id_nc x) i)) in 
      if (String.equal str_i tenv.thisFunc.spec.returnV.varYulAlias) then
        (* idnt ^ "_ret := " ^ "rv" ^ ";" *)
        idnt ^ functionalRet ^ " := " ^ "rv;"
        (* idnt ^ "let " ^ functionalRet ^ " = " ^ "rv" ^ " in" ^ appending *)
        (* idnt ^ "let " ^ yulStateCur ^ " = " ^ "(setRet " ^ yulStateCur ^ " rv) in" ^ appending *)
      else
        idnt ^ "let " ^ str_i ^ " = " ^ "rv" ^ " in" ^ appending

let rec ts_stmt lvl smth tenv isLast =
  let idnt = indent lvl in
  match smth with
  | FunctionDefinition(id, id_param_list, ty_id_ret, stmt_list) ->
      let str_id = string_of_id_nc id in
        (* instantiate the translated DAG node *)
        let thisTranslatedFunc = 
          ref {tFuncName = str_id; tFuncString = ""; tFuncReferences = SS.empty;} 
        in
        translatedFuncs := (List.cons thisTranslatedFunc !translatedFuncs);
        let is_target_func = List.fold_left 
                              (fun acc x -> 
                                let isThisName = contains str_id x.funcName in 
                                if isThisName then x.yulAlias <- str_id else ();
                                isThisName || acc
                              )
                              false
                              tenv.funcs in
        let is_target_func = is_target_func || (
          List.fold_left 
          (fun acc x -> 
            (contains str_id x) || acc
          )
          false
          functionShortCut
        ) in
        let thisReturnVarStr = ts_ttid_nc ty_id_ret in
        (* setting the return value to proper type *)
        let retType = if (String.equal thisReturnVarStr "") 
        (* "(" ^ yulStateType ^ ", " ^ yulUint64FormalShortType ^ ")" *)
        then " : " ^ yulStateType
        else 
          if is_target_func then
            let thisFuncDetail = getFuncDetailByYulName tenv str_id in
            thisFuncDetail.spec.returnV.varYulAlias <- thisReturnVarStr;
            " : " ^ 
            "(" ^ yulStateType ^ ", " ^ 
            (getSolTypeString thisFuncDetail.spec.returnV.solType) ^ 
            ")"
          else " : " ^ yulStateType
          (* consider matching the internal function types *)
          (* UNFINISHED *)
              in 
        let params = 
          if (List.length id_param_list) == 0 then
            " (" ^ universalFirstArg ^ ") "
          else
            if is_target_func then
              let thisFuncDetail = getFuncDetailByYulName tenv str_id in
              (List.mapi (fun idx x -> 
                let corParam = string_of_id_nc (List.nth id_param_list idx) in
                let paramNamesMatch = contains corParam x.varName in 
                if paramNamesMatch then
                  x.varYulAlias <- corParam
                else
                  raise (TranslationErr "parameter names does not match")
              ) thisFuncDetail.spec.paramList);
              " (" ^ universalFirstArg ^ ") " ^ 
              (String.concat " " 
                (List.map (fun x -> " (" ^ x.varYulAlias ^ ": " ^ getSolTypeString x.solType ^ ")") thisFuncDetail.spec.paramList)
              )
            else 
            (* consider matching the internal function types *)
            (* UNFINISHED *)
              " (" ^ universalFirstArg ^ ") " ^
              (String.concat " " 
                (List.map (fun x -> 
                    " (" ^ (string_of_id_nc x) ^ ": " ^ yulUint64FormalShortType ^ ")"
                  ) id_param_list)
              )
        in
        let func_signature = 
          idnt ^ "let ghost " ^ "function " ^ str_id ^ 
          (* translate parameter *)
          params ^
          (* translate return type *)
          retType
        in
        let func_body = 
          if is_target_func then
              (* if this function has any specs *)
            if String.equal yulVersion "0.5.13" 
            then
              let filterOuterFor le = match le with 
                  | ForLoop(init, condition, post, body) -> match body with
                      | Block(sl) -> sl
                      | _ -> raise (TranslationErr "no block for loop in yul")
                  | _ -> raise (TranslationErr "first not for loop in yul") in
              let filteredStmts = 
                if (List.length stmt_list) == 1 then 
                  filterOuterFor (List.nth stmt_list 0)
                else 
                  raise (TranslationErr ("Unexpected translation pattern in yul, at " ^ str_id)) in
              (* let filteredStmts = stmt_list in *)
              (
                tenv.thisFunc <- getFuncDetailByYulName tenv str_id;
                (String.concat "\n" (List.map (fun x -> (ts_stmt (lvl+1) x tenv isLast) ) filteredStmts))
              )
            else 
              (* defualt version to be 0.6.2 *)
              (
                tenv.thisFunc <- getFuncDetailByYulName tenv str_id;
                (String.concat "\n" (List.map (fun x -> (ts_stmt (lvl+1) x tenv isLast) ) stmt_list))
              )
          else
            let tempYulRetV = {varName = thisReturnVarStr; varYulAlias = thisReturnVarStr; solType = SolUInt 64;} in
            let tempYulSoliditySpec = {paramList = []; returnV = tempYulRetV; pre = []; post = []; assertions = [];} in
            let tempYulFuncDetail = { funcName = str_id; yulAlias = str_id; spec = tempYulSoliditySpec;} in
            tenv.thisFunc <- tempYulFuncDetail;
            (String.concat "\n" (List.map (fun x -> (ts_stmt (lvl+1) x tenv isLast)) stmt_list))
        in 
        let func_spec = 
          (String.concat "\n" 
            (List.map (fun x -> 
                idnt ^ "requires { 0 <= " ^ (string_of_id_nc x) ^ " <= 255 }"
              ) id_param_list)
          )
          (* if is_target_func then 
            let thisFuncDetail = getFuncDetailByYulName tenv str_id in
            let idntp = (indent (lvl+1)) in
            (String.concat "\n" (List.map (fun x -> 
              idntp ^ "requires" ^ " { " ^ x ^ " } "
              ) 
            tenv.thisFunc.spec.pre)) ^ "\n" ^
            (String.concat "\n" (List.map (fun x -> 
              idntp ^ "ensures" ^ " { " ^ x ^ " } "
              ) 
            tenv.thisFunc.spec.post))
            (* take care of thisFuncDetail.assertions *)
            (* UNFINISHED *)
          else "" *)
        in
        let finalTranslatedFuncStr = 
        func_signature ^
        (* translate specs, require and ensures*)
        (
        if (String.equal thisReturnVarStr "") then ""
        else   
          if String.equal "" func_spec then "\n" ^
          idnt ^ " " ^ manualAxiomGenerator1 ^ "\n" ^
          idnt ^ " " ^ manualAxiomGenerator2 ^ "\n"
          else 
          "\n" ^ func_spec ^ "\n"
        ) ^     
        (* translate body*)
        idnt ^ "=\n" ^
        idnt ^ "let _r: ref int" ^ " = ref 0 in\n" ^
        idnt ^ "let ghost " ^ yulStateFunctionGlobal ^ ": " ^ "ref " ^ yulStateType ^ " = ref " ^ yulStateCur ^ " in\n" ^
        idnt ^ yulConstDeclaration ^ "\n" ^ 
        
        idnt ^ "try\n" ^
        idnt ^ " " ^ "begin\n" ^
        idnt ^ "  " ^ "let return_flag = " ^ yulHelperB2W ^ " false" ^ " in\n" ^
        (* idnt ^ "  " ^ "let " ^ functionalRet ^ " : ref int = ref 0 in\n" ^  *)
        func_body ^ "\n" ^
        idnt ^ " " ^ "end;\n" ^
        idnt ^ " " ^ "st_g := (setRet !st_g !_r);\n" ^
        idnt ^ " " ^ "raise Ret\n" ^
        idnt ^ "with Ret -> " ^ 
        (* (if (String.equal thisReturnVarStr "") then "(" ^ "!" ^ yulStateFunctionGlobal ^ ", ()" ^ ")"
        else "(" ^  "!" ^ yulStateFunctionGlobal ^ ", !_ret" ^ ")") *)
        fgDeref ^ 
        " \n" ^
        idnt ^ "end\n" in
        (!thisTranslatedFunc).tFuncString <- finalTranslatedFuncStr;
        (!thisTranslatedFunc).tFuncString

  | Assignment(i, exp) ->
      ts_match_asgn i exp lvl tenv false
  | Expression(exp) ->
      (* special handling of functional gap, expr is not stmt *)
      let func exp = match exp with
        FunctionCall(str, explist) ->
          (* filter the require and asserts*)
          let specs = ["require"; "assert"] in
          let is_spec = List.fold_left 
                                (fun acc x -> (contains str x) || acc) 
                                    false specs in

          let isBuiltin = List.exists (fun x -> (String.equal x str)) tenv.builtin in
          let isKeyword = List.exists (fun x -> (String.equal x str)) whymlKeywords in
          let isArith = List.exists (fun x -> (String.equal x str)) builtinArith in
          let isBP = List.exists (fun x -> (contains str x)) yulBP in
          let isIdent = List.exists (fun x -> (contains str x)) yulIdentity in
          let str = if isKeyword then conflictRenamePrefix ^ str else str in 
          let str = if isBuiltin then yulSemanticFormalShort ^ "." ^ str else str in
          (* let firstParam = if isBuiltin then " (" ^ universalFirstArg ^ ") " else "" in *)
          
          (if not isBuiltin then
            if isBP then () else
            if isIdent then () else
            let translatedFuncRef = getTranslatedFuncByYulName tenv.thisFunc.yulAlias in
            (!translatedFuncRef).tFuncReferences <- 
              SS.add str (!translatedFuncRef).tFuncReferences);

          (* if a function call is used like a statement, then it should not have temp_v *)

          let rawFuncCall = 
          "(" ^ str ^ " " ^ 
          fgDeref ^ 
          (String.concat " " (List.map (fun x -> string_of_expr lvl x tenv) explist)) 
          ^ ")"
          in
(* 
          let specs = ["require"; "assert"] in
          let get_expr_func_name smth = 
            match smth with
              FunctionCall(str, explist) -> str
            | _ -> "" 
          in
          let str = get_expr_func_name exp in
          let is_spec = List.fold_left 
                                (fun acc x -> (contains str x) || acc) 
                                    false specs in *)

          (* List.filter (fun x -> match x with | FunctionCall(_, _) -> true else false) explist *)
                                    

          let is_spec = if String.equal str "" then false else is_spec in
          (* let appending =  *)
          if is_spec 
          then
                if List.length explist != 1 then
                  raise (TranslationErr "specification takes only one argument")
                else 
                  let str_i = (String.concat " " (List.map (fun x -> "(" ^ (string_of_expr lvl x tenv) ^ ")") explist)) in
                    if contains str "require" then
                      "\n" ^ idnt ^ "assume { " ^ "i2b " ^ str_i ^ " };"
                    else
                      if contains str "assert" then
                        "\n" ^ idnt ^ "assert { " ^ "i2b " ^ str_i ^ " };"
                      else 
                        raise (TranslationErr "keyword mismatch")
          else

          let str = if isBP then "Why3Inst.add" else str in
          let isBuiltin = if isBP then true else isBuiltin in
          let isArith = if isBP then true else isArith in

          let builtinFuncArg = 
            (String.concat " " (List.map 
              (fun x ->
                match x with 
                | FunctionCall (id, elist) -> if isIdentF id then "(List.Cons " ^ (String.concat "" (List.map (fun x -> (string_of_expr lvl x tenv)) elist)) else "(List.Cons (" ^ (string_of_expr lvl x tenv) ^ ")"
                | _ -> "(List.Cons (" ^ (string_of_expr lvl x tenv) ^ ")" )
            explist)) ^ 
            " List.Nil" ^ 
            (String.concat "" (List.map (fun x -> ")") explist))
          in 
          
          if isIdent then
            idnt ^ (String.concat " " (List.map (fun x -> "(" ^ (string_of_expr lvl x tenv) ^ ")") explist))
          else
            if isBuiltin
            then
              "(" ^ yulStateFunctionGlobal ^ " := " ^ inputFunc ^ " " ^ fgDeref ^ " " ^ builtinFuncArg ^ "; " ^ 
              yulStateFunctionGlobal ^ " := " ^ str ^ " " ^ fgDeref ^ "; " ^ 
              (* idnt ^ "let " ^ yulStateCur ^ " = " ^ inputFunc ^ " " ^ yulStateCur ^ " " ^ builtinFuncArg ^ " in \n" ^ 
              idnt ^ "let " ^ yulStateCur ^ " = " ^ str ^ " " ^ yulStateCur ^ " in \n" ^ 
              idnt ^ "let rv = " ^ outputFunc ^ " " ^ yulStateCur ^ " in \n" ^  *)
              (if isArith then
                idnt ^ "assert { 0 <= rv <= 255 };"
              else 
                "")
              ^
                if isLast then ")" else ");"
            else
              "(" ^ yulStateFunctionGlobal ^ " := " ^ rawFuncCall ^ "; );"

            (* idnt ^ "let " ^ yulStateCur ^ " = " ^ rawFuncCall ^ " in \n" ^ 
            idnt ^ "let rv = " ^ outputFunc ^ " " ^ yulStateCur ^ ";" *)

      | _ -> idnt ^ (string_of_expr lvl exp tenv) in
      func exp
  | VariableDeclaration(vd) ->
      idnt ^ ts_variabledeclaration lvl vd tenv false
  | If(e,s) ->
      (* translate to if, ocaml able to do this kind of control flow iff return is unit *)
      let isFuncCall = match e with
        | FunctionCall (_, _) -> true
        | _ -> false
      in
      let prefix = 
          idnt ^ "let rv = " ^ (string_of_expr lvl e tenv) ^ " in\n"
      in
      prefix ^   
      (* idnt ^ "let st = \n" ^ *)
      idnt ^ "(if " ^ yulHelperW2B ^ " rv \n" ^
      idnt ^ "then\n" ^ 
      ts_stmt (lvl+1) s tenv isLast ^ "\n" ^
      idnt ^ ");\n"
      (* idnt ^ "else\n" ^
      idnt ^ " " ^ yulStateCur ^ "\n" ^  *)
      (* if isLast then "" else idnt ^ "in\n" *)

      (* idnt ^ ""
      idnt ^ "(if \n" ^ 
      (* idnt ^ " " ^ "(\n" ^  *)
      (* "(" ^  ^ ")"  *)
      (indent (lvl+1)) ^ "(" ^ yulHelperW2B ^ " " ^ string_of_expr e tenv ^ ")\n" ^
      (* idnt ^ " " ^ ")\n" ^  *)
      idnt ^ " " ^ "then " ^ "\n" ^ 
      ts_stmt (lvl+1) s tenv ^ "\n" ^
      idnt ^ ");" *)
  | ForLoop(init, condition, post, body) ->
      (* translate to while *)
      let idntp = (indent (lvl+1)) in
      let idntpp = (indent (lvl+2)) in

      let isFuncCall = match condition with
        | FunctionCall (_, _) -> true
        | _ -> false
      in
      let prefix = 
          idnt ^ "let rv = " ^ (string_of_expr lvl condition tenv) ^ " in\n"
      in
      (ts_stmt (lvl+1) init tenv isLast) ^ "\n" ^
      prefix ^   
      idntp ^ "(while not " ^ yulHelperW2B ^ " rv " ^  "\n" ^ 
      idntp ^ " do" ^ "\n" ^
      idntp ^ "  variant {} \n" ^
      (ts_stmt (lvl+2) body tenv isLast) ^ "\n" ^
      (ts_stmt (lvl+2) post tenv isLast) ^ "\n" ^
      idntp ^ "done);" ^ "\n"
      (* if isLast then "" else idnt ^ "in\n" *)


      (* idnt ^ "(\n" ^
      (ts_stmt (lvl+1) init tenv) ^ "\n" ^
      idntp ^ "while" ^ " not " ^ 
      "(" ^ yulHelperW2B ^ " " ^ (string_of_expr condition tenv) ^ ")" ^
      " do" ^ "\n" ^
      (ts_stmt (lvl+2) body tenv) ^ "\n" ^
      (ts_stmt (lvl+2) post tenv) ^ "\n" ^
      idntp ^ "done" ^ "\n" ^
      idnt ^ ");" *)
  | Block(b) ->
      idnt ^ "(\n" ^ 
      (String.concat "\n" (List.mapi (
        fun idx x ->  if (idx < (List.length b) - 1) 
                      then 
                        ts_stmt (lvl+1) x tenv false
                      else
                        let lastInList = (List.hd (List.rev b)) in
                        let idnt = (indent (lvl+1)) in 
                        match lastInList with 
                        | VariableDeclaration(vd) -> idnt ^ ts_variabledeclaration lvl vd tenv true
                        | Assignment(i, exp) -> ts_match_asgn i exp (lvl + 1) tenv true
                        | _ -> ts_stmt (lvl+1) lastInList tenv true
        ) b))
      (* ^ "\n" ^ *)
      ^ idnt ^ "); "
      (* idnt ^ yulStateCur *)
  | Break -> 
      idnt ^ "break"
  | Continue -> "continue"
  | Leave -> 
      idnt ^ yulStateFunctionGlobal ^ " := " ^ "(setRet " ^ fgDeref ^ " " ^ functionalRet ^ ") in\n" ^
      (* idnt ^ "let " ^ yulStateCur ^ " = " ^ "(setRet " ^ yulStateCur ^ " " ^ functionalRet ^ ") in\n" *)
      "raise Ret"
  | Switch(exp, case_list, default_list) -> 
      (* (lit * stmt) list, stmt list *)
      let idntp = (indent (lvl+1)) in
      let idntpp = (indent (lvl+2)) in

      let isFuncCall = match exp with
        | FunctionCall (_, _) -> true
        | _ -> false
      in
      let prefix = 
          idnt ^ "let rv = " ^ (string_of_expr lvl exp tenv) ^ " in\n"
      in
      prefix ^   
      (* idnt ^ "let st = \n" ^  *)
      idntp ^ "(match rv with \n" ^
      (String.concat "\n" (List.map
        (fun (case_lit, case_stmt) -> 
        idntp ^ "| " ^ ts_lit case_lit ^ " -> \n" ^ 
          (ts_stmt (lvl+2) case_stmt tenv isLast)
        )
        case_list
      )) ^ "\n" ^ 

      idntp ^ "| _ -> " ^ "\n" ^ 
      idntpp ^ "(\n" ^ 
      (String.concat "\n" (List.mapi (
        fun idx x ->  if (idx < (List.length default_list) - 1) 
                      then 
                        ts_stmt (lvl+3) x tenv false
                      else
                        let lastInList = (List.hd (List.rev default_list)) in
                        match lastInList with 
                        | VariableDeclaration(vd) -> idntpp ^ ts_variabledeclaration lvl vd tenv true
                        | Assignment(i, exp) -> ts_match_asgn i exp (lvl+3) tenv true
                        | _ -> ts_stmt (lvl+3) lastInList tenv true
        ) default_list))
      ^ "\n"
      ^ idntpp ^ ");" ^ 
      
      "\n" ^
      idntp ^ "end);"
      (* if isLast then "" else idnt ^ "in\n" *)
      
(*       
      idnt ^ "(match \n" ^
      idntp ^ (string_of_expr exp tenv) ^ "\n" ^
      idnt ^ "with" ^ "\n" ^ 
      (String.concat "\n" (List.map
        (fun (case_lit, case_stmt) -> 
        idntp ^ "| " ^ ts_lit case_lit ^ " -> \n" ^ 
          (ts_stmt (lvl+2) case_stmt tenv)
        )
        case_list
      )) ^ "\n" ^ 

      idntp ^ "| _ -> " ^ "\n" ^ 

      (* translation of a list of stmts, alike block *)
      idntpp ^ "(\n" ^ 
      (String.concat "\n" (List.mapi (
        fun idx x ->  if (idx < (List.length default_list) - 1) 
                      then 
                        ts_stmt (lvl+3) x tenv
                      else
                        let lastInList = (List.hd (List.rev default_list)) in
                        match lastInList with 
                        | VariableDeclaration(vd) -> idntpp ^ ts_variabledeclaration vd tenv true
                        | Assignment(i, exp) -> ts_match_asgn i exp (lvl+3) tenv true
                        | _ -> ts_stmt (lvl+3) lastInList tenv
        ) default_list))
      ^ "\n"
      ^ idntpp ^ ");" ^ 
      
      "\n" ^
      idnt ^ "end" ^
      idnt ^ ");" *)
  | _ -> ""

let rec ts_code lvl smth tenv =
  let idnt = indent lvl in
  let funcOnly x = match x with
      FunctionDefinition(id, id_param_list, ty_id_ret, stmt_list) ->
        let str_id = string_of_id_nc id in
        let isBP = List.exists (fun x -> (contains str_id x)) yulBP in
        let isIdent = List.exists (fun x -> (contains str_id x)) yulIdentity in
        if isBP 
        then 
          false
        else
          if isIdent then false else
          true
    | _ -> false
  in 
  match smth with
    Stmt(s) -> let s_cleaned = List.filter funcOnly s in
        (* deal with the ordering here *)
        let unordered = 
          (* clean the double raise Ret and breaks *)
          String.concat "\n" (List.map (fun x -> ts_stmt (lvl+1) x tenv false) s_cleaned)
        in

        (* add rec keyword to those functions refer to itself *)
        (
          List.map 
          (fun x -> 
            if 
              (SS.mem (!x).tFuncName (!x).tFuncReferences) 
            then 
              (
                ( (!x).tFuncString <- addRec (!x).tFuncString );
                (!x).tFuncReferences <- SS.remove (!x).tFuncName (!x).tFuncReferences
              )
            else 
              ()
          ) !translatedFuncs
        );
        
        let rec rec_ordering rightOrder = 
          (* recurse until fixpoint, aka when no nodes left *)
          let thisIter = List.filter (fun x -> 0 == SS.cardinal (!x).tFuncReferences) !translatedFuncs in
          if List.length thisIter == 0 && List.length !translatedFuncs != 0 then
            let failedF = 
              String.concat "\n" (List.map (fun x -> 
                "{ " ^ 
                (String.concat ", " (SS.elements (SS.map (fun y -> y) (!x).tFuncReferences))) ^ " } -> " ^
                string_of_int (SS.cardinal (!x).tFuncReferences) ^ " -> " ^  (!x).tFuncName) !translatedFuncs)
            in
            raise (TranslationErr ("mutual recursion, loop in DAG: \n" ^ failedF))
          else 
            if List.length !translatedFuncs == 0 then rightOrder
            else 
              let rightOrder = List.append rightOrder (List.map (fun x -> (!x).tFuncString) thisIter)  in
              (* delete edges to this node *)
              (List.map 
                (fun elt -> 
                  (List.map (fun x -> 
                      (if SS.mem (!elt).tFuncName (!elt).tFuncReferences then 
                        (!elt).tFuncReferences <- SS.remove (!elt).tFuncName (!elt).tFuncReferences
                      else ());
                      (if SS.mem (!x).tFuncName (!elt).tFuncReferences then 
                        (!elt).tFuncReferences <- SS.remove (!x).tFuncName (!elt).tFuncReferences
                      else ());
                    ) thisIter
                  )
                )
                !translatedFuncs
              );
              (* delete node in DAG *)
              translatedFuncs := (List.filter (fun x -> not (List.mem x thisIter)) !translatedFuncs);
              rec_ordering rightOrder
        in
        let r = Str.regexp "leave" in
        let r2 = Str.regexp "0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" in
        Str.global_replace r2 "0xffffffffffffffff"
        (Str.global_replace r "raise Ret" (cleanDoubleBreaks ( String.concat "\n" (rec_ordering []) )))
        (* translatedFuncs := 
        (List.sort (fun x1 x2 -> 
          let x1c = SS.cardinal (!x1).tFuncReferences in 
          let x2c = SS.cardinal (!x2).tFuncReferences in
          if x1c == x2c then 0
          else 
            if x1c > x2c then 1 else 0
        ) !translatedFuncs); *)
        
        (* String.concat "\n" (List.map (fun x -> 
          string_of_int (SS.cardinal (!x).tFuncReferences) ^ " " ^ (!x).tFuncName
        ) !translatedFuncs) *)
        (* unordered *)
        (* String.concat "\n" (List.map (fun x -> (!x).tFuncName) !translatedFuncs) *)
  | _ -> ""

let rec ts_object lvl smth tenv = 
  let idnt = indent lvl in
  match smth with
    Object(n, c, dataobj) ->
      ts_code (lvl) c tenv
  | _ ->
      ""

let ts_program prog =
  let buf_overflow = [
    "safe_index_overflow";
    "unsafe_index_overflow";
    "safe_index_underflow";
    "unsafe_index_underflow";
    "pure_mode";
    "wild_key_access";
  ] in
  let idnt = "  " in
  let tEnvIni = playSpecs in
  evmStateMDefinition ^ 
"
module TS
  use int.Int
  use ref.Ref
  use map.Map
  use array.Array
  use list.List
  use int.ComputerDivision
  use mach.int.Unsigned
  clone EVMState

  " ^ "\n" ^

  idnt ^ yulUint64FormalImport ^ "\n" ^ 
  idnt ^ yulSemanticFormalImport ^ "\n" ^
  idnt ^ yulStateFormalImport ^ "\n" ^ 
  idnt ^ yulHelperFormalImport ^ "\n" ^
"
  exception Ret

" ^ 
  (String.concat "\n" (List.map (fun obj -> ts_object 0 obj tEnvIni) prog)) ^ 
"
end
"

(* Object list *) 
  
