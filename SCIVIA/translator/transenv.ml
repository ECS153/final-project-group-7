(* open Sckspec *)
open Yulast

type solidityType = 
  SolBool
| SolUInt of int (* here the int represents 64, etc. *)
| SolInt of int

type solidityVar = 
  {
    varName: string;
    mutable varYulAlias: string;
    solType: solidityType;
  }

type soliditySpecs = 
  {
    paramList: solidityVar list;
    returnV: solidityVar;
    pre: string list;
    post: string list;
    assertions: string list;
  }

type funcDetails = 
  {
    funcName : string;
    mutable yulAlias : string;
    spec: soliditySpecs;
  }

module SS = Set.Make(String)

module MS = Map.Make(String)

type translatedFuncDetails = 
  {
    tFuncName : string;
    mutable tFuncString : string;
    mutable tFuncReferences : SS.t;
  }

type transalationEnv = 
  {
    gamma : (string * string) list;
    funcs : funcDetails list;
    mutable thisFunc : funcDetails;
    builtin : string list;
  }

let builtinArith = [
  "add";
  "sub";
  "mul";
  "div";
]

let yulBP = [
  "checked_add";
]

let yulIdentity = [
  "convert_t_rational";
  "cleanup_t_uint256";
]

let builtInFuncs = [
  "keccak256";
  "sload";
  "sstore";
  "mload";
  "mstore";
  "stop";
  "revert";
  "iszero";
  "eq";
  "gt";
  "mod";
  "lt";
  "not";
  "and";
  "or";
  "xor";
  "add";
  "sub";
  "mul";
  "div";
  "calldataload";
  "calldatacopy";
  "calldatasize";
  "callvalue";
  "caller";
  "slt";
  "shr";
  "shl";
  "invalid";
  "balance";
  "log1";
]

(* subject to completion *)
let builtinFuncsWithState = 
  [
    "mload";
    "mstore";
    "callvalue";
    "stop";
    "revert";
    "balance";
  ]

let whymlKeywords = 
  [
    "let";
    "end";
    "not";
  ]

let conflictRenamePrefix = "bw_"

let manualAxiomGenerator1 = "ensures { 0 <= runState result <= 255 }"
let manualAxiomGenerator2 = "ensures { runState result = 0 }"

let staticAnalysis = 
"
  (* Semantic Fact Relations for Static Analysis *)

  (* Flow Dependency *)
  predicate mayFollow string string (* Instruction at label L2 may follow that at label L1. *)
  predicate mustFollow string string (* Instruction at label L2 must follow that at label L1. *)
  
  (* Data Dependency *)
  predicate mayDependOn string string (* Y, T. The value of Y may depend on tag T . *)
  predicate eq string string  (* The values of Y and T are equal. *)
  predicate detBy string string (* For different values of T the value of Y is different. *)

  (* EVM Call *)
  (* instr(L, Y, X1, ..., Xn), L label, Y is variable storing result, X is param *)
  predicate assign string string string
  predicate sstore string string string
  predicate op string string string
  predicate mload string string string

  (* Predicate *)
  predicate isConst string

  (* Memory Analysis Inference *)
  predicate MemTag string string string
  predicate ReassignMem string string string

  (* Implicit Control-flow Analysis*)
  predicate Taint string string string
  
  (* Properties *)
  axiom transitivityMayDependOn [@rewrite]:
    forall x: string, y: string, z: string.
      MayDependOn x y /\ MayDependOn y z <-> MayDependOn x z
  
  axiom MayDependOnInferenceI:
    forall w: string, y: string, x: string.
      assign w y x -> MayDependOn y x

  axiom MayDependOnInferenceII:
    forall w: string, y: string, x: string, t: string.
      assign w y x /\ MayDependOn x t -> MayDependOn y t

  axiom MayDependOnInferenceIII:
    forall w: string, y: string, x: string, t: string.
      op w y x /\ MayDependOn x t -> MayDependOn x t

  axiom MayDependOnInferenceIV:
    forall l: string, y: string, o: string, t: string.
      mload l y o /\ isConst o /\ MemTag l o t -> MayDependOn y t

  axiom MayDependOnInferenceV:
    forall w: string, l: string, y: string, o: string, t: string.
      mload l y o /\ not isConst o /\ MemTag l w t -> MayDependOn y t

  (* Static Analysis Unfinished *)
"

let functionalRet = "_r"

let yulFormalLib = "why_evm"

let yulUint64Formal = "Word"
let yulUint64FormalShort = "BV64"
let yulUint64FormalShortType = "int"

let yulUint64FormalTransFunc = yulUint64FormalShort ^ ".of_int"

let yulSemanticFormal = "Instructions"
let yulSemanticFormalShort = "Why3Inst" 

let yulStateFormal = "State"
let yulStateFormalShort = "Why3State"

let yulHelperFormal = "Helpers"
let yulHelperFormalShort = "Why3H"
let yulHelperW2B = "i2b"
let yulHelperB2W = "b2i"
let yulHelperConst0 = "bvconstzero"

let yulConstDeclaration = "let " ^ yulHelperConst0 ^ " = " ^ "0" ^ " in"

let inputFunc = "lp"
let outputFunc = "ur"

let yulStateInitial = "Why3State.state_init"
let yulStateType = "evmState"
let yulStateTypeUnit = "evmStateA unit"
let yulStateTypeWord = "evmStateA evmWord"
let yulStateCur = "st_c"
let yulStateFunctionGlobal = "st_g"
let fgDeref = "(! " ^ yulStateFunctionGlobal ^ ")"

let universalFirstArg = yulStateCur ^ ": " ^ yulStateType

let yulUint64FormalImport = 
  "use " ^ yulFormalLib ^ "." ^ yulUint64Formal ^ " as " ^ yulUint64FormalShort
let yulSemanticFormalImport = 
  "use " ^ yulFormalLib ^ "." ^ yulSemanticFormal ^ " as " ^ yulSemanticFormalShort
let yulStateFormalImport = 
  "use " ^ yulFormalLib ^ "." ^ yulStateFormal ^ " as " ^ yulStateFormalShort
let yulHelperFormalImport = 
  "use " ^ yulFormalLib ^ "." ^ yulHelperFormal ^ " as " ^ yulHelperFormalShort

(* use why_evm.Semantics as Sem
use why_evm.BVCheck64 as Bv64 *)

let contains s1 s2 =
  try
    let len = String.length s2 in
    for i = 0 to String.length s1 - len do
      if String.equal (String.sub s1 i len) s2 then raise Exit
    done;
    false
  with Exit -> true

let guessFuncType fn = 
  if contains fn "t_bool" then SolBool
  else if contains fn "t_uint" then SolUInt(64)
  else if contains fn "t_int" then SolInt(64)
  else SolUInt(64)

exception TranslationErr of string

let getFuncDetailByYulName tenv name = 
  let ret = List.fold_left (fun acc x -> 
    if (String.equal name x.yulAlias) then
      x
    else 
      acc
  ) (List.nth tenv.funcs 0) tenv.funcs in
  if String.equal ret.yulAlias name then ret
  else raise (TranslationErr ("No matching function for " ^ name))

let getSolTypeString st = 
  match st with
  | SolBool -> yulUint64FormalShortType (* "bool" *) (* temporary fix *)
  | SolUInt(n) -> if n == 64 then yulUint64FormalShortType else "uint" ^ string_of_int n
  | SolInt(n) -> "int" ^ string_of_int n

let cleanDoubleBreaks str =
  let r = Str.regexp "raise Ret[ \n\r\x0c\t]+raise Ret" in
      Str.global_replace r "raise Ret" str

let addRec str = 
  let r = Str.regexp "let function" in 
    Str.replace_first r "let rec function" str

(* control the translation features *)
let yulVersion = 
  "0.5.13"

let functionShortCut = [
  (* "transferFrom";
  "balanceOf"; *)
]

let isIdentF str = List.exists (fun x -> (contains str x)) yulIdentity

let evmStateMDefinition = 
"
module EVMState

	use list.List
	use why_evm.Word
  use why_evm.State
  use list.NthNoOpt as Nth
  use why_evm.State as Why3State
  use int.Int
  use bool.Bool

  type evmState = Why3State.t

  let evmStateInit = Why3State.init_state

  let function lp (s : evmState) (p : list int) : evmState
	= { s with cd = p }
	
	let ghost function ur (s : evmState) : int
  = Nth.nth 0 s.sk
  
  let ghost function getParam (s : evmState) (i : int) : int
    = let params = s.cd in
    Nth.nth i params
    
  let function setRet (s : evmState) (v : int) : evmState
    = { s with sk = Cons v Nil }
    
  let ghost function getRet (s : evmState) (i : int) : int
    = let params = s.cd in
    Nth.nth i params

  let ghost function runState (st: evmState) : int
  = 
  ur st

  let function i2b (i: int) : bool
  = if i = 0 then false else true

  let function b2i (b: bool) : int
  = if b then 1 else 0

end
"

(* 

module EVMStateM
  use why_evm.State as Why3State
  use int.Int
	use bool.Bool
  type evmState = Why3State.state_t
	
	(* actually, in EVM dialect, 'a can only be uint64 or unit *)
	type evmStateM 'a = evmState -> ('a, evmState)
	
	let function ret (v: 'a): evmStateM 'a
	=
	fun (st: evmState) -> (v, st)
	
	let function bind (m: evmStateM 'a) (f: 'a -> evmStateM 'b) : evmStateM 'b
	= 
	fun (st: evmState) -> 
	match m st with
	| (v, st') -> f v st'
	end
	
	let function execute (m: evmStateM 'a) : 'a
	=
	match m Why3State.init_state with
	| (v, st') -> v
	end
	
	let function word2bool (w: int) : bool
	=
	if w = 0 then false else true
end

module EVMState
  use why_evm.State as Why3State
  use int.Int
  use bool.Bool
  use why_evm.Word as BV64

  type evmWord = BV64.word

  type evmState = Why3State.state_t

  type evmStateA 'a = (evmState, 'a)

  let evmStateInit = Why3State.init_state

  let function runState (st: evmStateA evmWord) : int
  =
  match st with
  | (st', v) -> BV64.to_int v
  end

  let function copyState (st: evmStateA 'a) (v: 'b): evmStateA 'b
  =
  match st with
  | (st', v') -> (st', v)
  end

  let function b2w (b: bool): evmWord
  = 
  if b then BV64.of_int 1 else BV64.of_int 0

  let function w2b (w: evmWord): bool
  = 
  if BV64.to_int w = 0 then false else true

  let function w2i (w: evmWord): int
  =
  BV64.to_int w
end

*)


(* 

Axiom storage_reduce : forall st st' i v, 
  st' = update_storage_value_offset_0t_uint256 st i v 
  -> v = ur (read_from_storage_offset_0_t_uint256 st' i).


Axiom storage_reduce : forall st i v, 
  ur (read_from_storage_offset_0_t_uint256
    (update_storage_value_offset_0t_uint256 st i v) i)
  = v.

predicate memoryAbs evmState int int

axiom storage_reduce : forall st: evmState, i: int, v: int.
  v = ur (read_from_storage_offset_0_t_uint256 (update_storage_value_offset_0t_uint256 st i v) i)

(* How the state of the system changes in a single method call. *)
Inductive mstep : state -> state -> Prop :=
| mstep_call : forall p st retval st' rst,
    runStateT ((strategies p prev_contract_state state rst
                            (fun w hv => lif p w (BlindAuction_bid_opt hv))
                            (fun w v hv => lif p w (BlindAuction_reveal_opt v hv))
                            (fun w => lif  p w BlindAuction_withdraw_opt)
                            (fun w => lif p w BlindAuction_auctionEnd_opt))
                        : osT state unit) st
    = Some (retval, st') ->
    mstep st st'.

Inductive multi_mstep : state -> state -> Prop := 
| multi_mstep_reflexive : forall (st : state), multi_mstep st st
| multi_mstep_transitive : forall (st st' st'' : state), 
  mstep st st' -> multi_mstep st' st'' -> multi_mstep st st''.
(* | multi_mstep_synchronicity : forall (stg : strategy) (s s' a a': state),
  multi_mstep s a /\ mstep a a' /\ multi_mstep a' s'. *)

Inductive mstep =
| call: forall (st: evmState) (f: evmState -> evmState) , f st = st' -> mstep st st'

inductive storate_mstep =
  ｜ refl: forall st, storate_mstep st st
  ｜ trns: forall st st' st'', 

axiom storage_reduce2 : forall st: evmState, st': evmState, st'': evmState, i: int, v: int.
  st' = (update_storage_value_offset_0t_uint256 st i v) ->
  multi_mstep st' st'' -> 
  v = ur (read_from_storage_offset_0_t_uint256 st' i)
  
axiom storage_update : forall st: evmState, st': evmState, i: int, v: int.
  st' = (update_storage_value_offset_0t_uint256 st i v) ->
  memoryAbs st' i v

axiom storage_read : forall st: evmState, i: int, v: int.
  memoryAbs st i v ->
  v = ur (read_from_storage_offset_0_t_uint256 st i)


*)


(* 

function update_storage_value_offset_0t_uint256(slot, value) {
    tp1:=sload(slot)
    tp2:=prepare_store_t_uint256(value)
    tp:=update_byte_slice_32_shift_0(tp1, tp2)
    sstore(slot, tp)
}

function update_byte_slice_32_shift_0(value, toInsert) -> result {
    let mask := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
    toInsert := shift_left_0(toInsert)
    tp:=not(mask)
    value := and(value, tp)
    tp:=and(toInsert, mask)
    result := or(value, tp)
}

function extract_from_storage_value_offset_0t_uint256(slot_value) -> value {
    tp:=shift_right_0_unsigned(slot_value)
    value := cleanup_from_storage_t_uint256(tp)
}


function read_from_storage_offset_0_t_uint256(slot) -> value {
    tp:=sload(slot)
    value := extract_from_storage_value_offset_0t_uint256(tp)
}


*)