open Ts

type action = Ts
let string_of_action act =
  match act with
    Ts -> "Ts"
  | _ -> "None"

exception Option_not_implemented of string

let () =
  let action = ref Ts in
  let set_action a () = action := a in
  let speclist = [
    ("-a", Arg.Unit (set_action Ts), "Print the Ts");
  ] in
  let usage_msg = "usage: ./yulp.native [-a] [file.yulp]" in
  let channel = ref stdin in
  Arg.parse speclist (fun filename -> channel := open_in filename) usage_msg;

  let lexbuf = Lexing.from_channel !channel in
  let ts = Parser.program Scanner.token lexbuf in
    match !action with
      Ts -> print_string (Ts.ts_program ts)
    | _ -> raise (Option_not_implemented (string_of_action !action))
