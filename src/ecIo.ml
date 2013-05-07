(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
let lexbuf_from_channel = fun name channel ->
  let lexbuf = Lexing.from_channel channel in
    lexbuf.Lexing.lex_curr_p <- {
        Lexing.pos_fname = name;
        Lexing.pos_lnum  = 1;
        Lexing.pos_bol   = 0;
        Lexing.pos_cnum  = 0
      };
    lexbuf

(* -------------------------------------------------------------------- *)
let parserfun = fun () ->
    MenhirLib.Convert.Simplified.traditional2revised EcParser.prog

type parser_t =
  (EcParser.token * Lexing.position * Lexing.position, EcParsetree.prog)
    MenhirLib.Convert.revised

(* -------------------------------------------------------------------- *)
type ecreader_r = {
  (*---*) ecr_lexbuf  : Lexing.lexbuf;
  (*---*) ecr_parser  : parser_t;
  mutable ecr_atstart : bool;
}

type ecreader = ecreader_r Disposable.t

(* -------------------------------------------------------------------- *)
let lexbuf (reader : ecreader) =
  (Disposable.get reader).ecr_lexbuf

(* -------------------------------------------------------------------- *)
let from_channel ~name channel =
  let lexbuf = lexbuf_from_channel name channel in

    Disposable.create
      { ecr_lexbuf  = lexbuf;
        ecr_parser  = parserfun ();
        ecr_atstart = true; }

(* -------------------------------------------------------------------- *)
let from_file filename =
  let channel = open_in filename in
    try
      let lexbuf = lexbuf_from_channel filename channel in

        Disposable.create ~cb:(fun _ -> close_in channel)
          { ecr_lexbuf  = lexbuf;
            ecr_parser  = parserfun ();
            ecr_atstart = true; }

    with
      | e ->
          (try close_in channel with _ -> ());
          raise e

(* -------------------------------------------------------------------- *)
let from_string data =
  let lexbuf = Lexing.from_string data in

    Disposable.create
      { ecr_lexbuf  = lexbuf;
        ecr_parser  = parserfun ();
        ecr_atstart = true; }

(* -------------------------------------------------------------------- *)
let finalize (ecreader : ecreader) =
  Disposable.dispose ecreader

(* -------------------------------------------------------------------- *)
let lexer = fun ecreader ->
  let lexbuf = ecreader.ecr_lexbuf in
  let token  = EcLexer.main lexbuf in
    ecreader.ecr_atstart <- (token = EcParser.FINAL);
    (token, Lexing.lexeme_start_p lexbuf, Lexing.lexeme_end_p lexbuf)

(* -------------------------------------------------------------------- *)
let drain (ecreader : ecreader) =
  let ecreader = Disposable.get ecreader in
  let rec drain () =
    match lexer ecreader with
    | (EcParser.FINAL, _, _) -> ()
    | _ -> drain ()
  in
    if not ecreader.ecr_atstart then
      drain ()

(* -------------------------------------------------------------------- *)
let parse (ecreader : ecreader) =
  let ecreader = Disposable.get ecreader in
    ecreader.ecr_parser (fun () -> lexer ecreader)

(* -------------------------------------------------------------------- *)
let parseall (ecreader : ecreader) =
  let rec aux acc =
    match parse ecreader with
    | EcParsetree.P_Prog (commands, terminate) ->
        let acc = List.rev_append commands acc in
          if terminate then List.rev acc else aux acc
    | EcParsetree.P_Undo _ ->
        assert false                    (* FIXME *)
  in
    aux []

(* -------------------------------------------------------------------- *)
let lex_single_token name =
  try
    let lexbuf = Lexing.from_string name in
    let token  = EcLexer.main lexbuf in
      match EcLexer.main lexbuf with
      | EcParser.EOF -> Some token
      | _ -> None

  with EcLexer.LexicalError _ -> None

(* -------------------------------------------------------------------- *)
let is_sym_ident x =
  match lex_single_token x with
  | Some (EcParser.LIDENT _) -> true
  | Some (EcParser.UIDENT _) -> true
  | _ -> false

let is_mem_ident x =
  match lex_single_token x with
  | Some (EcParser.MIDENT _) -> true
  | _ -> false

let is_mod_ident x =
  match lex_single_token x with
  | Some (EcParser.UIDENT _) -> true
  | _ -> false
