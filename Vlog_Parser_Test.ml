let () =
  let lexbuf = Lexing.from_channel stdin in
  let mod_ = Vlog_Parser.top Vlog_Lexer.token lexbuf in
  Format.printf "%a@." Vlog_AST.pp_module mod_
