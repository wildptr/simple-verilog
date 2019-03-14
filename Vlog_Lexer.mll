{
open Lexing
open Vlog_Parser

exception Error of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with
      pos_bol = pos.pos_cnum;
      pos_lnum = pos.pos_lnum + 1 }

module M = Map.Make(String)

let keyword_map =
  [
    "always", ALWAYS;
    "assign", ASSIGN;
    "begin", BEGIN;
    "case", CASE;
    "casex", CASEX;
    "casez", CASEZ;
    "default", DEFAULT;
    "else", ELSE;
    "end", END;
    "endcase", ENDCASE;
    "endmodule", ENDMODULE;
    "if", IF;
    "inout", INOUT;
    "input", INPUT;
    "localparam", LOCALPARAM;
    "module", MODULE;
    "negedge", NEGEDGE;
    "output", OUTPUT;
    "parameter", PARAMETER;
    "posedge", POSEDGE;
    "reg", REG;
    "wire", WIRE;
  ]
  |> List.to_seq |> M.of_seq

let convert_bin_literal s =
  let rec f i =
    if i = 0
    then (0, 0)
    else
      let a', b' = f (i-1) in
      let c = s.[i-1] in
      match c with
      | 'x' | 'X' ->
          a' lsl 1 lor 1, b' lsl 1 lor 1
      | 'z' | 'Z' | '?' ->
          a' lsl 1 lor 0, b' lsl 1 lor 1
      | '0' | '1' ->
          let d = int_of_char c - 0x30 in
          a' lsl 1 lor d, b' lsl 1 lor 0
      | _ -> assert false
  in
  let a, b = f (String.length s) in
  Literal (a, b)

let convert_oct_literal s =
  let rec f i =
    if i = 0
    then (0, 0)
    else
      let a', b' = f (i-1) in
      let c = s.[i-1] in
      match c with
      | 'x' | 'X' ->
          a' lsl 3 lor 7, b' lsl 3 lor 7
      | 'z' | 'Z' | '?' ->
          a' lsl 3 lor 0, b' lsl 3 lor 7
      | '0'..'7' ->
          let d = int_of_char c - 0x30 in
          a' lsl 3 lor d, b' lsl 3 lor 0
      | _ -> assert false
  in
  let a, b = f (String.length s) in
  Literal (a, b)

let hex_value c =
  let b = int_of_char c in
  if b > 0x40 then (b lor 32) - 87 else b-48

let convert_hex_literal s =
  let rec f i =
    if i = 0
    then (0, 0)
    else
      let a', b' = f (i-1) in
      let c = s.[i-1] in
      match c with
      | 'x' | 'X' ->
          a' lsl 4 lor 0xf, b' lsl 4 lor 0xf
      | 'z' | 'Z' | '?' ->
          a' lsl 4 lor 0, b' lsl 4 lor 0xf
      | '0'..'9' | 'A'..'F' | 'a'..'f' ->
          let d = hex_value c in
          a' lsl 4 lor d, b' lsl 4 lor 0
      | _ -> assert false
  in
  let a, b = f (String.length s) in
  Literal (a, b)

let convert_dec_literal s =
  let rec f i =
    if i = 0
    then 0
    else
      let a' = f (i-1) in
      let c = s.[i-1] in
      match c with
      | '0'..'9' ->
          a' * 10 + (int_of_char c - 0x30)
      | _ -> assert false
  in
  Literal (f (String.length s), 0)

}

(* numeric literals *)

let base_prefix = "'" ['s' 'S']?
let dec_base = base_prefix ['d' 'D']
let bin_base = base_prefix ['b' 'B']
let oct_base = base_prefix ['o' 'O']
let hex_base = base_prefix ['h' 'H']

let xz_digit = ['x' 'X' 'z' 'Z' '?']
let bin_digit = ['0' '1']
let bin_digit' = bin_digit | xz_digit
let oct_digit = ['0'-'7']
let oct_digit' = oct_digit | xz_digit
let hex_digit = ['0'-'9' 'a'-'f' 'A'-'F']
let hex_digit' = hex_digit | xz_digit

let dec_number = ['0'-'9'] ['0'-'9' '_']*
let bin_number' = bin_digit' (bin_digit'|'_')*
let oct_number' = oct_digit' (oct_digit'|'_')*
let hex_number' = hex_digit' (hex_digit'|'_')*

(* identifiers *)

let ident = ['a'-'z' 'A'-'Z' '_'] ['a'-'z' 'A'-'Z' '_' '0'-'9' '$']*

let white_char = [' ' '\t']
let white = white_char+
let single_line_comment = "//" [^'\n']* '\n'

rule token = parse
  | white { token lexbuf }
  | single_line_comment { next_line lexbuf; token lexbuf }
  | "/*" { comment lexbuf }
  | '\n' { next_line lexbuf; token lexbuf }
  | dec_base white_char* (dec_number as value)
    { convert_dec_literal value }
  | bin_base white_char* (bin_number' as value)
    { convert_bin_literal value }
  | oct_base white_char* (oct_number' as value)
    { convert_oct_literal value }
  | hex_base white_char* (hex_number' as value)
    { convert_hex_literal value }
  | ident as s
    { match M.find_opt s keyword_map with Some k -> k | None -> Ident s }
  | dec_number as s { Int (int_of_string s) }
  | "!=" { BangEq }
  | "+:" { PlusColon }
  | "<<" { LtLt }
  | "<=" { LtEq }
  | "==" { EqEq }
  | ">=" { GtEq }
  | ">>" { GtGt }
  | '!' { Bang }
  | '#' { Hash }
  | '&' { Amp }
  | '(' { LParen }
  | ')' { RParen }
  | '*' { Star }
  | '+' { Plus }
  | ',' { Comma }
  | '-' { Minus }
  | '.' { Dot }
  | ':' { Colon }
  | ';' { Semi }
  | '<' { Lt }
  | '=' { Eq }
  | '>' { Gt }
  | '?' { Quest }
  | '@' { At }
  | '[' { LBrack }
  | ']' { RBrack }
  | '^' { Caret }
  | '{' { LBrace }
  | '|' { Bar }
  | '}' { RBrace }
  | '~' { Tilde }
  | eof { EOF }
  | _ as c { raise (Error (Printf.sprintf "unexpected character: %c" c)) }

and comment = parse
  | "*/" { token lexbuf }
  | '\n' { next_line lexbuf; comment lexbuf }
  | _ { comment lexbuf }
