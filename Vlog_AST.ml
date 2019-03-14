open ExtLib

type signal_type =
  | Wire
  | Reg
  | Localparam
  | Parameter

let pp_signal_type f sig_ =
  let open Format in
  match sig_ with
  | Wire -> fprintf f "wire"
  | Reg -> fprintf f "reg"
  | Localparam -> fprintf f "localparam"
  | Parameter -> fprintf f "parameter"

type sensitivity =
  | Sens_auto
  | Sens_posedge of string
  | Sens_negedge of string

let pp_sensitivity f sens =
  let open Format in
  match sens with
  | Sens_auto -> fprintf f "*"
  | Sens_posedge s -> fprintf f "(posedge %s)" s
  | Sens_negedge s -> fprintf f "(negedge %s)" s

type case_variant =
  | Case
  | Casex
  | Casez

let pp_case_variant f case =
  let open Format in
  match case with
  | Case -> fprintf f "case"
  | Casex -> fprintf f "casex"
  | Casez -> fprintf f "casez"

module Literal : sig
  type t
  val make_unsized : int -> t
  val make_simple : int -> int -> t
  val make : int -> int * int -> t
  val to_string : t -> string
  val to_int : t -> int
  val width : t -> int option
  val pp : Format.formatter -> t -> unit
  val bit_select : t -> int -> t
  val part_select : t -> int * int -> t
  val of_int : int -> t
end = struct
  type t = int option * (int * int)

  let make_unsized value =
    None, (value, 0)

  let of_int = make_unsized

  let make_simple width value =
    Some width, (value, 0)

  let make width value =
    Some width, value

  let min_width x =
    let rec f x' acc =
      if x' = 0 then acc else f (x' lsr 1) (acc+1)
    in
    f x 0

  let to_string lit =
    let width_opt, (a, b) = lit in
    if b = 0
    then match width_opt with
    | None -> string_of_int a
    | Some width -> Printf.sprintf "%d'd%d" width a
    else
      let rec f i =
        if i = 0
        then []
        else
          let mask = 1 lsl i in
          let c =
            match a land mask <> 0, b land mask <> 0 with
            | false, false -> '0'
            | true , false -> '1'
            | false, true  -> 'z'
            | true , true  -> 'x'
          in
          c :: f (i-1)
      in
      let width = Option.default (min_width (a lor b)) width_opt in
      let value_s = String.of_seq (List.to_seq (f width)) in
      match width_opt with
      | None -> value_s
      | Some width -> Printf.sprintf "%d'b%s" width value_s

  let to_int lit =
    let _, (a, _) = lit in a

  let width = fst

  let pp f lit =
    Format.fprintf f "%s" (to_string lit)

  let part_select lit (lo, hi) =
    let width_opt, (a, b) = lit in
    let mask = (1 lsl (hi-lo)) - 1 in
    let a' = a lsr lo land mask in
    let b' = b lsr lo land mask in
    let width_opt' =
      match width_opt with
      | None -> None
      | Some _ -> Some (hi-lo)
    in
    width_opt', (a', b')

  let bit_select lit i =
    part_select lit (i, i+1)

end

(* Binary operators are listed in precedence order, from high to low.
 * Operators with same precedence are listed on the same line. *)
type binary_op =
  | B_mul
  | B_add | B_sub
  | B_shiftL | B_shiftR
  | B_lt | B_ge | B_gt | B_le
  | B_eq | B_neq
  | B_and
  | B_or
  | B_xor

(* let prec_of_binary_op = function
  | B_mul -> 0
  | B_add | B_sub -> 1
  | B_shiftL | B_shiftR -> 2
  | B_lt | B_ge | B_gt | B_le -> 3
  | B_eq | B_neq -> 4
  | B_and -> 5
  | B_or -> 6
  | B_xor -> 7 *)

let string_of_binary_op = function
  | B_mul -> "*"
  | B_add -> "+"
  | B_sub -> "-"
  | B_shiftL -> "<<"
  | B_shiftR -> ">>"
  | B_lt -> "<"
  | B_ge -> ">="
  | B_gt -> ">"
  | B_le -> "<="
  | B_eq -> "=="
  | B_neq -> "!="
  | B_and -> "&"
  | B_or -> "|"
  | B_xor -> "^"

type unary_op =
  | U_not
  | U_reduce_and
  | U_reduce_or

let string_of_unary_op = function
  | U_not -> "~"
  | U_reduce_and -> "&"
  | U_reduce_or -> "|"

type expr =
  | E_select of string * index list
  | E_literal of Literal.t
  | E_cond of expr * expr * expr
  | E_binary of binary_op * expr * expr
  | E_unary of unary_op * expr
  | E_concat of expr list
  | E_duplicate of expr * expr

and index =
  | Bit of expr
  | Part_const of expr * expr
  | Part_var of expr * expr

let rec pp_expr f expr =
  let open Format in
  match expr with
  | E_select (name, indices) ->
      fprintf f "%s" name;
      List.iter (pp_index f) indices
  | E_literal lit -> Literal.pp f lit
  | E_cond (e_cond, e_true, e_false) ->
      fprintf f "(%a ? %a : %a)"
        pp_expr e_cond pp_expr e_true pp_expr e_false
  | E_binary (op, e1, e2) ->
      fprintf f "(%a %s %a)"
        pp_expr e1 (string_of_binary_op op) pp_expr e2
  | E_unary (op, e) ->
      fprintf f "(%s%a)" (string_of_unary_op op) pp_expr e
  | E_concat es ->
      fprintf f "{";
      let n = List.length es in
      es |> List.iteri begin fun i e ->
        pp_expr f e;
        if i < n-1 then fprintf f ","
      end;
      fprintf f "}"
  | E_duplicate (e_n, e_data) ->
      fprintf f "{%a{%a}}" pp_expr e_n pp_expr e_data

and pp_index f index =
  let open Format in
  match index with
  | Bit e ->
      fprintf f "[%a]" pp_expr e
  | Part_const (e_msb, e_lsb) ->
      fprintf f "[%a:%a]" pp_expr e_msb pp_expr e_lsb
  | Part_var (e_base, e_width) ->
      fprintf f "[%a+:%a]" pp_expr e_base pp_expr e_width

type assign = expr * expr

type proc =
  | P_blocking_assign of assign
  | P_nonblocking_assign of assign
  | P_comp of proc list
  | P_if of expr * proc * proc option
  | P_case of case_variant * expr * (expr option * proc) list

let rec pp_proc ind f proc =
  let open Format in
  match proc with
  | P_blocking_assign (lhs, rhs) ->
      fprintf f "%s%a = %a;\n" ind pp_expr lhs pp_expr rhs
  | P_nonblocking_assign (lhs, rhs) ->
      fprintf f "%s%a <= %a;\n" ind pp_expr lhs pp_expr rhs
  | P_comp procs ->
      fprintf f "%sbegin\n" ind;
      List.iter (pp_proc (ind^"  ") f) procs;
      fprintf f "%send\n" ind
  | P_if (e_cond, p_true, p_false_opt) ->
    let ind' = ind ^ "  " in
    fprintf f "%sif (%a)\n%a" ind pp_expr e_cond (pp_proc ind') p_true;
      begin match p_false_opt with
      | None -> ()
      | Some p_false ->
          fprintf f "%selse\n%a" ind (pp_proc ind') p_false
      end
  | P_case (variant, e_disc, branches) ->
    let ind' = ind ^ "  " in
    fprintf f "%s%a (%a)\n" ind pp_case_variant variant pp_expr e_disc;
    branches |> List.iter begin fun (label_expr_opt, proc) ->
      begin match label_expr_opt with
        | None -> fprintf f "%sdefault:\n" ind
        | Some label_expr -> fprintf f "%s%a:\n" ind pp_expr label_expr
      end;
      pp_proc ind' f proc
    end;
    fprintf f "%sendcase\n" ind

type signal_declarator = string * (expr * expr) list * expr option

let pp_signal_declarator f (name, dims, eq_expr_opt) =
  let open Format in
  fprintf f "%s" name;
  dims |> List.iter begin fun (e1, e2) ->
    fprintf f "[%a:%a]" pp_expr e1 pp_expr e2
  end;
  match eq_expr_opt with
  | None -> ()
  | Some eq_expr -> fprintf f " = %a" pp_expr eq_expr

type signal_decl = {
  sig_type : signal_type;
  sig_range_opt : (expr * expr) option;
  sig_declarators : signal_declarator list;
}

type port_direction = Input | Output | Inout

let string_of_port_direction = function
  | Input -> "input"
  | Output -> "output"
  | Inout -> "inout"

type port_decl = {
  port_dir : port_direction;
  port_is_reg : bool;
  port_range_opt : (expr * expr) option;
  port_declarators : signal_declarator list;
}

let pp_range f (msb, lsb) =
  Format.fprintf f "[%a:%a]" pp_expr msb pp_expr lsb

let pp_port_decl f port =
  let open Format in
  fprintf f "%s%s"
    (string_of_port_direction port.port_dir)
    (if port.port_is_reg then " reg" else "");
  begin match port.port_range_opt with
  | None -> ()
  | Some range -> fprintf f " %a" pp_range range
  end;
  fprintf f " ";
  let n = List.length port.port_declarators in
  port.port_declarators |> List.iteri begin fun i declr ->
    pp_signal_declarator f declr;
    if i < n-1 then fprintf f ", "
  end

let pp_signal_decl f sigdecl =
  let open Format in
  fprintf f "%a" pp_signal_type sigdecl.sig_type;
  begin match sigdecl.sig_range_opt with
  | None -> ()
  | Some range -> fprintf f " %a" pp_range range
  end;
  fprintf f " ";
  let n = List.length sigdecl.sig_declarators in
  sigdecl.sig_declarators |> List.iteri begin fun i declr ->
    pp_signal_declarator f declr;
    if i < n-1 then fprintf f ", "
  end

type instance = {
  inst_class_name : string;
  inst_inst_name : string;
  inst_connections : (string * expr option) list;
}

let pp_instance f inst =
  let open Format in
  fprintf f "%s %s(" inst.inst_class_name inst.inst_inst_name;
  let n = List.length inst.inst_connections in
  inst.inst_connections |> List.iteri begin fun i (name, expr_opt) ->
    pp_print_string f "\n  ";
    begin match expr_opt with
      | None -> fprintf f ".%s()" name
      | Some expr -> fprintf f ".%s(%a)" name pp_expr expr
    end;
    if i < n-1 then fprintf f ","
  end;
  fprintf f "\n);\n"

type always_block = sensitivity * proc

let pp_always_block f (sens, proc) =
  Format.fprintf f "always @@%a\n%a" pp_sensitivity sens (pp_proc "  ") proc

type decl =
  | Decl_signal of signal_decl
  | Decl_assign of assign
  | Decl_instance of instance
  | Decl_always of always_block

let pp_decl f = function
  | Decl_signal sigdecl -> Format.fprintf f "%a;\n" pp_signal_decl sigdecl
  | Decl_assign (lhs, rhs) ->
      Format.fprintf f "assign %a = %a;\n" pp_expr lhs pp_expr rhs
  | Decl_instance inst -> pp_instance f inst
  | Decl_always always -> pp_always_block f always

type module_ = {
  mod_name : string;
  mod_params : signal_decl list;
  mod_ports : port_decl list;
  mod_decls : decl list;
}

let pp_module f m =
  let open Format in
  fprintf f "module %s" m.mod_name;
(*if m.mod_params <> [] then begin
    fprintf f "#(";
    let n = List.length m.mod_params in
    m.mod_params |> List.iteri (fun i sigdecl ->
      pp_signal_decl f sigdecl;
      if i < n-1 then fprintf f ", ");
    fprintf f ");";
  end;*)
  fprintf f "(";
  let n = List.length m.mod_ports in
  m.mod_ports |> List.iteri (fun i port_decl ->
    fprintf f "\n  %a" pp_port_decl port_decl;
    if i < n-1 then fprintf f ",");
  fprintf f "\n);\n";
  List.iter (pp_decl f) m.mod_decls;
  fprintf f "endmodule"