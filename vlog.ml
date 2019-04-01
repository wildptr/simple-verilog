type typ =
  | T_array of (int * int) list
  | T_vector of int * int * bool (* msb, lsb, signed *)
  | T_bit

type obj = {
  o_name : string;
  o_kind : obj_kind;
  o_type : typ
}
