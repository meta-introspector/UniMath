open Ast
open BasicAst
open Byte
open Datatypes
open Kernames
open Lists
open Preamble
open Universes
open Bytestring

type 'x string_list = 'x list

type string = coq_UU

type coq_MyUU = coq_UU

type ast_desc =
| Adxu
| Ad_Ad_arg_label_expression_list_Da
| Ad_Ad_attributes_Da
| Ad_Ad_bool_Da
| Ad_Ad_empty_list_Da
| Ad_Ad_int_Da
| Ad_Ad_list
| Ad_Ad_loc2_Da
| Ad_Ad_loc_Da
| Ad_Ad_loc_stack_Da
| Ad_Ad_pos_Da
| Ad_Ad_process_arg_constructor_declaration_Da
| Ad_Ad_process_arg_label_expression_Da
| Ad_Ad_process_arg_label_expression_list_Da
| Ad_Ad_process_ast_desc
| Ad_Ad_process_cases
| Ad_Ad_process_cstrs_Da
| Ad_Ad_process_generic_list_Da
| Ad_Ad_process_label_declaration_list_Da
| Ad_Ad_process_list_tail_Da
| Ad_Ad_process_loc_Da
| Ad_Ad_process_params_Da
| Ad_Ad_process_string_loc_list_pattern_option_Da
| Ad_Ad_process_structure_item_Da
| Ad_Ad_process_structure_item_desc_Da
| Ad_Ad_process_structure_items_Da
| Ad_Ad_process_type_declaration_list_Da
| Ad_Ad_process_value_binding_list_Da
| Ad_Ad_process_var_list_Da
| Ad_Ad_quote_Da
| Ad_Definition
| Ad_FIXME
| Ad_FIXME_process_ast_desc
| Ad_Fixme1
| Ad_Fixme2_Da
| Ad_Ident of ast_desc
| Ad_MetaCoq_Definition
| Ad_NEW
| Ad_NoString
| Ad_Nolabel_Da
| Ad_None
| Ad_Nonrecursive_Da
| Ad_Obj
| Ad_P4
| Ad_Pconst_string_Da
| Ad_Pexp_apply_Da
| Ad_Pexp_constant_Da
| Ad_Pexp_constraint_Da
| Ad_Pexp_construct_Da
| Ad_Pexp_fun_Da
| Ad_Pexp_ident_Da
| Ad_Pexp_tuple_Da
| Ad_Ppat_constraint_Da
| Ad_Ppat_var_Da
| Ad_Pstr_type_Da
| Ad_Pstr_value_Da
| Ad_Ptyp_constr_Da
| Ad_Ptype_abstract_Da
| Ad_Public_Da
| Ad_Recursive_Da
| Ad_String of ast_desc
| Ad_TRUNCATED
| Ad_TypeParam_T
| Ad_TypeParam_T_dot
| Ad_Type_UUU
| Ad_Da_Da
| Ad_Da_Da_Da
| Ad_
| Ad_Da
| Ad_a_Da
| Ad_arg_label_Da
| Ad_arg_label_expression_list of ast_desc
| Ad_ast_desc
| Ad_ast_desc_Da
| Ad_attributes
| Ad_b_Da
| Ad_bool of ast_desc
| Ad_c_Da
| Ad_caret
| Ad_close_parens
| Ad_close_parens_Da_Da
| Ad_closebrace
| Ad_constant_Da
| Ad_core_type_desc_Da
| Ad_empty
| Ad_empty_array
| Ad_error
| Ad_errr
| Ad_expression_desc_Da
| Ad_fixme of ast_desc
| Ad_foo1_Da
| Ad_ident_Da
| Ad_int of ast_desc
| Ad_list of ast_desc
| Ad_list_Da
| Ad_loc
| Ad_loc2
| Ad_loc2_Da
| Ad_loc_Da
| Ad_loc_stack
| Ad_loc_stack_Da
| Ad_none_Da
| Ad_open_parenAd_Ident
| Ad_open_parenAd_String
| Ad_open_paren_rec_root
| Ad_openbrace
| Ad_pattern_desc_Da
| Ad_pos
| Ad_private_flag_Da
| Ad_process_arg_constructor_declaration of ast_desc
| Ad_process_arg_constructor_declaration_Da
| Ad_process_arg_label_expression of ast_desc * ast_desc
| Ad_process_arg_label_expression_Da
| Ad_process_arg_label_expression_list of ast_desc
| Ad_process_ast_desc of ast_desc
| Ad_process_ast_desc_loc_list_pattern_option
| Ad_process_cases of ast_desc
| Ad_process_core_type_list_Da
| Ad_process_cstrs of ast_desc
| Ad_process_cstrs_Da
| Ad_process_expression_list_Da
| Ad_process_generic_list of ast_desc * ast_desc
| Ad_process_generic_type
| Ad_process_generic_type3
| Ad_process_generic_type_Da
| Ad_process_label_declaration_list of ast_desc
| Ad_process_label_declaration_list_Da
| Ad_process_list_tail of ast_desc * ast_desc
| Ad_process_loc of ast_desc
| Ad_process_loc_Da
| Ad_process_params of ast_desc
| Ad_process_params_Da
| Ad_process_string
| Ad_process_string_loc_list_pattern_option
| Ad_process_string_loc_list_pattern_option_Da
| Ad_process_structure_item of ast_desc
| Ad_process_structure_item_desc of ast_desc
| Ad_process_structure_items of ast_desc
| Ad_process_structure_items_Da
| Ad_process_type_declaration_list of ast_desc
| Ad_process_type_declaration_list_Da
| Ad_process_value_binding_list
| Ad_process_var_list of ast_desc
| Ad_process_vars_list_Da
| Ad_quot_list of ast_desc
| Ad_quote of ast_desc * ast_desc
| Ad_rec_flag_Da
| Ad_root of ast_desc
| Ad_string_Da
| Ad_structure_item_desc_Da
| Ad_todofixme
| Ad_type_kind_Da
| Ad_umcr_n_role_
| Ad_umcr_n_type_
| Ad_umcr_r_rel_
| Ad_umcr_type
| Ad_x_Da
| Ad_y_Da
| Coq_ad_nostring

val ast_desc_rect :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) ->
  'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> (ast_desc -> 'a1 -> 'a1) -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> (ast_desc ->
  'a1 -> ast_desc -> 'a1 -> 'a1) -> 'a1 -> (ast_desc -> 'a1 -> 'a1) ->
  (ast_desc -> 'a1 -> 'a1) -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 ->
  (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> ast_desc ->
  'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 ->
  (ast_desc -> 'a1 -> ast_desc -> 'a1 -> 'a1) -> (ast_desc -> 'a1 -> 'a1) ->
  'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (ast_desc ->
  'a1 -> 'a1) -> (ast_desc -> 'a1 -> 'a1) -> (ast_desc -> 'a1 -> 'a1) -> 'a1
  -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) ->
  'a1 -> (ast_desc -> 'a1 -> 'a1) -> (ast_desc -> 'a1 -> ast_desc -> 'a1 ->
  'a1) -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> ast_desc -> 'a1

val ast_desc_rec :
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) ->
  'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> (ast_desc -> 'a1 -> 'a1) -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
  'a1 -> 'a1 -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> (ast_desc ->
  'a1 -> ast_desc -> 'a1 -> 'a1) -> 'a1 -> (ast_desc -> 'a1 -> 'a1) ->
  (ast_desc -> 'a1 -> 'a1) -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 ->
  (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> ast_desc ->
  'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 ->
  (ast_desc -> 'a1 -> ast_desc -> 'a1 -> 'a1) -> (ast_desc -> 'a1 -> 'a1) ->
  'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> (ast_desc ->
  'a1 -> 'a1) -> (ast_desc -> 'a1 -> 'a1) -> (ast_desc -> 'a1 -> 'a1) -> 'a1
  -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) ->
  'a1 -> (ast_desc -> 'a1 -> 'a1) -> (ast_desc -> 'a1 -> ast_desc -> 'a1 ->
  'a1) -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1
  -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> ast_desc -> 'a1

type ast_desc_list =
| Ad_empty_list
| Ad_cons of ast_desc * ast_desc_list

val ast_desc_list_rect :
  'a1 -> (ast_desc -> ast_desc_list -> 'a1 -> 'a1) -> ast_desc_list -> 'a1

val ast_desc_list_rec :
  'a1 -> (ast_desc -> ast_desc_list -> 'a1 -> 'a1) -> ast_desc_list -> 'a1

val ident : ast_desc -> ast_desc

val none : ast_desc

val process_cases : ast_desc -> ast_desc

val process_var_list : ast_desc -> ast_desc

val process_arg_constructor_declaration : ast_desc -> ast_desc

val process_label_declaration_list : ast_desc -> ast_desc

val process_params : ast_desc -> ast_desc

val process_cstrs : ast_desc -> ast_desc

val process_type_declaration_list : ast_desc -> ast_desc

val loc : ast_desc

val loc2 : ast_desc

val loc_stack : ast_desc

val process_loc : ast_desc -> ast_desc

val process_string_loc_list_pattern_option : ast_desc

val process_arg_label_expression : ast_desc -> ast_desc -> ast_desc

val process_expression_list : ast_desc -> ast_desc

val process_arg_label_expression_list : ast_desc -> ast_desc

val process_location : ast_desc -> ast_desc

val process_location_stack : ast_desc -> ast_desc

val attributes : ast_desc

val process_value_binding_list : ast_desc

val pos : ast_desc -> ast_desc

val b_value : ast_desc -> ast_desc

val mint : ast_desc -> ast_desc

val string_value : ast_desc -> ast_desc

val make_pair : ast_desc -> ast_desc -> ast_desc

val process_string_option : ast_desc

val process_structure_items : ast_desc -> ast_desc

val my_append : ast_desc -> ast_desc -> ast_desc

val process_generic_type3 : ast_desc -> ast_desc -> ast_desc -> ast_desc

val quot : ast_desc -> ast_desc -> ast_desc

val ad_list : ast_desc_list -> ast_desc

val quot_list :
  ast_desc -> (ast_desc -> ast_desc) -> ast_desc_list -> ast_desc

val process_ast_desc : ast_desc -> ast_desc

val process_simple_ast_root : ast_desc -> ast_desc

val process_string : ast_desc -> ast_desc

val process_int : ast_desc -> ast_desc

val process_bool : ast_desc -> ast_desc

val process_generic_list :
  ast_desc -> ast_desc_list -> (ast_desc -> ast_desc) -> ast_desc

val print_endline : ast_desc -> coq_unit

val def_basic : ast_desc -> ast_desc -> ast_desc

val def_pair : ast_desc -> ast_desc -> ast_desc -> ast_desc -> ast_desc

val process_generic_type2 : ast_desc -> ast_desc -> 'a1 -> ast_desc

val not_empty : ast_desc_list -> bool

val ast_dest_list_to_single : ast_desc_list -> ast_desc

val process_ast_desc3 : ast_desc_list -> ast_desc

val process_ast_desc4 : ast_desc -> ast_desc

val process_ast_desc2 : ast_desc_list -> ast_desc

val process_root_list : ast_desc -> ast_desc

val tostring : ast_desc -> ast_desc

val ast_desc_to_yojson : ast_desc -> ast_desc

val process_generic_type_print : ast_desc -> ast_desc -> ast_desc -> coq_unit

val process_generic_type : ast_desc -> ast_desc -> ast_desc -> ast_desc

val process_structure_item : ast_desc -> ast_desc

val process_structure_item_desc : ast_desc -> ast_desc

val extract_root : ast_desc -> ast_desc

val ff1 : ast_desc

val ff0 : ast_desc

val ff00 : ast_desc

val ff000 : ast_desc

val ff2 : ast_desc

val foo1 : ast_desc

val ref_air : Env.program

val reifMyUU : Env.program
