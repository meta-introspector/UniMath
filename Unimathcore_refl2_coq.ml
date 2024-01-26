open Lists
open Preamble

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
| Ad__Da_Da
| Ad__Da_Da_Da
| Ad___
| Ad____Da
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

(** val ast_desc_rect :
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
    'a1 -> 'a1 -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> (ast_desc
    -> 'a1 -> ast_desc -> 'a1 -> 'a1) -> 'a1 -> (ast_desc -> 'a1 -> 'a1) ->
    (ast_desc -> 'a1 -> 'a1) -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 ->
    (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> ast_desc ->
    'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 ->
    (ast_desc -> 'a1 -> ast_desc -> 'a1 -> 'a1) -> (ast_desc -> 'a1 -> 'a1)
    -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    (ast_desc -> 'a1 -> 'a1) -> (ast_desc -> 'a1 -> 'a1) -> (ast_desc -> 'a1
    -> 'a1) -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> (ast_desc ->
    'a1 -> 'a1) -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> (ast_desc -> 'a1 ->
    ast_desc -> 'a1 -> 'a1) -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    ast_desc -> 'a1 **)

let rec ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 = function
| Adxu -> f
| Ad_Ad_arg_label_expression_list_Da -> f0
| Ad_Ad_attributes_Da -> f1
| Ad_Ad_bool_Da -> f2
| Ad_Ad_empty_list_Da -> f3
| Ad_Ad_int_Da -> f4
| Ad_Ad_list -> f5
| Ad_Ad_loc2_Da -> f6
| Ad_Ad_loc_Da -> f7
| Ad_Ad_loc_stack_Da -> f8
| Ad_Ad_pos_Da -> f9
| Ad_Ad_process_arg_constructor_declaration_Da -> f10
| Ad_Ad_process_arg_label_expression_Da -> f11
| Ad_Ad_process_arg_label_expression_list_Da -> f12
| Ad_Ad_process_ast_desc -> f13
| Ad_Ad_process_cases -> f14
| Ad_Ad_process_cstrs_Da -> f15
| Ad_Ad_process_generic_list_Da -> f16
| Ad_Ad_process_label_declaration_list_Da -> f17
| Ad_Ad_process_list_tail_Da -> f18
| Ad_Ad_process_loc_Da -> f19
| Ad_Ad_process_params_Da -> f20
| Ad_Ad_process_string_loc_list_pattern_option_Da -> f21
| Ad_Ad_process_structure_item_Da -> f22
| Ad_Ad_process_structure_item_desc_Da -> f23
| Ad_Ad_process_structure_items_Da -> f24
| Ad_Ad_process_type_declaration_list_Da -> f25
| Ad_Ad_process_value_binding_list_Da -> f26
| Ad_Ad_process_var_list_Da -> f27
| Ad_Ad_quote_Da -> f28
| Ad_Definition -> f29
| Ad_FIXME -> f30
| Ad_FIXME_process_ast_desc -> f31
| Ad_Fixme1 -> f32
| Ad_Fixme2_Da -> f33
| Ad_Ident a0 ->
  f34 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_MetaCoq_Definition -> f35
| Ad_NEW -> f36
| Ad_NoString -> f37
| Ad_Nolabel_Da -> f38
| Ad_None -> f39
| Ad_Nonrecursive_Da -> f40
| Ad_Obj -> f41
| Ad_P4 -> f42
| Ad_Pconst_string_Da -> f43
| Ad_Pexp_apply_Da -> f44
| Ad_Pexp_constant_Da -> f45
| Ad_Pexp_constraint_Da -> f46
| Ad_Pexp_construct_Da -> f47
| Ad_Pexp_fun_Da -> f48
| Ad_Pexp_ident_Da -> f49
| Ad_Pexp_tuple_Da -> f50
| Ad_Ppat_constraint_Da -> f51
| Ad_Ppat_var_Da -> f52
| Ad_Pstr_type_Da -> f53
| Ad_Pstr_value_Da -> f54
| Ad_Ptyp_constr_Da -> f55
| Ad_Ptype_abstract_Da -> f56
| Ad_Public_Da -> f57
| Ad_Recursive_Da -> f58
| Ad_String a0 ->
  f59 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_TRUNCATED -> f60
| Ad_TypeParam_T -> f61
| Ad_TypeParam_T_dot -> f62
| Ad_Type_UUU -> f63
| Ad__Da_Da -> f64
| Ad__Da_Da_Da -> f65
| Ad___ -> f66
| Ad____Da -> f67
| Ad_a_Da -> f68
| Ad_arg_label_Da -> f69
| Ad_arg_label_expression_list a0 ->
  f70 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_ast_desc -> f71
| Ad_ast_desc_Da -> f72
| Ad_attributes -> f73
| Ad_b_Da -> f74
| Ad_bool a0 ->
  f75 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_c_Da -> f76
| Ad_caret -> f77
| Ad_close_parens -> f78
| Ad_close_parens_Da_Da -> f79
| Ad_closebrace -> f80
| Ad_constant_Da -> f81
| Ad_core_type_desc_Da -> f82
| Ad_empty -> f83
| Ad_empty_array -> f84
| Ad_error -> f85
| Ad_errr -> f86
| Ad_expression_desc_Da -> f87
| Ad_fixme a0 ->
  f88 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_foo1_Da -> f89
| Ad_ident_Da -> f90
| Ad_int a0 ->
  f91 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_list a0 ->
  f92 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_list_Da -> f93
| Ad_loc -> f94
| Ad_loc2 -> f95
| Ad_loc2_Da -> f96
| Ad_loc_Da -> f97
| Ad_loc_stack -> f98
| Ad_loc_stack_Da -> f99
| Ad_none_Da -> f100
| Ad_open_parenAd_Ident -> f101
| Ad_open_parenAd_String -> f102
| Ad_open_paren_rec_root -> f103
| Ad_openbrace -> f104
| Ad_pattern_desc_Da -> f105
| Ad_pos -> f106
| Ad_private_flag_Da -> f107
| Ad_process_arg_constructor_declaration a0 ->
  f108 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_arg_constructor_declaration_Da -> f109
| Ad_process_arg_label_expression (a0, a1) ->
  f110 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0) a1
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a1)
| Ad_process_arg_label_expression_Da -> f111
| Ad_process_arg_label_expression_list a0 ->
  f112 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_ast_desc a0 ->
  f113 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_ast_desc_loc_list_pattern_option -> f114
| Ad_process_cases a0 ->
  f115 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_core_type_list_Da -> f116
| Ad_process_cstrs a0 ->
  f117 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_cstrs_Da -> f118
| Ad_process_expression_list_Da -> f119
| Ad_process_generic_list (a0, a1) ->
  f120 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0) a1
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a1)
| Ad_process_generic_type -> f121
| Ad_process_generic_type3 -> f122
| Ad_process_generic_type_Da -> f123
| Ad_process_label_declaration_list a0 ->
  f124 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_label_declaration_list_Da -> f125
| Ad_process_list_tail (a0, a1) ->
  f126 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0) a1
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a1)
| Ad_process_loc a0 ->
  f127 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_loc_Da -> f128
| Ad_process_params a0 ->
  f129 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_params_Da -> f130
| Ad_process_string -> f131
| Ad_process_string_loc_list_pattern_option -> f132
| Ad_process_string_loc_list_pattern_option_Da -> f133
| Ad_process_structure_item a0 ->
  f134 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_structure_item_desc a0 ->
  f135 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_structure_items a0 ->
  f136 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_structure_items_Da -> f137
| Ad_process_type_declaration_list a0 ->
  f138 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_type_declaration_list_Da -> f139
| Ad_process_value_binding_list -> f140
| Ad_process_var_list a0 ->
  f141 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_vars_list_Da -> f142
| Ad_quot_list a0 ->
  f143 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_quote (a0, a1) ->
  f144 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0) a1
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a1)
| Ad_rec_flag_Da -> f145
| Ad_root a0 ->
  f146 a0
    (ast_desc_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
      f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33
      f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51
      f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69
      f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87
      f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103
      f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117
      f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131
      f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145
      f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_string_Da -> f147
| Ad_structure_item_desc_Da -> f148
| Ad_todofixme -> f149
| Ad_type_kind_Da -> f150
| Ad_umcr_n_role_ -> f151
| Ad_umcr_n_type_ -> f152
| Ad_umcr_r_rel_ -> f153
| Ad_umcr_type -> f154
| Ad_x_Da -> f155
| Ad_y_Da -> f156
| Coq_ad_nostring -> f157

(** val ast_desc_rec :
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
    'a1 -> 'a1 -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> (ast_desc
    -> 'a1 -> ast_desc -> 'a1 -> 'a1) -> 'a1 -> (ast_desc -> 'a1 -> 'a1) ->
    (ast_desc -> 'a1 -> 'a1) -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 ->
    (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> ast_desc ->
    'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 ->
    (ast_desc -> 'a1 -> ast_desc -> 'a1 -> 'a1) -> (ast_desc -> 'a1 -> 'a1)
    -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    (ast_desc -> 'a1 -> 'a1) -> (ast_desc -> 'a1 -> 'a1) -> (ast_desc -> 'a1
    -> 'a1) -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> (ast_desc ->
    'a1 -> 'a1) -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> (ast_desc -> 'a1 ->
    ast_desc -> 'a1 -> 'a1) -> 'a1 -> (ast_desc -> 'a1 -> 'a1) -> 'a1 -> 'a1
    -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 ->
    ast_desc -> 'a1 **)

let rec ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16 f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34 f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52 f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70 f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88 f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104 f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118 f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132 f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146 f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 = function
| Adxu -> f
| Ad_Ad_arg_label_expression_list_Da -> f0
| Ad_Ad_attributes_Da -> f1
| Ad_Ad_bool_Da -> f2
| Ad_Ad_empty_list_Da -> f3
| Ad_Ad_int_Da -> f4
| Ad_Ad_list -> f5
| Ad_Ad_loc2_Da -> f6
| Ad_Ad_loc_Da -> f7
| Ad_Ad_loc_stack_Da -> f8
| Ad_Ad_pos_Da -> f9
| Ad_Ad_process_arg_constructor_declaration_Da -> f10
| Ad_Ad_process_arg_label_expression_Da -> f11
| Ad_Ad_process_arg_label_expression_list_Da -> f12
| Ad_Ad_process_ast_desc -> f13
| Ad_Ad_process_cases -> f14
| Ad_Ad_process_cstrs_Da -> f15
| Ad_Ad_process_generic_list_Da -> f16
| Ad_Ad_process_label_declaration_list_Da -> f17
| Ad_Ad_process_list_tail_Da -> f18
| Ad_Ad_process_loc_Da -> f19
| Ad_Ad_process_params_Da -> f20
| Ad_Ad_process_string_loc_list_pattern_option_Da -> f21
| Ad_Ad_process_structure_item_Da -> f22
| Ad_Ad_process_structure_item_desc_Da -> f23
| Ad_Ad_process_structure_items_Da -> f24
| Ad_Ad_process_type_declaration_list_Da -> f25
| Ad_Ad_process_value_binding_list_Da -> f26
| Ad_Ad_process_var_list_Da -> f27
| Ad_Ad_quote_Da -> f28
| Ad_Definition -> f29
| Ad_FIXME -> f30
| Ad_FIXME_process_ast_desc -> f31
| Ad_Fixme1 -> f32
| Ad_Fixme2_Da -> f33
| Ad_Ident a0 ->
  f34 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_MetaCoq_Definition -> f35
| Ad_NEW -> f36
| Ad_NoString -> f37
| Ad_Nolabel_Da -> f38
| Ad_None -> f39
| Ad_Nonrecursive_Da -> f40
| Ad_Obj -> f41
| Ad_P4 -> f42
| Ad_Pconst_string_Da -> f43
| Ad_Pexp_apply_Da -> f44
| Ad_Pexp_constant_Da -> f45
| Ad_Pexp_constraint_Da -> f46
| Ad_Pexp_construct_Da -> f47
| Ad_Pexp_fun_Da -> f48
| Ad_Pexp_ident_Da -> f49
| Ad_Pexp_tuple_Da -> f50
| Ad_Ppat_constraint_Da -> f51
| Ad_Ppat_var_Da -> f52
| Ad_Pstr_type_Da -> f53
| Ad_Pstr_value_Da -> f54
| Ad_Ptyp_constr_Da -> f55
| Ad_Ptype_abstract_Da -> f56
| Ad_Public_Da -> f57
| Ad_Recursive_Da -> f58
| Ad_String a0 ->
  f59 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_TRUNCATED -> f60
| Ad_TypeParam_T -> f61
| Ad_TypeParam_T_dot -> f62
| Ad_Type_UUU -> f63
| Ad__Da_Da -> f64
| Ad__Da_Da_Da -> f65
| Ad___ -> f66
| Ad____Da -> f67
| Ad_a_Da -> f68
| Ad_arg_label_Da -> f69
| Ad_arg_label_expression_list a0 ->
  f70 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_ast_desc -> f71
| Ad_ast_desc_Da -> f72
| Ad_attributes -> f73
| Ad_b_Da -> f74
| Ad_bool a0 ->
  f75 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_c_Da -> f76
| Ad_caret -> f77
| Ad_close_parens -> f78
| Ad_close_parens_Da_Da -> f79
| Ad_closebrace -> f80
| Ad_constant_Da -> f81
| Ad_core_type_desc_Da -> f82
| Ad_empty -> f83
| Ad_empty_array -> f84
| Ad_error -> f85
| Ad_errr -> f86
| Ad_expression_desc_Da -> f87
| Ad_fixme a0 ->
  f88 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_foo1_Da -> f89
| Ad_ident_Da -> f90
| Ad_int a0 ->
  f91 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_list a0 ->
  f92 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_list_Da -> f93
| Ad_loc -> f94
| Ad_loc2 -> f95
| Ad_loc2_Da -> f96
| Ad_loc_Da -> f97
| Ad_loc_stack -> f98
| Ad_loc_stack_Da -> f99
| Ad_none_Da -> f100
| Ad_open_parenAd_Ident -> f101
| Ad_open_parenAd_String -> f102
| Ad_open_paren_rec_root -> f103
| Ad_openbrace -> f104
| Ad_pattern_desc_Da -> f105
| Ad_pos -> f106
| Ad_private_flag_Da -> f107
| Ad_process_arg_constructor_declaration a0 ->
  f108 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_arg_constructor_declaration_Da -> f109
| Ad_process_arg_label_expression (a0, a1) ->
  f110 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0) a1
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a1)
| Ad_process_arg_label_expression_Da -> f111
| Ad_process_arg_label_expression_list a0 ->
  f112 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_ast_desc a0 ->
  f113 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_ast_desc_loc_list_pattern_option -> f114
| Ad_process_cases a0 ->
  f115 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_core_type_list_Da -> f116
| Ad_process_cstrs a0 ->
  f117 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_cstrs_Da -> f118
| Ad_process_expression_list_Da -> f119
| Ad_process_generic_list (a0, a1) ->
  f120 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0) a1
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a1)
| Ad_process_generic_type -> f121
| Ad_process_generic_type3 -> f122
| Ad_process_generic_type_Da -> f123
| Ad_process_label_declaration_list a0 ->
  f124 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_label_declaration_list_Da -> f125
| Ad_process_list_tail (a0, a1) ->
  f126 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0) a1
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a1)
| Ad_process_loc a0 ->
  f127 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_loc_Da -> f128
| Ad_process_params a0 ->
  f129 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_params_Da -> f130
| Ad_process_string -> f131
| Ad_process_string_loc_list_pattern_option -> f132
| Ad_process_string_loc_list_pattern_option_Da -> f133
| Ad_process_structure_item a0 ->
  f134 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_structure_item_desc a0 ->
  f135 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_structure_items a0 ->
  f136 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_structure_items_Da -> f137
| Ad_process_type_declaration_list a0 ->
  f138 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_type_declaration_list_Da -> f139
| Ad_process_value_binding_list -> f140
| Ad_process_var_list a0 ->
  f141 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_process_vars_list_Da -> f142
| Ad_quot_list a0 ->
  f143 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_quote (a0, a1) ->
  f144 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0) a1
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a1)
| Ad_rec_flag_Da -> f145
| Ad_root a0 ->
  f146 a0
    (ast_desc_rec f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 f16
      f17 f18 f19 f20 f21 f22 f23 f24 f25 f26 f27 f28 f29 f30 f31 f32 f33 f34
      f35 f36 f37 f38 f39 f40 f41 f42 f43 f44 f45 f46 f47 f48 f49 f50 f51 f52
      f53 f54 f55 f56 f57 f58 f59 f60 f61 f62 f63 f64 f65 f66 f67 f68 f69 f70
      f71 f72 f73 f74 f75 f76 f77 f78 f79 f80 f81 f82 f83 f84 f85 f86 f87 f88
      f89 f90 f91 f92 f93 f94 f95 f96 f97 f98 f99 f100 f101 f102 f103 f104
      f105 f106 f107 f108 f109 f110 f111 f112 f113 f114 f115 f116 f117 f118
      f119 f120 f121 f122 f123 f124 f125 f126 f127 f128 f129 f130 f131 f132
      f133 f134 f135 f136 f137 f138 f139 f140 f141 f142 f143 f144 f145 f146
      f147 f148 f149 f150 f151 f152 f153 f154 f155 f156 f157 a0)
| Ad_string_Da -> f147
| Ad_structure_item_desc_Da -> f148
| Ad_todofixme -> f149
| Ad_type_kind_Da -> f150
| Ad_umcr_n_role_ -> f151
| Ad_umcr_n_type_ -> f152
| Ad_umcr_r_rel_ -> f153
| Ad_umcr_type -> f154
| Ad_x_Da -> f155
| Ad_y_Da -> f156
| Coq_ad_nostring -> f157

type ast_desc_list =
| Ad_empty_list
| Ad_cons of ast_desc * ast_desc_list

(** val ast_desc_list_rect :
    'a1 -> (ast_desc -> ast_desc_list -> 'a1 -> 'a1) -> ast_desc_list -> 'a1 **)

let rec ast_desc_list_rect f f0 = function
| Ad_empty_list -> f
| Ad_cons (a0, a1) -> f0 a0 a1 (ast_desc_list_rect f f0 a1)

(** val ast_desc_list_rec :
    'a1 -> (ast_desc -> ast_desc_list -> 'a1 -> 'a1) -> ast_desc_list -> 'a1 **)

let rec ast_desc_list_rec f f0 = function
| Ad_empty_list -> f
| Ad_cons (a0, a1) -> f0 a0 a1 (ast_desc_list_rec f f0 a1)

(** val ident : ast_desc -> ast_desc **)

let ident a_value =
  Ad_Ident a_value

(** val none : ast_desc **)

let none =
  Ad_None

(** val process_cases : ast_desc -> ast_desc **)

let process_cases x_value =
  Ad_process_cases x_value

(** val process_var_list : ast_desc -> ast_desc **)

let process_var_list x_value =
  Ad_process_var_list x_value

(** val process_arg_constructor_declaration : ast_desc -> ast_desc **)

let process_arg_constructor_declaration x_value =
  Ad_process_arg_constructor_declaration x_value

(** val process_label_declaration_list : ast_desc -> ast_desc **)

let process_label_declaration_list x_value =
  Ad_process_label_declaration_list x_value

(** val process_params : ast_desc -> ast_desc **)

let process_params x_value =
  Ad_process_params x_value

(** val process_cstrs : ast_desc -> ast_desc **)

let process_cstrs x_value =
  Ad_process_cstrs x_value

(** val process_type_declaration_list : ast_desc -> ast_desc **)

let process_type_declaration_list x_value =
  Ad_process_type_declaration_list x_value

(** val loc : ast_desc **)

let loc =
  Ad_loc

(** val loc2 : ast_desc **)

let loc2 =
  Ad_loc2

(** val loc_stack : ast_desc **)

let loc_stack =
  Ad_loc_stack

(** val process_loc : ast_desc -> ast_desc **)

let process_loc a_value =
  Ad_process_loc a_value

(** val process_string_loc_list_pattern_option : ast_desc **)

let process_string_loc_list_pattern_option =
  Ad_process_string_loc_list_pattern_option

(** val process_arg_label_expression : ast_desc -> ast_desc -> ast_desc **)

let process_arg_label_expression x_value y_value =
  Ad_process_arg_label_expression (x_value, y_value)

(** val process_expression_list : ast_desc -> ast_desc **)

let process_expression_list x_value =
  Ad_arg_label_expression_list x_value

(** val process_arg_label_expression_list : ast_desc -> ast_desc **)

let process_arg_label_expression_list a_value =
  Ad_process_arg_label_expression_list a_value

(** val process_location : ast_desc -> ast_desc **)

let process_location a_value =
  Ad_process_loc a_value

(** val process_location_stack : ast_desc -> ast_desc **)

let process_location_stack a_value =
  Ad_process_loc a_value

(** val attributes : ast_desc **)

let attributes =
  Ad_attributes

(** val process_value_binding_list : ast_desc **)

let process_value_binding_list =
  Ad_process_value_binding_list

(** val pos : ast_desc -> ast_desc **)

let pos a_value =
  Ad_process_loc a_value

(** val b_value : ast_desc -> ast_desc **)

let b_value a_value =
  Ad_bool a_value

(** val mint : ast_desc -> ast_desc **)

let mint a_value =
  Ad_int a_value

(** val string_value : ast_desc -> ast_desc **)

let string_value a_value =
  Ad_String a_value

(** val make_pair : ast_desc -> ast_desc -> ast_desc **)

let make_pair _ _ =
  Ad_None

(** val process_string_option : ast_desc **)

let process_string_option =
  Ad_NoString

(** val process_structure_items : ast_desc -> ast_desc **)

let process_structure_items x_value =
  Ad_process_structure_items x_value

(** val my_append : ast_desc -> ast_desc -> ast_desc **)

let my_append a_value _ =
  a_value

(** val process_generic_type3 :
    ast_desc -> ast_desc -> ast_desc -> ast_desc **)

let process_generic_type3 a_value b_value0 _ =
  my_append Ad_process_generic_type3
    (my_append a_value
      (my_append Ad_caret
        (my_append b_value0
          (my_append Ad_openbrace (my_append Ad_None Ad_closebrace)))))

(** val quot : ast_desc -> ast_desc -> ast_desc **)

let quot a_value b_value0 =
  Ad_quote (a_value, b_value0)

(** val ad_list : ast_desc_list -> ast_desc **)

let ad_list _ =
  Ad_list Ad_None

(** val quot_list :
    ast_desc -> (ast_desc -> ast_desc) -> ast_desc_list -> ast_desc **)

let quot_list _ _ _ =
  Ad_None

(** val process_ast_desc : ast_desc -> ast_desc **)

let process_ast_desc _ =
  Ad_fixme Ad_FIXME_process_ast_desc

(** val process_simple_ast_root : ast_desc -> ast_desc **)

let process_simple_ast_root x_value =
  Ad_root x_value

(** val process_string : ast_desc -> ast_desc **)

let process_string a_value =
  quot Ad_process_string a_value

(** val process_int : ast_desc -> ast_desc **)

let process_int a_value =
  Ad_int a_value

(** val process_bool : ast_desc -> ast_desc **)

let process_bool a_value =
  Ad_bool a_value

(** val process_generic_list :
    ast_desc -> ast_desc_list -> (ast_desc -> ast_desc) -> ast_desc **)

let process_generic_list name _ _ =
  name

(** val print_endline : ast_desc -> coq_unit **)

let print_endline _ =
  Coq_tt

(** val def_basic : ast_desc -> ast_desc -> ast_desc **)

let def_basic a_value b_value0 =
  my_append Ad_MetaCoq_Definition
    (my_append a_value
      (my_append Ad_TypeParam_T (my_append b_value0 Ad_Type_UUU)))

(** val def_pair :
    ast_desc -> ast_desc -> ast_desc -> ast_desc -> ast_desc **)

let def_pair a_value b_value0 a1 b1 =
  my_append Ad_Definition
    (my_append a_value
      (my_append Ad_TypeParam_T
        (my_append b_value0
          (my_append Ad_Type_UUU
            (my_append a1 (my_append Adxu (my_append b1 Ad_TypeParam_T_dot)))))))

(** val process_generic_type2 : ast_desc -> ast_desc -> 'a1 -> ast_desc **)

let process_generic_type2 _ _ _ =
  Ad_empty

(** val not_empty : ast_desc_list -> bool **)

let not_empty _ =
  Coq_false

(** val ast_dest_list_to_single : ast_desc_list -> ast_desc **)

let ast_dest_list_to_single _ =
  Ad_empty

(** val process_ast_desc3 : ast_desc_list -> ast_desc **)

let process_ast_desc3 _ =
  Ad_empty

(** val process_ast_desc4 : ast_desc -> ast_desc **)

let process_ast_desc4 _ =
  Ad_empty

(** val process_ast_desc2 : ast_desc_list -> ast_desc **)

let process_ast_desc2 = function
| Ad_empty_list -> Ad_empty
| Ad_cons (_, t_value) ->
  (match not_empty t_value with
   | Coq_true -> Ad_FIXME
   | Coq_false -> Ad_empty_array)

(** val process_root_list : ast_desc -> ast_desc **)

let process_root_list a_value =
  a_value

(** val tostring : ast_desc -> ast_desc **)

let tostring _ =
  Ad_todofixme

(** val ast_desc_to_yojson : ast_desc -> ast_desc **)

let ast_desc_to_yojson x_value =
  x_value

(** val process_generic_type_print :
    ast_desc -> ast_desc -> ast_desc -> coq_unit **)

let process_generic_type_print _ _ c_value =
  let yj1 = process_root_list c_value in print_endline (my_append Ad_NEW yj1)

(** val process_generic_type :
    ast_desc -> ast_desc -> ast_desc -> ast_desc **)

let process_generic_type _ _ _ =
  Ad_None

(** val process_structure_item : ast_desc -> ast_desc **)

let process_structure_item x_value =
  Ad_process_structure_item x_value

(** val process_structure_item_desc : ast_desc -> ast_desc **)

let process_structure_item_desc x_value =
  Ad_process_structure_item_desc x_value

(** val extract_root : ast_desc -> ast_desc **)

let extract_root = function
| Ad_Ident string0 -> Ad_Ident string0
| Ad_bool bool0 -> Ad_bool bool0
| Ad_loc -> process_generic_type3 Ad_ast_desc_Da Ad_Ad_loc_Da Ad_None
| Ad_loc2 -> process_generic_type3 Ad_ast_desc_Da Ad_Ad_loc2_Da Ad_None
| Ad_loc_stack ->
  process_generic_type3 Ad_ast_desc_Da Ad_Ad_loc_stack_Da Ad_None
| Ad_pos -> process_generic_type3 Ad_ast_desc_Da Ad_Ad_pos_Da Ad_None
| Ad_process_arg_constructor_declaration ast_desc0 ->
  process_generic_type3 Ad_ast_desc_Da
    Ad_Ad_process_arg_constructor_declaration_Da (Ad_process_ast_desc
    ast_desc0)
| Ad_process_arg_label_expression (ast_desc0, ast_desc1) ->
  process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_arg_label_expression_Da
    (make_pair (process_ast_desc ast_desc0) (process_ast_desc ast_desc1))
| Ad_process_arg_label_expression_list ast_desc0 ->
  process_generic_type3 Ad_ast_desc_Da
    Ad_Ad_process_arg_label_expression_list_Da (Ad_process_ast_desc ast_desc0)
| Ad_process_ast_desc _ -> Ad_Fixme2_Da
| Ad_process_cases ast_desc0 ->
  process_generic_type3 Ad_ast_desc Ad_Ad_process_cases (Ad_process_ast_desc
    ast_desc0)
| Ad_process_cstrs ast_desc0 ->
  process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_cstrs_Da
    (Ad_process_ast_desc ast_desc0)
| Ad_process_generic_list (string0, _) ->
  process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_generic_list_Da
    (make_pair (process_string string0) (Ad_fixme Ad_P4))
| Ad_process_label_declaration_list _ -> Ad_FIXME
| Ad_process_list_tail (ast_desc0, ast_desc1) ->
  process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_list_tail_Da
    (make_pair (process_ast_desc ast_desc0) (process_ast_desc ast_desc1))
| Ad_process_string_loc_list_pattern_option ->
  process_generic_type3 Ad_ast_desc_Da
    Ad_Ad_process_string_loc_list_pattern_option_Da Ad_None
| Ad_process_value_binding_list ->
  process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_value_binding_list_Da
    Ad_None
| _ -> Ad_Fixme1

(** val ff1 : ast_desc **)

let ff1 =
  process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da
    (string_value Ad_none_Da)

(** val ff0 : ast_desc **)

let ff0 =
  process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None

(** val ff00 : ast_desc **)

let ff00 =
  Ad_None

(** val ff000 : ast_desc **)

let ff000 =
  process_generic_type Ad_constant_Da Ad_Pconst_string_Da ff00

(** val ff2 : ast_desc **)

let ff2 =
  process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da ff000

(** val foo1 : ast_desc **)

let foo1 =
  process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da
    (make_pair ff0 (make_pair ff1 ff2))
