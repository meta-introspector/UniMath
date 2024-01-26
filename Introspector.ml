open PartA
open Preamble

type umcr_refl = coq_UU

type umcr_type = umcr_refl

type 't umcr_n_role_arg_label = umcr_refl

type 't umcr_n_role_constant = umcr_refl

type 't umcr_n_role_core_type_desc = umcr_refl

type 't umcr_n_role_expression_desc = umcr_refl

type 't umcr_n_role_pattern_desc = umcr_refl

type 't umcr_n_role_rec_flag = umcr_refl

type 't umcr_n_role_structure_item_desc = umcr_refl

type 't umcr_n_type_Nolabel = umcr_refl

type 't umcr_n_type_Nonrecursive = umcr_refl

type 't umcr_n_type_Pconst_string = umcr_refl

type 't umcr_n_type_Pexp_apply = umcr_refl

type 't umcr_n_type_Pexp_constant = umcr_refl

type 't umcr_n_type_Pexp_constraint = umcr_refl

type 't umcr_n_type_Pexp_construct = umcr_refl

type 't umcr_n_type_Pexp_fun = umcr_refl

type 't umcr_n_type_Pexp_ident = umcr_refl

type 't umcr_n_type_Pexp_tuple = umcr_refl

type 't umcr_n_type_Ppat_constraint = umcr_refl

type 't umcr_n_type_Ppat_var = umcr_refl

type 't umcr_n_type_Pstr_value = umcr_refl

type 't umcr_n_type_Ptyp_constr = umcr_refl

type 't umcr_r_rel_arg_label__Nolabel =
  ('t umcr_n_role_arg_label, 't umcr_n_type_Nolabel) dirprod

type 't umcr_r_rel_constant__Pconst_string =
  ('t umcr_n_role_constant, 't umcr_n_type_Pconst_string) dirprod

type 't umcr_r_rel_core_type_desc__Ptyp_constr =
  ('t umcr_n_role_core_type_desc, 't umcr_n_type_Ptyp_constr) dirprod

type 't umcr_r_rel_expression_desc__Pexp_apply =
  ('t umcr_n_role_expression_desc, 't umcr_n_type_Pexp_apply) dirprod

type 't umcr_r_rel_expression_desc__Pexp_constant =
  ('t umcr_n_role_expression_desc, 't umcr_n_type_Pexp_constant) dirprod

type 't umcr_r_rel_expression_desc__Pexp_constraint =
  ('t umcr_n_role_expression_desc, 't umcr_n_type_Pexp_constraint) dirprod

type 't umcr_r_rel_expression_desc__Pexp_construct =
  ('t umcr_n_role_expression_desc, 't umcr_n_type_Pexp_construct) dirprod

type 't umcr_r_rel_expression_desc__Pexp_fun =
  ('t umcr_n_role_expression_desc, 't umcr_n_type_Pexp_fun) dirprod

type 't umcr_r_rel_expression_desc__Pexp_ident =
  ('t umcr_n_role_expression_desc, 't umcr_n_type_Pexp_ident) dirprod

type 't umcr_r_rel_expression_desc__Pexp_tuple =
  ('t umcr_n_role_expression_desc, 't umcr_n_type_Pexp_tuple) dirprod

type 't umcr_r_rel_pattern_desc__Ppat_constraint =
  ('t umcr_n_role_pattern_desc, 't umcr_n_type_Ppat_constraint) dirprod

type 't umcr_r_rel_pattern_desc__Ppat_var =
  ('t umcr_n_role_pattern_desc, 't umcr_n_type_Ppat_var) dirprod

type 't umcr_r_rel_rec_flag__Nonrecursive =
  ('t umcr_n_role_rec_flag, 't umcr_n_type_Nonrecursive) dirprod

type 't umcr_r_rel_structure_item_desc__Pstr_value =
  ('t umcr_n_role_structure_item_desc, 't umcr_n_type_Pstr_value) dirprod

type umcr_constant = umcr_refl
