Require Export UniMath.Foundations.All.
Definition  umcr_refl: UU := UU.
Definition umcr_type: UU := umcr_refl.

Definition umcr_n_role_arg_label(T : umcr_type): UU := umcr_refl.
Definition umcr_n_role_constant(T : umcr_type): UU := umcr_refl.
Definition umcr_n_role_core_type_desc(T : umcr_type): UU := umcr_refl.
Definition umcr_n_role_expression_desc(T : umcr_type): UU := umcr_refl.
Definition umcr_n_role_pattern_desc(T : umcr_type): UU := umcr_refl.
Definition umcr_n_role_rec_flag(T : umcr_type): UU := umcr_refl.
Definition umcr_n_role_structure_item_desc(T : umcr_type): UU := umcr_refl.
Definition umcr_n_type_Nolabel(T : umcr_type): UU := umcr_refl.
Definition umcr_n_type_Nonrecursive(T : umcr_type): UU := umcr_refl.
Definition umcr_n_type_Pconst_string(T : umcr_type): UU := umcr_refl.
Definition umcr_n_type_Pexp_apply(T : umcr_type): UU := umcr_refl.
Definition umcr_n_type_Pexp_constant(T : umcr_type): UU := umcr_refl.
Definition umcr_n_type_Pexp_constraint(T : umcr_type): UU := umcr_refl.
Definition umcr_n_type_Pexp_construct(T : umcr_type): UU := umcr_refl.
Definition umcr_n_type_Pexp_fun(T : umcr_type): UU := umcr_refl.
Definition umcr_n_type_Pexp_ident(T : umcr_type): UU := umcr_refl.
Definition umcr_n_type_Pexp_tuple(T : umcr_type): UU := umcr_refl.
Definition umcr_n_type_Ppat_constraint(T : umcr_type): UU := umcr_refl.
Definition umcr_n_type_Ppat_var(T : umcr_type): UU := umcr_refl.
Definition umcr_n_type_Pstr_value(T : umcr_type): UU := umcr_refl.
Definition umcr_n_type_Ptyp_constr(T : umcr_type): UU := umcr_refl.
Definition umcr_r_rel_arg_label_Nolabel(T : umcr_type): UU := umcr_n_role_arg_label T ☺ umcr_n_type_Nolabel T.
Definition umcr_r_rel_constant_Pconst_string(T : umcr_type): UU := umcr_n_role_constant T ☺ umcr_n_type_Pconst_string T.
Definition umcr_r_rel_core_type_desc_Ptyp_constr(T : umcr_type): UU := umcr_n_role_core_type_desc T ☺ umcr_n_type_Ptyp_constr T.
Definition umcr_r_rel_expression_desc_Pexp_apply(T : umcr_type): UU := umcr_n_role_expression_desc T ☺ umcr_n_type_Pexp_apply T.
Definition umcr_r_rel_expression_desc_Pexp_constant(T : umcr_type): UU := umcr_n_role_expression_desc T ☺ umcr_n_type_Pexp_constant T.
Definition umcr_r_rel_expression_desc_Pexp_constraint(T : umcr_type): UU := umcr_n_role_expression_desc T ☺ umcr_n_type_Pexp_constraint T.
Definition umcr_r_rel_expression_desc_Pexp_construct(T : umcr_type): UU := umcr_n_role_expression_desc T ☺ umcr_n_type_Pexp_construct T.
Definition umcr_r_rel_expression_desc_Pexp_fun(T : umcr_type): UU := umcr_n_role_expression_desc T ☺ umcr_n_type_Pexp_fun T.
Definition umcr_r_rel_expression_desc_Pexp_ident(T : umcr_type): UU := umcr_n_role_expression_desc T ☺ umcr_n_type_Pexp_ident T.
Definition umcr_r_rel_expression_desc_Pexp_tuple(T : umcr_type): UU := umcr_n_role_expression_desc T ☺ umcr_n_type_Pexp_tuple T.
Definition umcr_r_rel_pattern_desc_Ppat_constraint(T : umcr_type): UU := umcr_n_role_pattern_desc T ☺ umcr_n_type_Ppat_constraint T.
Definition umcr_r_rel_pattern_desc_Ppat_var(T : umcr_type): UU := umcr_n_role_pattern_desc T ☺ umcr_n_type_Ppat_var T.
Definition umcr_r_rel_rec_flag_Nonrecursive(T : umcr_type): UU := umcr_n_role_rec_flag T ☺ umcr_n_type_Nonrecursive T.
Definition umcr_r_rel_structure_item_desc_Pstr_value(T : umcr_type): UU := umcr_n_role_structure_item_desc T ☺ umcr_n_type_Pstr_value T.

Definition umcr_constant: UU := umcr_refl .
