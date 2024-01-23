Require Export UniMath.Foundations.All.
Definition  umcr_refl: UU := UU.
			   
			     
		     
Definition umcr_constant: UU := umcr_refl .
Definition umcr_core_type_desc: UU := umcr_refl .
Definition umcr_expression_desc: UU := umcr_refl.
Definition umcr_pattern_desc: UU := umcr_refl.
Definition umcr_rec_flag: UU := umcr_refl (* bool*).
Definition umcr_structure_item_desc: UU := umcr_refl.


Definition umcr_role_constant: UU := umcr_refl.
Definition umcr_role_core_type_desc: UU := umcr_refl.
Definition umcr_role_expression_desc: UU := umcr_refl.
Definition umcr_role_pattern_desc: UU := umcr_refl.
Definition umcr_role_rec_flag: UU := umcr_refl.
Definition umcr_role_structure_item_desc: UU := umcr_refl.

			     

Definition umcr_type_Nonrecursive: UU := umcr_refl.
Definition umcr_type_Pconst_string: UU := umcr_refl.
Definition umcr_type_Pexp_apply: UU := umcr_refl.
Definition umcr_type_Pexp_constant: UU := umcr_refl.
Definition umcr_type_Pexp_constraint: UU := umcr_refl.
Definition umcr_type_Pexp_construct: UU := umcr_refl.
Definition umcr_type_Pexp_fun: UU := umcr_refl.
Definition umcr_type_Pexp_ident: UU := umcr_refl.
Definition umcr_type_Pexp_tuple: UU := umcr_refl.
Definition umcr_type_Ppat_constraint: UU := umcr_refl.
Definition umcr_type_Ppat_var: UU := umcr_refl.
Definition umcr_type_Pstr_value: UU := umcr_refl.
Definition umcr_type_Ptyp_constr: UU := umcr_refl.

Definition umcr_type: UU := umcr_refl.			     
			     
Definition umcr_rel_arg_label_Nolabel (T : umcr_type) : UU := umcr_refl.
  
Definition umcr_role_arg_label(T:umcr_type): UU := umcr_refl.
			     
Definition umcr_type_Nolabel(T:umcr_type): UU := umcr_refl.
			     
Definition umcr_rel2_arg_label_Nolabel (T:umcr_type) :UU :=
 
    umcr_role_arg_label T
   ×u
			     umcr_type_Nolabel T.
			     
			     
Definition umcr_rel_constant_Pconst_string: UU := umcr_refl.
Definition umcr_rel_core_type_desc_Ptyp_constr: UU := umcr_refl.
Definition umcr_rel_expression_desc_Pexp_apply: UU := umcr_refl.
Definition umcr_rel_expression_desc_Pexp_constant: UU := umcr_refl.
Definition umcr_rel_expression_desc_Pexp_constraint: UU := umcr_refl.
Definition umcr_rel_expression_desc_Pexp_construct: UU := umcr_refl.
Definition umcr_rel_expression_desc_Pexp_fun: UU := umcr_refl.
Definition umcr_rel_expression_desc_Pexp_ident: UU := umcr_refl.
Definition umcr_rel_expression_desc_Pexp_tuple: UU := umcr_refl.
Definition umcr_rel_pattern_desc_Ppat_constraint: UU := umcr_refl.
Definition umcr_rel_pattern_desc_Ppat_var: UU := umcr_refl.
Definition umcr_rel_rec_flag_Nonrecursive: UU := umcr_refl.
Definition umcr_rel_structure_item_desc_Pstr_value: UU := umcr_refl.			     
