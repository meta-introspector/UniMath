

Section WithUniMath .



Require Export UniMath.Foundations.All.
Require Import UniMath.Combinatorics.Lists.
Definition string_list : UU -> UU := list.
Definition string : UU := UU.
Definition MyUU := UU.
Inductive ast_desc : Type :=
| Adxu : ast_desc
| Ad_Ad_arg_label_expression_list_Da : ast_desc
| Ad_Ad_attributes_Da : ast_desc
| Ad_Ad_bool_Da : ast_desc
| Ad_Ad_empty_list_Da : ast_desc
| Ad_Ad_int_Da : ast_desc
| Ad_Ad_list : ast_desc
| Ad_Ad_loc2_Da : ast_desc
| Ad_Ad_loc_Da : ast_desc
| Ad_Ad_loc_stack_Da : ast_desc
| Ad_Ad_pos_Da : ast_desc
| Ad_Ad_process_arg_constructor_declaration_Da : ast_desc
| Ad_Ad_process_arg_label_expression_Da : ast_desc
| Ad_Ad_process_arg_label_expression_list_Da : ast_desc
| Ad_Ad_process_ast_desc : ast_desc
| Ad_Ad_process_cases : ast_desc
| Ad_Ad_process_cstrs_Da : ast_desc
| Ad_Ad_process_generic_list_Da : ast_desc
| Ad_Ad_process_label_declaration_list_Da : ast_desc
| Ad_Ad_process_list_tail_Da : ast_desc
| Ad_Ad_process_loc_Da : ast_desc
| Ad_Ad_process_params_Da : ast_desc
| Ad_Ad_process_string_loc_list_pattern_option_Da : ast_desc
| Ad_Ad_process_structure_item_Da : ast_desc
| Ad_Ad_process_structure_item_desc_Da : ast_desc
| Ad_Ad_process_structure_items_Da : ast_desc
| Ad_Ad_process_type_declaration_list_Da : ast_desc
| Ad_Ad_process_value_binding_list_Da : ast_desc
| Ad_Ad_process_var_list_Da : ast_desc
| Ad_Ad_quote_Da : ast_desc
| Ad_Definition : ast_desc
| Ad_FIXME : ast_desc
| Ad_FIXME_process_ast_desc : ast_desc
| Ad_Fixme1 : ast_desc
| Ad_Fixme2_Da : ast_desc
| Ad_Ident : ast_desc -> ast_desc
| Ad_MetaCoq_Definition : ast_desc
| Ad_NEW : ast_desc
| Ad_NoString : ast_desc
| Ad_Nolabel_Da : ast_desc
| Ad_None : ast_desc
| Ad_Nonrecursive_Da : ast_desc
| Ad_Obj : ast_desc
| Ad_P4 : ast_desc
| Ad_Pconst_string_Da : ast_desc
| Ad_Pexp_apply_Da : ast_desc
| Ad_Pexp_constant_Da : ast_desc
| Ad_Pexp_constraint_Da : ast_desc
| Ad_Pexp_construct_Da : ast_desc
| Ad_Pexp_fun_Da : ast_desc
| Ad_Pexp_ident_Da : ast_desc
| Ad_Pexp_tuple_Da : ast_desc
| Ad_Ppat_constraint_Da : ast_desc
| Ad_Ppat_var_Da : ast_desc
| Ad_Pstr_type_Da : ast_desc
| Ad_Pstr_value_Da : ast_desc
| Ad_Ptyp_constr_Da : ast_desc
| Ad_Ptype_abstract_Da : ast_desc
| Ad_Public_Da : ast_desc
| Ad_Recursive_Da : ast_desc
| Ad_String : ast_desc -> ast_desc(*orig*)
| Ad_TRUNCATED : ast_desc
| Ad_TypeParam_T : ast_desc
| Ad_TypeParam_T_dot : ast_desc
| Ad_Type_UU : ast_desc
| Ad_Da_Da : ast_desc
| Ad_Da_Da_Da : ast_desc
| Ad_ : ast_desc
| Ad_Da : ast_desc
| Ad_a_Da : ast_desc
| Ad_arg_label_Da : ast_desc
| Ad_arg_label_expression_list : ast_desc -> ast_desc(*orig*)
| Ad_ast_desc : ast_desc
| Ad_ast_desc_Da : ast_desc
| Ad_attributes : ast_desc(*orig*)
| Ad_b_Da : ast_desc
| Ad_bool : ast_desc -> ast_desc(*orig*)
| Ad_c_Da : ast_desc
| Ad_caret
| Ad_close_parens : ast_desc
| Ad_close_parens_Da_Da : ast_desc
| Ad_closebrace : ast_desc
| Ad_constant_Da : ast_desc
| Ad_core_type_desc_Da : ast_desc
| Ad_empty : ast_desc
| Ad_empty_array : ast_desc
| Ad_error : ast_desc
| Ad_errr : ast_desc
| Ad_expression_desc_Da : ast_desc
| Ad_fixme : ast_desc -> ast_desc(*orig*)
| Ad_foo1_Da : ast_desc
| Ad_ident_Da : ast_desc
| Ad_int : ast_desc -> ast_desc(*orig*)
| Ad_list : ast_desc -> ast_desc(*orig*)
| Ad_list_Da : ast_desc
| Ad_loc : ast_desc(*orig*)
| Ad_loc2 : ast_desc(*orig*)
| Ad_loc2_Da : ast_desc
| Ad_loc_Da : ast_desc
| Ad_loc_stack : ast_desc(*orig*)
| Ad_loc_stack_Da : ast_desc
| Ad_none_Da : ast_desc
| Ad_open_parenAd_Ident : ast_desc
| Ad_open_parenAd_String : ast_desc
| Ad_open_paren_rec_root : ast_desc
| Ad_openbrace
| Ad_pattern_desc_Da : ast_desc
| Ad_pos : ast_desc(*orig*)
| Ad_private_flag_Da : ast_desc
| Ad_process_arg_constructor_declaration : ast_desc -> ast_desc(*orig*)
| Ad_process_arg_constructor_declaration_Da : ast_desc
| Ad_process_arg_label_expression : ast_desc -> ast_desc -> ast_desc(*orig*)
| Ad_process_arg_label_expression_Da : ast_desc
| Ad_process_arg_label_expression_list : ast_desc -> ast_desc(*orig*)
| Ad_process_ast_desc : ast_desc -> ast_desc(*orig*)
| Ad_process_ast_desc_loc_list_pattern_option : ast_desc
| Ad_process_cases : ast_desc -> ast_desc(*orig*)
| Ad_process_core_type_list_Da : ast_desc
| Ad_process_cstrs : ast_desc -> ast_desc(*orig*)
| Ad_process_cstrs_Da : ast_desc
| Ad_process_expression_list_Da : ast_desc
| Ad_process_generic_list : ast_desc -> ast_desc -> ast_desc(*orig*)
| Ad_process_generic_type : ast_desc
| Ad_process_generic_type3
| Ad_process_generic_type_Da : ast_desc
| Ad_process_label_declaration_list : ast_desc -> ast_desc(*orig*)
| Ad_process_label_declaration_list_Da : ast_desc
| Ad_process_list_tail : ast_desc -> ast_desc -> ast_desc(*orig*)
| Ad_process_loc : ast_desc -> ast_desc(*orig*)
| Ad_process_loc_Da : ast_desc
| Ad_process_params : ast_desc -> ast_desc(*orig*)
| Ad_process_params_Da : ast_desc
| Ad_process_string : ast_desc
| Ad_process_string_loc_list_pattern_option : ast_desc(*orig*)
| Ad_process_string_loc_list_pattern_option_Da : ast_desc
| Ad_process_structure_item : ast_desc -> ast_desc(*orig*)
| Ad_process_structure_item_desc : ast_desc -> ast_desc(*orig*)
| Ad_process_structure_items : ast_desc -> ast_desc(*orig*)
| Ad_process_structure_items_Da : ast_desc
| Ad_process_type_declaration_list : ast_desc -> ast_desc(*orig*)
| Ad_process_type_declaration_list_Da : ast_desc
| Ad_process_value_binding_list : ast_desc(*orig*)
| Ad_process_var_list : ast_desc -> ast_desc(*orig*)
| Ad_process_vars_list_Da : ast_desc
| Ad_quot_list : ast_desc -> ast_desc
| Ad_quote : ast_desc -> ast_desc -> ast_desc(*orig*)
| Ad_rec_flag_Da : ast_desc
| Ad_root : ast_desc -> ast_desc(*orig*)
| Ad_string_Da : ast_desc
| Ad_structure_item_desc_Da : ast_desc
| Ad_todofixme : ast_desc
| Ad_type_kind_Da : ast_desc
| Ad_umcr_n_role_ : ast_desc
| Ad_umcr_n_type_ : ast_desc
| Ad_umcr_r_rel_ : ast_desc
| Ad_umcr_type : ast_desc
| Ad_x_Da : ast_desc
| Ad_y_Da : ast_desc
| ad_nostring : ast_desc
.

Inductive ast_desc_list  : Type :=
| Ad_empty_list : ast_desc_list
| Ad_cons : ast_desc ->ast_desc_list  ->ast_desc_list
.

(* Module simple_ast_root. *)
(*   Record record {sa_role sa_type sa_list : Set} : Set := Build { *)
(*     sa_role : sa_role; *)
(*     sa_type : sa_type; *)
(*     sa_list : sa_list; *)
(*   }. *)
(*   Arguments record : clear implicits. *)
(*   Definition with_sa_role {t_sa_role t_sa_type t_sa_list} sa_role *)
(*     (r : record t_sa_role t_sa_type t_sa_list) := *)
(*     Build t_sa_role t_sa_type t_sa_list sa_role r.(sa_type) r.(sa_list). *)
(*   Definition with_sa_type {t_sa_role t_sa_type t_sa_list} sa_type *)
(*     (r : record t_sa_role t_sa_type t_sa_list) := *)
(*     Build t_sa_role t_sa_type t_sa_list r.(sa_role) sa_type r.(sa_list). *)
(*   Definition with_sa_list {t_sa_role t_sa_type t_sa_list} sa_list *)
(*     (r : record t_sa_role t_sa_type t_sa_list) := *)
(*     Build t_sa_role t_sa_type t_sa_list r.(sa_role) r.(sa_type) sa_list. *)
(* End simple_ast_root. *)

(* Definition simple_ast_root_skeleton := simple_ast_root.record. *)

(*
ast_desc2 : Type
The term "simple_ast_root_skeleton" has type "Set → Set → Set → Set"
which should be Set, Prop or Type.

 Inductive ast_desc2 : Type := *)
(*   | Ad2_simple_ast_root_record : simple_ast_root_skeleton . *)



Definition ident (a_value : ast_desc) : ast_desc := Ad_Ident a_value.

Definition none : ast_desc := Ad_None.


Definition process_cases (x_value : ast_desc) : ast_desc :=
  Ad_process_cases x_value.

Definition process_var_list (x_value : ast_desc) : ast_desc :=
  Ad_process_var_list x_value.

Definition process_arg_constructor_declaration (x_value : ast_desc)
  : ast_desc := Ad_process_arg_constructor_declaration x_value.

Definition process_label_declaration_list (x_value : ast_desc)
  : ast_desc := Ad_process_label_declaration_list x_value.

Definition process_params (x_value : ast_desc) : ast_desc :=
  Ad_process_params x_value.

Definition process_cstrs (x_value : ast_desc) : ast_desc :=
  Ad_process_cstrs x_value.

Definition process_type_declaration_list (x_value : ast_desc) : ast_desc :=
  Ad_process_type_declaration_list x_value.

Definition loc : ast_desc := Ad_loc.

Definition loc2 : ast_desc := Ad_loc2.

Definition loc_stack : ast_desc := Ad_loc_stack.

Definition process_loc (a_value : ast_desc) : ast_desc :=
  Ad_process_loc a_value.

Definition process_string_loc_list_pattern_option : ast_desc :=
  Ad_process_string_loc_list_pattern_option.

Definition process_arg_label_expression
  (x_value : ast_desc) (y_value : ast_desc) : ast_desc :=
  Ad_process_arg_label_expression x_value y_value.

Definition process_expression_list (x_value : ast_desc) : ast_desc :=
  Ad_arg_label_expression_list x_value.

Definition process_arg_label_expression_list (a_value : ast_desc)
  : ast_desc := Ad_process_arg_label_expression_list a_value.

Definition process_location (a_value : ast_desc) : ast_desc :=
  Ad_process_loc a_value.

Definition process_location_stack (a_value : ast_desc) : ast_desc :=
  Ad_process_loc a_value.

Definition attributes : ast_desc := Ad_attributes.

Definition process_value_binding_list : ast_desc :=
  Ad_process_value_binding_list.

Definition pos (a_value : ast_desc) : ast_desc := Ad_process_loc a_value.

Definition b_value (a_value : ast_desc) : ast_desc := Ad_bool a_value.

Definition mint (a_value : ast_desc) : ast_desc := Ad_int a_value.

Definition string_value (a_value : ast_desc) : ast_desc := Ad_String a_value.

Definition make_pair (a_value : ast_desc) (b_value : ast_desc) : ast_desc := Ad_None.

Definition process_string_option : ast_desc := Ad_NoString.

Notation "[ a , b ]" := (make_pair a b ).

Definition process_structure_items (x_value : ast_desc) : ast_desc :=
  Ad_process_structure_items x_value.



(* Fixpoint process_generic_list_tail *)
(*   (name : ast_desc) (a_value :   ast_desc_list  ) (f_value : ast_desc -> ast_desc) *)
(*   : ast_desc_list := *)
(*   match a_value with *)

(*   | Ad_empty_list => Ad_empty_list *)
(*   | Ad_cons a_value t_value => *)
(*     let v1 := f_value a_value in Ad_empty_list *)
(*     (* if Stdlib.not_empty t_value nil then *) *)
(*     (*   Ad_process_list_tail v1 (process_generic_list_tail name t_value f_value) *) *)
(*     (* else *) *)
(*     (*   v1 *) *)
(*   end *)

Definition  my_append (a_value : ast_desc) (b_value : ast_desc) : ast_desc := a_value .

Definition process_generic_type3
  (a_value : ast_desc) (b_value : ast_desc) (c_value : ast_desc) : ast_desc :=
  my_append Ad_process_generic_type3
    (my_append a_value
      (my_append Ad_caret
        (my_append b_value
          (my_append Ad_openbrace
            (my_append Ad_None(* (process_ast_desc4  c_value) *) Ad_closebrace )))))
.

Definition quot (a_value : ast_desc) (b_value : ast_desc) : ast_desc :=
  Ad_quote a_value b_value
.

Definition ad_list(ls : ast_desc_list) :=
  Ad_list Ad_None
.

Definition quot_list (n_value : ast_desc) (fn : ast_desc -> ast_desc) (ls : ast_desc_list)
  : ast_desc :=
  let quot_a (c_value : ast_desc) : ast_desc :=
    quot n_value (fn c_value) in
  Ad_None
  (* process_generic_list (my_append (Ad_quot_list n_value (ad_list ls) quot_a)) *)
.

Definition process_ast_desc (l_value : ast_desc) : ast_desc :=
  Ad_fixme Ad_FIXME_process_ast_desc
.

Definition process_simple_ast_root (x_value : ast_desc) : ast_desc :=
  Ad_root x_value
.

Definition process_string (a_value : ast_desc) : ast_desc :=
  quot Ad_process_string a_value
.

Definition process_int (a_value : ast_desc) : ast_desc := Ad_int a_value
.

Definition process_bool (a_value : ast_desc) : ast_desc := Ad_bool a_value
.

Definition process_generic_list
  (name : ast_desc) (a_value : ast_desc_list) (f_value : ast_desc -> ast_desc)
  : ast_desc := name.

  (* Ad_process_generic_list name *)
  (*   [ *)
  (*     match a_value with *)
  (*     | Ad_empty_list => Ad_empty_list name *)
  (*     | cons a_value t_value => *)
  (*       let v1 := f_value a_value in *)
  (*       if Stdlib.not_empty t_value nil then *)
  (*         Ad_process_list_tail v1 *)
  (*           (process_generic_list_tail name t_value f_value) *)
  (*       else *)
  (*         v1 *)
  (*     end *)
  (*   ] *)
Definition print_endline (a:ast_desc):unit := tt.


(*TODO in coq return unit*)
Definition def_basic (a_value : ast_desc) (b_value : ast_desc) : ast_desc :=
  let t_value :=
    my_append Ad_MetaCoq_Definition
      (my_append a_value
        (my_append Ad_TypeParam_T (my_append b_value Ad_Type_UU)))
    in
  let '_ := print_endline t_value in
  t_value
.

Definition def_pair (a_value : ast_desc) (b_value : ast_desc) (a1 : ast_desc) (b1 : ast_desc)
  : ast_desc :=
  let tt :=
    my_append Ad_Definition
      (my_append a_value
        (my_append Ad_TypeParam_T
          (my_append b_value
            (my_append Ad_Type_UU
              (my_append a1
                (my_append Adxu (my_append b1 Ad_TypeParam_T_dot ))))))) in
  let '_ := print_endline tt in
  tt
.

Definition process_generic_type2 {A : MyUU}
  (a_value : ast_desc) (b_value : ast_desc) (c_value : A) : ast_desc := Ad_empty
  (* let baset := Ad_umcr_type in *)
  (* let _at := my_append Ad_umcr_n_role_ a_value in *)
  (* let bt := my_append Ad_umcr_n_type_ b_value in *)
  (* let ct := *)
  (*   my_append Ad_umcr_r_rel_ *)
  (*     (my_append a_value (my_append Ad_ b_value)) in *)
  (* let f1 := def_basic _at baset in *)
  (* let f2 := def_basic bt baset in *)
  (* let f3 := def_pair ct baset _at bt in *)
  (* my_append Ad_ (my_append f1 (my_append f2 f3)) *)
.

(* Definition process_ast_desc (x_value : ast_desc) : ast_desc := *)
(*   Ad_fixme Ad_Ad_process_ast_desc *)
(* . *)

Definition not_empty (al : ast_desc_list) : bool := false
.
Definition ast_dest_list_to_single (al : ast_desc_list) : ast_desc := Ad_empty
.
Definition process_ast_desc3 (al : ast_desc_list) : ast_desc := Ad_empty
                                                             .
Definition process_ast_desc4 (al : ast_desc) : ast_desc := Ad_empty
.
                                         Definition process_ast_desc2 (al : ast_desc_list) : ast_desc :=
  match al with
  | Ad_empty_list => Ad_empty
  | Ad_cons h_value t_value =>
    if not_empty t_value  then
      (* my_append (extract_root h_value) *)
      (*   (my_append Ad_caret (process_ast_desc3 t_value)) *)
      Ad_FIXME
    else
      Ad_empty_array
  end
.
(* Definition extract_root (al : ast_desc) : ast_desc := al. *)
(* Definition process_ast_desc3 (al : ast_desc_list) : ast_desc := *)
(*   match al with *)
(*   | Ad_empty_list => Ad_empty *)
(*   | Ad_cons h_value t_value => *)
(*     if not_empty t_value  then *)
(*       my_append (extract_root h_value) *)
(*         (my_append Ad_caret (process_ast_desc3 t_value)) *)
(*     else *)
(*       Ad_error *)
(*   end
.
 *)


(* Definition process_ast_desc4 (al : ast_desc_list) : ast_desc := *)
(*   match al with *)
(*   | Ad_empty_list => Ad_empty *)
(*   | Ad_cons h_value t_value => *)
(*     if not_empty t_value then *)
(*       my_append (extract_root h_value) (my_append Ad_caret Ad_TRUNCATED) *)
(*     else *)
(*        Ad_errr *)
(*   end *)
(* . *)

Definition process_root_list (a_value : ast_desc) : ast_desc := a_value
  (* match a_value with *)
  (* | Ad_empty_list => Ad_empty *)
  (* | Ad_cons x_value t_value => *)
  (*   let v1 := extract_root x_value in *)
  (*   if not_empty t_value  then *)
  (*     my_append v1 (my_append Ad_caret (process_root_list t_value)) *)
  (*   else *)
  (*     v1 *)
  (* end *)
.

Definition tostring (x_value : ast_desc) : ast_desc := Ad_todofixme
.

Definition ast_desc_to_yojson (x_value : ast_desc) : ast_desc :=
  x_value
.

Definition process_generic_type_print
  (a_value : ast_desc) (b_value : ast_desc) (c_value : ast_desc) : unit :=
  let yj := tostring (ast_desc_to_yojson c_value) in
  let dd := my_append Ad_process_generic_type (my_append a_value b_value)
    in
  let yj1 := process_root_list c_value in
  let '_ := print_endline yj in
  let '_ := print_endline dd in
  print_endline (my_append Ad_NEW yj1)
.

Definition process_generic_type
  (a_value : ast_desc) (b_value : ast_desc) (c_value : ast_desc) : ast_desc :=
  let '_ := process_generic_type_print a_value b_value c_value in
  Ad_None
    (* Ad2_simple_ast_root_record {| simple_ast_root.sa_role := a_value; simple_ast_root.sa_type := b_value; *)
    (*   simple_ast_root.sa_list := c_value; |} *)
.

Definition process_structure_item (x_value : ast_desc) : ast_desc :=
  Ad_process_structure_item x_value
.

Definition process_structure_item_desc (x_value : ast_desc) : ast_desc :=
  Ad_process_structure_item_desc x_value
.

(* Definition process_structure_items (x_value : ast_desc_list) : ast_desc := *)
(*   process_generic_list Ad_Ad_process_structure_items_Da x_value process_structure_item. *)

Definition extract_root (x_value : ast_desc) : ast_desc :=
  match x_value with
  | Ad_Ad_arg_label_expression_list_Da     => Ad_Fixme1
  | Ad_Ad_attributes_Da     => Ad_Fixme1
  | Ad_Ad_bool_Da     => Ad_Fixme1
  | Ad_Ad_empty_list_Da     => Ad_Fixme1
  | Ad_Ad_int_Da     => Ad_Fixme1
  | Ad_Ad_list     => Ad_Fixme1
  | Ad_Ad_loc2_Da     => Ad_Fixme1
  | Ad_Ad_loc_Da     => Ad_Fixme1
  | Ad_Ad_loc_stack_Da     => Ad_Fixme1
  | Ad_Ad_pos_Da     => Ad_Fixme1
  | Ad_Ad_process_arg_constructor_declaration_Da     => Ad_Fixme1
  | Ad_Ad_process_arg_label_expression_Da     => Ad_Fixme1
  | Ad_Ad_process_arg_label_expression_list_Da     => Ad_Fixme1
  | Ad_Ad_process_ast_desc => Ad_Fixme1
  | Ad_Ad_process_cases     => Ad_Fixme1
  | Ad_Ad_process_cstrs_Da     => Ad_Fixme1
  | Ad_Ad_process_generic_list_Da     => Ad_Fixme1
  | Ad_Ad_process_label_declaration_list_Da     => Ad_Fixme1
  | Ad_Ad_process_list_tail_Da     => Ad_Fixme1
  | Ad_Ad_process_loc_Da     => Ad_Fixme1
  | Ad_Ad_process_params_Da     => Ad_Fixme1
  | Ad_Ad_process_string_loc_list_pattern_option_Da     => Ad_Fixme1
  | Ad_Ad_process_structure_item_Da     => Ad_Fixme1
  | Ad_Ad_process_structure_item_desc_Da     => Ad_Fixme1
  | Ad_Ad_process_structure_items_Da     => Ad_Fixme1
  | Ad_Ad_process_type_declaration_list_Da     => Ad_Fixme1
  | Ad_Ad_process_value_binding_list_Da     => Ad_Fixme1
  | Ad_Ad_process_var_list_Da     => Ad_Fixme1
  | Ad_Ad_quote_Da     => Ad_Fixme1
  | Ad_Definition     => Ad_Fixme1
  | Ad_FIXME
  | Ad_FIXME_process_ast_desc
  | Ad_Fixme1     => Ad_Fixme1
  | Ad_Fixme2_Da     => Ad_Fixme1
  | Ad_Ident string0 =>   Ad_Ident string0
  | Ad_MetaCoq_Definition     => Ad_Fixme1
  | Ad_NEW     => Ad_Fixme1
  | Ad_NoString => Ad_Fixme1
  | Ad_Nolabel_Da     => Ad_Fixme1
  | Ad_None => Ad_Fixme1
  | Ad_Nonrecursive_Da     => Ad_Fixme1
  | Ad_Obj     => Ad_Fixme1
  | Ad_P4     => Ad_Fixme1
  | Ad_Pconst_string_Da     => Ad_Fixme1
  | Ad_Pexp_apply_Da     => Ad_Fixme1
  | Ad_Pexp_constant_Da     => Ad_Fixme1
  | Ad_Pexp_constraint_Da     => Ad_Fixme1
  | Ad_Pexp_construct_Da     => Ad_Fixme1
  | Ad_Pexp_fun_Da     => Ad_Fixme1
  | Ad_Pexp_ident_Da     => Ad_Fixme1
  | Ad_Pexp_tuple_Da     => Ad_Fixme1
  | Ad_Ppat_constraint_Da     => Ad_Fixme1
  | Ad_Ppat_var_Da     => Ad_Fixme1
  | Ad_Pstr_type_Da     => Ad_Fixme1
  | Ad_Pstr_value_Da     => Ad_Fixme1
  | Ad_Ptyp_constr_Da     => Ad_Fixme1
  | Ad_Ptype_abstract_Da     => Ad_Fixme1
  | Ad_Public_Da     => Ad_Fixme1
  | Ad_Recursive_Da     => Ad_Fixme1
  | Ad_String string0 =>   Ad_Fixme1
  | Ad_TRUNCATED     => Ad_Fixme1
  | Ad_TypeParam_T     => Ad_Fixme1
  | Ad_TypeParam_T_dot     => Ad_Fixme1
  | Ad_Type_UU     => Ad_Fixme1
  | Ad_Da_Da     => Ad_Fixme1
  | Ad_Da_Da_Da     => Ad_Fixme1
  | Ad_     => Ad_Fixme1
  | Ad_Da     => Ad_Fixme1
  | Ad_a_Da     => Ad_Fixme1
  | Ad_arg_label_Da     => Ad_Fixme1
  | Ad_arg_label_expression_list ast_desc0 =>    Ad_Fixme1
  | Ad_ast_desc     => Ad_Fixme1
  | Ad_ast_desc_Da     => Ad_Fixme1
  | Ad_attributes => Ad_Fixme1
  | Ad_b_Da     => Ad_Fixme1
  | Ad_bool bool0 =>    Ad_bool bool0
  | Ad_c_Da     => Ad_Fixme1
  | Ad_caret
  | Ad_close_parens     => Ad_Fixme1
  | Ad_close_parens_Da_Da     => Ad_Fixme1
  | Ad_closebrace     => Ad_Fixme1
  | Ad_constant_Da     => Ad_Fixme1
  | Ad_core_type_desc_Da     => Ad_Fixme1
  | Ad_empty     => Ad_Fixme1
  | Ad_empty_array     => Ad_Fixme1
  | Ad_error     => Ad_Fixme1
  | Ad_errr     => Ad_Fixme1
  | Ad_expression_desc_Da     => Ad_Fixme1
  | Ad_fixme  _   => Ad_Fixme1
  | Ad_foo1_Da     => Ad_Fixme1
  | Ad_ident_Da     => Ad_Fixme1
  | Ad_int int0 =>  Ad_Fixme1
  | Ad_list  _   => Ad_Fixme1

  | Ad_list_Da     => Ad_Fixme1
  | Ad_loc => process_generic_type3 Ad_ast_desc_Da Ad_Ad_loc_Da Ad_None
  | Ad_loc2 => process_generic_type3 Ad_ast_desc_Da Ad_Ad_loc2_Da Ad_None
  | Ad_loc2_Da     => Ad_Fixme1
  | Ad_loc_Da     => Ad_Fixme1
  | Ad_loc_stack => process_generic_type3 Ad_ast_desc_Da Ad_Ad_loc_stack_Da Ad_None
  | Ad_loc_stack_Da     => Ad_Fixme1
  | Ad_none_Da     => Ad_Fixme1
  | Ad_open_parenAd_Ident     => Ad_Fixme1
  | Ad_open_parenAd_String     => Ad_Fixme1
  | Ad_open_paren_rec_root     => Ad_Fixme1
  | Ad_openbrace
  | Ad_pattern_desc_Da     => Ad_Fixme1
  | Ad_pos => process_generic_type3 Ad_ast_desc_Da Ad_Ad_pos_Da Ad_None
  | Ad_private_flag_Da     => Ad_Fixme1

  | Ad_process_arg_constructor_declaration ast_desc0 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_arg_constructor_declaration_Da      (Ad_process_ast_desc ast_desc0)
  | Ad_process_arg_constructor_declaration_Da     => Ad_Fixme1

  | Ad_process_arg_label_expression ast_desc0 ast_desc1 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_arg_label_expression_Da      [ process_ast_desc ast_desc0, process_ast_desc ast_desc1 ]
  | Ad_process_arg_label_expression_Da     => Ad_Fixme1

  | Ad_process_arg_label_expression_list ast_desc0 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_arg_label_expression_list_Da      (Ad_process_ast_desc ast_desc0)
  | Ad_process_ast_desc _ => Ad_Fixme2_Da
  | Ad_process_ast_desc_loc_list_pattern_option     => Ad_Fixme1

  | Ad_process_cases ast_desc0 =>    process_generic_type3 Ad_ast_desc Ad_Ad_process_cases      (Ad_process_ast_desc ast_desc0)
  | Ad_process_core_type_list_Da     => Ad_Fixme1

  | Ad_process_cstrs ast_desc0 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_cstrs_Da     (Ad_process_ast_desc ast_desc0)
  | Ad_process_cstrs_Da     => Ad_Fixme1
  | Ad_process_expression_list_Da     => Ad_Fixme1

  | Ad_process_generic_list string0 ast_desc1 =>     process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_generic_list_Da      [        process_string string0,        Ad_fixme Ad_P4      ]
  | Ad_process_generic_type     => Ad_Fixme1
  | Ad_process_generic_type3
  | Ad_process_generic_type_Da     => Ad_Fixme1

  | Ad_process_label_declaration_list ast_desc0 =>    (* process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_label_declaration_list_Da    Ad_Ad_process_ast_desc ast_desc0 *) Ad_FIXME
  | Ad_process_label_declaration_list_Da     => Ad_Fixme1

  | Ad_process_list_tail ast_desc0 ast_desc1 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_list_tail_Da      [ process_ast_desc ast_desc0, process_ast_desc ast_desc1 ]

  | Ad_process_loc ast_desc0 =>    (* process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_loc_Da        process_ast_desc ast_desc0 *) Ad_Fixme1
  | Ad_process_loc_Da     => Ad_Fixme1

  | Ad_process_params ast_desc0 => Ad_Fixme1 (*    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_params_Da       process_ast_desc ast_desc0 *)
  | Ad_process_params_Da     => Ad_Fixme1
  | Ad_process_string     => Ad_Fixme1
  | Ad_process_string_loc_list_pattern_option =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_string_loc_list_pattern_option_Da       Ad_None
  | Ad_process_string_loc_list_pattern_option_Da     => Ad_Fixme1
  | Ad_process_structure_item _    => Ad_Fixme1
  (* | Ad_process_structure_item ast_desc0 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_structure_item_Da      process_ast_desc ast_desc0 *)
  | Ad_process_structure_item_desc _    => Ad_Fixme1
  (* | Ad_process_structure_item_desc ast_desc0 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_structure_item_desc_Da      process_ast_desc ast_desc0 *)
  | Ad_process_structure_items  _   => Ad_Fixme1
  (* | Ad_process_structure_items ast_desc0 =>      process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_structure_items_Da       process_ast_desc ast_desc0 *)
  | Ad_process_structure_items_Da     => Ad_Fixme1
  | Ad_process_type_declaration_list _    => Ad_Fixme1
  (* | Ad_process_type_declaration_list ast_desc0 =>     process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_type_declaration_list_Da        process_ast_desc ast_desc0 *)
  | Ad_process_type_declaration_list_Da     => Ad_Fixme1
  | Ad_process_value_binding_list =>     process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_value_binding_list_Da Ad_None
  | Ad_process_var_list   _  => Ad_Fixme1
  (* | Ad_process_var_list ast_desc0 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_process_var_list_Da      process_ast_desc ast_desc0 *)
  | Ad_process_vars_list_Da     => Ad_Fixme1
  | Ad_quot_list  _   => Ad_Fixme1
  | Ad_quote  _ _   => Ad_Fixme1
  (* | Ad_quote string0 ast_desc1 =>    process_generic_type3 Ad_ast_desc_Da Ad_Ad_quote_Da      [ process_string string0, process_string ast_desc1 ] *)
  | Ad_rec_flag_Da     => Ad_Fixme1
  | Ad_root  _   => Ad_Fixme1
  | Ad_string_Da     => Ad_Fixme1
  | Ad_structure_item_desc_Da     => Ad_Fixme1
  | Ad_todofixme     => Ad_Fixme1
  | Ad_type_kind_Da     => Ad_Fixme1
  | Ad_umcr_n_role_     => Ad_Fixme1
  | Ad_umcr_n_type_     => Ad_Fixme1
  | Ad_umcr_r_rel_     => Ad_Fixme1
  | Ad_umcr_type     => Ad_Fixme1
  | Ad_x_Da     => Ad_Fixme1
  | Ad_y_Da     => Ad_Fixme1
  | Adxu => Ad_Fixme1
  | ad_nostring     => Ad_Fixme1

  end.

Definition ff1 := process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da ( string_value Ad_none_Da ).
Definition ff0 := process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None.


Definition ff00 :=      Ad_None.

Definition ff000 :=     (process_generic_type Ad_constant_Da Ad_Pconst_string_Da            ff00).
Definition ff2 := process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da
        ff000.

Definition foo1 : ast_desc :=
  process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da
    [
      ff0,
      [
        ff1,
        ff2
      ]
    ].

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       [ *)
(*       (process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*         (string_value Ad_process_vars_list_Da)) *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *)
(*         [ *)
(*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *)
(*           none, *)
(*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*             string_value Ad_x_Da , *)
(*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *)
(*             [ *)
(*               process_generic_type Ad_constant_Da *)
(*                 Ad_Pconst_string_Da *)
(*                 [ *)
(*                   string_value *)
(*                     Ad_process_vars_list_Da, *)
(*                   process_string_option *)
(*                 ] *)
(*             ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*         [ string_value Ad_process_arg_constructor_declaration_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *)
(*         [ *)
(*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *)
(*           none, *)
(*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*             [ string_value Ad_x_Da ], *)
(*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *)
(*             [ *)
(*               process_generic_type Ad_constant_Da *)
(*                 Ad_Pconst_string_Da *)
(*                 [ *)
(*                   string_value *)
(*                     Ad_process_arg_constructor_declaration_Da, *)
(*                   process_string_option *)
(*                 ] *)
(*             ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*         [ string_value Ad_process_label_declaration_list_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *)
(*         [ *)
(*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *)
(*           none, *)
(*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*             [ string_value Ad_x_Da ], *)
(*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *)
(*             [ *)
(*               process_generic_type Ad_constant_Da *)
(*                 Ad_Pconst_string_Da *)
(*                 [ *)
(*                   string_value *)
(*                     Ad_process_label_declaration_list_Da, *)
(*                   process_string_option *)
(*                 ] *)
(*             ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*         [ string_value Ad_process_params_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *)
(*         [ *)
(*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *)
(*           none, *)
(*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*             [ string_value Ad_x_Da ], *)
(*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *)
(*             [ *)
(*               process_generic_type Ad_constant_Da *)
(*                 Ad_Pconst_string_Da *)
(*                 [ *)
(*                   string_value *)
(*                     Ad_process_params_Da, *)
(*                   process_string_option *)
(*                 ] *)
(*             ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*         [ string_value Ad_process_cstrs_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *)
(*         [ *)
(*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *)
(*           none, *)
(*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*             [ string_value Ad_x_Da ], *)
(*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *)
(*             [ *)
(*               process_generic_type Ad_constant_Da *)
(*                 Ad_Pconst_string_Da *)
(*                 [ *)
(*                   string_value *)
(*                     Ad_process_cstrs_Da, *)
(*                   process_string_option *)
(*                 ] *)
(*             ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*         [ string_value Ad_process_core_type_list_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *)
(*         [ *)
(*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *)
(*           none, *)
(*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*             [ string_value Ad_x_Da ], *)
(*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *)
(*             [ *)
(*               process_generic_type Ad_constant_Da *)
(*                 Ad_Pconst_string_Da *)
(*                 [ *)
(*                   string_value *)
(*                     Ad_process_core_type_list_Da, *)
(*                   process_string_option *)
(*                 ] *)
(*             ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*         [ string_value Ad_process_type_declaration_list_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *)
(*         [ *)
(*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *)
(*           none, *)
(*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*             [ string_value Ad_x_Da ], *)
(*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *)
(*             [ *)
(*               process_generic_type Ad_constant_Da *)
(*                 Ad_Pconst_string_Da *)
(*                 [ *)
(*                   string_value *)
(*                     Ad_process_type_declaration_list_Da, *)
(*                   process_string_option *)
(*                 ] *)
(*             ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da [ string_value Ad_loc_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *)
(*         [ *)
(*           process_generic_type Ad_constant_Da Ad_Pconst_string_Da *)
(*             [ string_value Ad_loc_Da, process_string_option ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da [ string_value Ad_loc2_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *)
(*         [ *)
(*           process_generic_type Ad_constant_Da Ad_Pconst_string_Da *)
(*             [ string_value Ad_loc_Da, process_string_option ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*         [ string_value Ad_loc_stack_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *)
(*         [ *)
(*           process_generic_type Ad_constant_Da Ad_Pconst_string_Da *)
(*             [ string_value Ad_loc_Da, process_string_option ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*         [ string_value Ad_process_generic_type_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *)
(*         [ *)
(*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *)
(*           none, *)
(*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_constraint_Da *)
(*             [ *)
(*               process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*                 [ string_value Ad_a_Da ], *)
(*               process_generic_type Ad_core_type_desc_Da *)
(*                 Ad_Ptyp_constr_Da *)
(*                 [ *)
(*                   ident *)
(*                     Ad_string_Da, *)
(*                   process_core_type_list *)
(*                     Ad_None *)
(*                 ] *)
(*             ], *)
(*           process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *)
(*             [ *)
(*               process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *)
(*               none, *)
(*               process_generic_type Ad_pattern_desc_Da *)
(*                 Ad_Ppat_constraint_Da *)
(*                 [ *)
(*                   process_generic_type *)
(*                     Ad_pattern_desc_Da *)
(*                     Ad_Ppat_var_Da *)
(*                     [ *)
(*                       string_value *)
(*                         Ad_b_Da *)
(*                     ], *)
(*                   process_generic_type *)
(*                     Ad_core_type_desc_Da *)
(*                     Ad_Ptyp_constr_Da *)
(*                     [ *)
(*                       ident *)
(*                         Ad_string_Da, *)
(*                       process_core_type_list *)
(*                         Ad_None *)
(*                     ] *)
(*                 ], *)
(*               process_generic_type Ad_expression_desc_Da *)
(*                 Ad_Pexp_fun_Da *)
(*                 [ *)
(*                   process_generic_type *)
(*                     Ad_arg_label_Da *)
(*                     Ad_Nolabel_Da *)
(*                     Ad_None, *)
(*                   none, *)
(*                   process_generic_type *)
(*                     Ad_pattern_desc_Da *)
(*                     Ad_Ppat_constraint_Da *)
(*                     [ *)
(*                       process_generic_type *)
(*                         Ad_pattern_desc_Da *)
(*                         Ad_Ppat_var_Da *)
(*                         [ *)
(*                           string_value *)
(*                             Ad_c_Da *)
(*                         ], *)
(*                       process_generic_type *)
(*                         Ad_core_type_desc_Da *)
(*                         Ad_Ptyp_constr_Da *)
(*                         [ *)
(*                           ident *)
(*                             Ad_list_Da, *)
(*                           process_core_type_list *)
(*                             [ *)
(*                               process_generic_type *)
(*                                 Ad_core_type_desc_Da *)
(*                                 Ad_Ptyp_constr_Da *)
(*                                 [ *)
(*                                   ident *)
(*                                     Ad_string_Da, *)
(*                                   process_core_type_list *)
(*                                     Ad_None *)
(*                                 ] *)
(*                             ] *)
(*                         ] *)
(*                     ], *)
(*                   process_generic_type *)
(*                     Ad_expression_desc_Da *)
(*                     Ad_Pexp_constraint_Da *)
(*                     [ *)
(*                       process_generic_type *)
(*                         Ad_expression_desc_Da *)
(*                         Ad_Pexp_constant_Da *)
(*                         [ *)
(*                           process_generic_type *)
(*                             Ad_constant_Da *)
(*                             Ad_Pconst_string_Da *)
(*                             [ *)
(*                               string_value *)
(*                                 Ad_process_generic_type_Da, *)
(*                               process_string_option *)
(*                             ] *)
(*                         ], *)
(*                       process_generic_type *)
(*                         Ad_core_type_desc_Da *)
(*                         Ad_Ptyp_constr_Da *)
(*                         [ *)
(*                           ident *)
(*                             Ad_string_Da, *)
(*                           process_core_type_list *)
(*                             Ad_None *)
(*                         ] *)
(*                     ] *)
(*                 ] *)
(*             ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*         [ string_value Ad_process_loc_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *)
(*         [ *)
(*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *)
(*           none, *)
(*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*             [ string_value Ad_a_Da ], *)
(*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *)
(*             [ *)
(*               process_generic_type Ad_constant_Da *)
(*                 Ad_Pconst_string_Da *)
(*                 [ *)
(*                   string_value *)
(*                     Ad_process_loc_Da, *)
(*                   process_string_option *)
(*                 ] *)
(*             ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da [ string_value Ad_ident_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *)
(*         [ *)
(*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *)
(*           none, *)
(*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*             [ string_value Ad_a_Da ], *)
(*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *)
(*             [ *)
(*               process_generic_type Ad_constant_Da *)
(*                 Ad_Pconst_string_Da *)
(*                 [ *)
(*                   string_value *)
(*                     Ad_ident_Da, *)
(*                   process_string_option *)
(*                 ] *)
(*             ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*         [ string_value Ad_process_string_loc_list_pattern_option_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *)
(*         [ *)
(*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *)
(*           none, *)
(*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*             [ string_value Ad_x_Da ], *)
(*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *)
(*             [ *)
(*               process_generic_type Ad_constant_Da *)
(*                 Ad_Pconst_string_Da *)
(*                 [ *)
(*                   string_value *)
(*                     Ad_process_string_loc_list_pattern_option_Da, *)
(*                   process_string_option *)
(*                 ] *)
(*             ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*         [ string_value Ad_process_arg_label_expression_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *)
(*         [ *)
(*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *)
(*           none, *)
(*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*             [ string_value Ad_x_Da ], *)
(*           process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *)
(*             [ *)
(*               process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *)
(*               none, *)
(*               process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*                 [ string_value Ad_y_Da ], *)
(*               process_generic_type Ad_expression_desc_Da *)
(*                 Ad_Pexp_constant_Da *)
(*                 [ *)
(*                   process_generic_type *)
(*                     Ad_constant_Da *)
(*                     Ad_Pconst_string_Da *)
(*                     [ *)
(*                       string_value *)
(*                         Ad_process_arg_label_expression_Da, *)
(*                       process_string_option *)
(*                     ] *)
(*                 ] *)
(*             ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*         [ string_value Ad_process_expression_list_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *)
(*         [ *)
(*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *)
(*           none, *)
(*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*             [ string_value Ad_x_Da ], *)
(*           process_generic_type Ad_expression_desc_Da Ad_Pexp_constant_Da *)
(*             [ *)
(*               process_generic_type Ad_constant_Da *)
(*                 Ad_Pconst_string_Da *)
(*                 [ *)
(*                   string_value *)
(*                     Ad_process_expression_list_Da, *)
(*                   process_string_option *)
(*                 ] *)
(*             ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*         [ string_value Ad_process_structure_items_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_fun_Da *)
(*         [ *)
(*           process_generic_type Ad_arg_label_Da Ad_Nolabel_Da Ad_None, *)
(*           none, *)
(*           process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da *)
(*             [ string_value Ad_x_Da ], *)
(*           process_generic_type Ad_expression_desc_Da Ad_Pexp_apply_Da *)
(*             [ *)
(*               process_generic_type Ad_expression_desc_Da *)
(*                 Ad_Pexp_ident_Da *)
(*                 [ ident Ad_caret ], *)
(*               process_arg_label_expression_list *)
(*                 [ *)
(*                   process_arg_label_expression *)
(*                     (process_generic_type *)
(*                       Ad_arg_label_Da *)
(*                       Ad_Nolabel_Da *)
(*                       Ad_None) *)
(*                     (process_generic_type *)
(*                       Ad_expression_desc_Da *)
(*                       Ad_Pexp_constant_Da *)
(*                       [ *)
(*                         process_generic_type *)
(*                           Ad_constant_Da *)
(*                           Ad_Pconst_string_Da *)
(*                           [ *)
(*                             string_value *)
(*                               Ad_process_structure_items_Da, *)
(*                             process_string_option *)
(*                           ] *)
(*                       ]), *)
(*                   process_arg_label_expression *)
(*                     (process_generic_type *)
(*                       Ad_arg_label_Da *)
(*                       Ad_Nolabel_Da *)
(*                       Ad_None) *)
(*                     (process_generic_type *)
(*                       Ad_expression_desc_Da *)
(*                       Ad_Pexp_ident_Da *)
(*                       [ *)
(*                         ident *)
(*                           Ad_x_Da *)
(*                       ]) *)
(*                 ] *)
(*             ] *)
(*         ] *)
(*     ]. *)

(* Definition foo1 : ast_desc := *)
(*   process_generic_type Ad_structure_item_desc_Da Ad_Pstr_value_Da *)
(*     [ *)
(*       process_generic_type Ad_rec_flag_Da Ad_Nonrecursive_Da Ad_None, *)
(*       process_generic_type Ad_pattern_desc_Da Ad_Ppat_var_Da [ string_value Ad_foo1_Da ], *)
(*       process_generic_type Ad_expression_desc_Da Ad_Pexp_apply_Da *)
(*         [ *)
(*           process_generic_type Ad_expression_desc_Da Ad_Pexp_ident_Da *)
(*             [ ident Ad_process_generic_type_Da ], *)
(*           process_arg_label_expression_list *)
(*             [ *)
(*               process_arg_label_expression *)
(*                 (process_generic_type *)
(*                   Ad_arg_label_Da *)
(*                   Ad_Nolabel_Da *)
(*                   Ad_None) *)
(*                 (process_generic_type *)
(*                   Ad_expression_desc_Da *)
(*                   Ad_Pexp_constant_Da *)
(*                   [ *)
(*                     process_generic_type *)
(*                       Ad_constant_Da *)
(*                       Ad_Pconst_string_Da *)
(*                       [ *)
(*                         string_value *)
(*                           Ad_structure_item_desc_Da, *)
(*                         process_string_option *)
(*                       ] *)
(*                   ]), *)
(*               process_arg_label_expression *)
(*                 (process_generic_type *)
(*                   Ad_arg_label_Da *)
(*                   Ad_Nolabel_Da *)
(*                   Ad_None) *)
(*                 (process_generic_type *)
(*                   Ad_expression_desc_Da *)
(*                   Ad_Pexp_constant_Da *)
(*                   [ *)
(*                     process_generic_type *)
(*                       Ad_constant_Da *)
(*                       Ad_Pconst_string_Da *)
(*                       [ *)
(*                         string_value *)
(*                           Ad_Pstr_type_Da, *)
(*                         process_string_option *)
(*                       ] *)
(*                   ]), *)
(*               process_arg_label_expression *)
(*                 (process_generic_type *)
(*                   Ad_arg_label_Da *)
(*                   Ad_Nolabel_Da *)
(*                   Ad_None) *)
(*                 (process_generic_type *)
(*                   Ad_expression_desc_Da *)
(*                   Ad_Pexp_construct_Da *)
(*                   [ *)
(*                     ident *)
(*                       Ad_::_Da, *)
(*                     process_generic_type *)
(*                       Ad_expression_desc_Da *)
(*                       Ad_Pexp_tuple_Da *)
(*                       [ *)
(*                         process_expression_list *)
(*                           [ *)
(*                             process_generic_type *)
(*                               Ad_expression_desc_Da *)
(*                               Ad_Pexp_apply_Da *)
(*                               [ *)
(*                                 process_generic_type *)
(*                                   Ad_expression_desc_Da *)
(*                                   Ad_Pexp_ident_Da *)
(*                                   [ *)
(*                                     ident *)
(*                                       Ad_process_generic_type_Da *)
(*                                   ], *)
(*                                 process_arg_label_expression_list *)
(*                                   [ *)
(*                                     process_arg_label_expression *)
(*                                       (process_generic_type *)
(*                                         Ad_arg_label_Da *)
(*                                         Ad_Nolabel_Da *)
(*                                         Ad_None) *)
(*                                       (process_generic_type *)
(*                                         Ad_expression_desc_Da *)
(*                                         Ad_Pexp_constant_Da *)
(*                                         [ *)
(*                                           process_generic_type *)
(*                                             Ad_constant_Da *)
(*                                             Ad_Pconst_string_Da *)
(*                                             [ *)
(*                                               string_value *)
(*                                                 Ad_rec_flag_Da, *)
(*                                               process_string_option *)
(*                                             ] *)
(*                                         ]), *)
(*                                     process_arg_label_expression *)
(*                                       (process_generic_type *)
(*                                         Ad_arg_label_Da *)
(*                                         Ad_Nolabel_Da *)
(*                                         Ad_None) *)
(*                                       (process_generic_type *)
(*                                         Ad_expression_desc_Da *)
(*                                         Ad_Pexp_constant_Da *)
(*                                         [ *)
(*                                           process_generic_type *)
(*                                             Ad_constant_Da *)
(*                                             Ad_Pconst_string_Da *)
(*                                             [ *)
(*                                               string_value *)
(*                                                 Ad_Recursive_Da, *)
(*                                               process_string_option *)
(*                                             ] *)
(*                                         ]), *)
(*                                     process_arg_label_expression *)
(*                                       (process_generic_type *)
(*                                         Ad_arg_label_Da *)
(*                                         Ad_Nolabel_Da *)
(*                                         Ad_None) *)
(*                                       (process_generic_type *)
(*                                         Ad_expression_desc_Da *)
(*                                         Ad_Pexp_construct_Da *)
(*                                         [ *)
(*                                           ident *)
(*                                             Ad_empty_list, *)
(*                                           none *)
(*                                         ]) *)
(*                                   ] *)
(*                               ], *)
(*                             process_generic_type *)
(*                               Ad_expression_desc_Da *)
(*                               Ad_Pexp_construct_Da *)
(*                               [ *)
(*                                 ident *)
(*                                   Ad_::_Da, *)
(*                                 process_generic_type *)
(*                                   Ad_expression_desc_Da *)
(*                                   Ad_Pexp_tuple_Da *)
(*                                   [ *)
(*                                     process_expression_list *)
(*                                       [ *)
(*                                         process_generic_type *)
(*                                           Ad_expression_desc_Da *)
(*                                           Ad_Pexp_apply_Da *)
(*                                           [ *)
(*                                             process_generic_type *)
(*                                               Ad_expression_desc_Da *)
(*                                               Ad_Pexp_ident_Da *)
(*                                               [ *)
(*                                                 ident *)
(*                                                   Ad_process_type_declaration_list_Da *)
(*                                               ], *)
(*                                             process_arg_label_expression_list *)
(*                                               [ *)
(*                                                 process_arg_label_expression *)
(*                                                   (process_generic_type *)
(*                                                     Ad_arg_label_Da *)
(*                                                     Ad_Nolabel_Da *)
(*                                                     Ad_None) *)
(*                                                   (process_generic_type *)
(*                                                     Ad_expression_desc_Da *)
(*                                                     Ad_Pexp_construct_Da *)
(*                                                     [ *)
(*                                                       ident *)
(*                                                         Ad_::_Da, *)
(*                                                       process_generic_type *)
(*                                                         Ad_expression_desc_Da *)
(*                                                         Ad_Pexp_tuple_Da *)
(*                                                         [ *)
(*                                                           process_expression_list *)
(*                                                             [ *)
(*                                                               process_generic_type *)
(*                                                                 Ad_expression_desc_Da *)
(*                                                                 Ad_Pexp_apply_Da *)
(*                                                                 [ *)
(*                                                                   process_generic_type *)
(*                                                                     Ad_expression_desc_Da *)
(*                                                                     Ad_Pexp_ident_Da *)
(*                                                                     [ *)
(*                                                                       ident *)
(*                                                                         Ad_caret *)
(*                                                                     ], *)
(*                                                                   process_arg_label_expression_list *)
(*                                                                     [ *)
(*                                                                       process_arg_label_expression *)
(*                                                                         (process_generic_type *)
(*                                                                           Ad_arg_label_Da *)
(*                                                                           Ad_Nolabel_Da *)
(*                                                                           Ad_None) *)
(*                                                                         (process_generic_type *)
(*                                                                           Ad_expression_desc_Da *)
(*                                                                           Ad_Pexp_apply_Da *)
(*                                                                           [ *)
(*                                                                             process_generic_type *)
(*                                                                               Ad_expression_desc_Da *)
(*                                                                               Ad_Pexp_ident_Da *)
(*                                                                               [ *)
(*                                                                                 ident *)
(*                                                                                   Ad_string_Da *)
(*                                                                               ], *)
(*                                                                             process_arg_label_expression_list *)
(*                                                                               [ *)
(*                                                                                 process_arg_label_expression *)
(*                                                                                   (process_generic_type *)
(*                                                                                     Ad_arg_label_Da *)
(*                                                                                     Ad_Nolabel_Da *)
(*                                                                                     Ad_None) *)
(*                                                                                   (process_generic_type *)
(*                                                                                     Ad_expression_desc_Da *)
(*                                                                                     Ad_Pexp_constant_Da *)
(*                                                                                     [ *)
(*                                                                                       process_generic_type *)
(*                                                                                         Ad_constant_Da *)
(*                                                                                         Ad_Pconst_string_Da *)
(*                                                                                         [ *)
(*                                                                                           string_value *)
(*                                                                                             Ad_Da, *)
(*                                                                                           process_string_option *)
(*                                                                                         ] *)
(*                                                                                     ]) *)
(*                                                                               ] *)
(*                                                                           ]), *)
(*                                                                       process_arg_label_expression *)
(*                                                                         (process_generic_type *)
(*                                                                           Ad_arg_label_Da *)
(*                                                                           Ad_Nolabel_Da *)
(*                                                                           Ad_None) *)
(*                                                                         (process_generic_type *)
(*                                                                           Ad_expression_desc_Da *)
(*                                                                           Ad_Pexp_apply_Da *)
(*                                                                           [ *)
(*                                                                             process_generic_type *)
(*                                                                               Ad_expression_desc_Da *)
(*                                                                               Ad_Pexp_ident_Da *)
(*                                                                               [ *)
(*                                                                                 ident *)
(*                                                                                   Ad_caret *)
(*                                                                               ], *)
(*                                                                             process_arg_label_expression_list *)
(*                                                                               [ *)
(*                                                                                 process_arg_label_expression *)
(*                                                                                   (process_generic_type *)
(*                                                                                     Ad_arg_label_Da *)
(*                                                                                     Ad_Nolabel_Da *)
(*                                                                                     Ad_None) *)
(*                                                                                   (process_generic_type *)
(*                                                                                     Ad_expression_desc_Da *)
(*                                                                                     Ad_Pexp_apply_Da *)
(*                                                                                     [ *)
(*                                                                                       process_generic_type *)
(*                                                                                         Ad_expression_desc_Da *)
(*                                                                                         Ad_Pexp_ident_Da *)
(*                                                                                         [ *)
(*                                                                                           ident *)
(*                                                                                             Ad_process_params_Da *)
(*                                                                                         ], *)
(*                                                                                       process_arg_label_expression_list *)
(*                                                                                         [ *)
(*                                                                                           process_arg_label_expression *)
(*                                                                                             (process_generic_type *)
(*                                                                                               Ad_arg_label_Da *)
(*                                                                                               Ad_Nolabel_Da *)
(*                                                                                               Ad_None) *)
(*                                                                                             (process_generic_type *)
(*                                                                                               Ad_expression_desc_Da *)
(*                                                                                               Ad_Pexp_construct_Da *)
(*                                                                                               [ *)
(*                                                                                                 ident *)
(*                                                                                                   Ad_empty_list, *)
(*                                                                                                 none *)
(*                                                                                               ]) *)
(*                                                                                         ] *)
(*                                                                                     ]), *)
(*                                                                                 process_arg_label_expression *)
(*                                                                                   (process_generic_type *)
(*                                                                                     Ad_arg_label_Da *)
(*                                                                                     Ad_Nolabel_Da *)
(*                                                                                     Ad_None) *)
(*                                                                                   (process_generic_type *)
(*                                                                                     Ad_expression_desc_Da *)
(*                                                                                     Ad_Pexp_apply_Da *)
(*                                                                                     [ *)
(*                                                                                       process_generic_type *)
(*                                                                                         Ad_expression_desc_Da *)
(*                                                                                         Ad_Pexp_ident_Da *)
(*                                                                                         [ *)
(*                                                                                           ident *)
(*                                                                                             Ad_caret *)
(*                                                                                         ], *)
(*                                                                                       process_arg_label_expression_list *)
(*                                                                                         [ *)
(*                                                                                           process_arg_label_expression *)
(*                                                                                             (process_generic_type *)
(*                                                                                               Ad_arg_label_Da *)
(*                                                                                               Ad_Nolabel_Da *)
(*                                                                                               Ad_None) *)
(*                                                                                             (process_generic_type *)
(*                                                                                               Ad_expression_desc_Da *)
(*                                                                                               Ad_Pexp_apply_Da *)
(*                                                                                               [ *)
(*                                                                                                 process_generic_type *)
(*                                                                                                   Ad_expression_desc_Da *)
(*                                                                                                   Ad_Pexp_ident_Da *)
(*                                                                                                   [ *)
(*                                                                                                     ident *)
(*                                                                                                       Ad_process_cstrs_Da *)
(*                                                                                                   ], *)
(*                                                                                                 process_arg_label_expression_list *)
(*                                                                                                   [ *)
(*                                                                                                     process_arg_label_expression *)
(*                                                                                                       (process_generic_type *)
(*                                                                                                         Ad_arg_label_Da *)
(*                                                                                                         Ad_Nolabel_Da *)
(*                                                                                                         Ad_None) *)
(*                                                                                                       (process_generic_type *)
(*                                                                                                         Ad_expression_desc_Da *)
(*                                                                                                         Ad_Pexp_construct_Da *)
(*                                                                                                         [ *)
(*                                                                                                           ident *)
(*                                                                                                             Ad_empty_list, *)
(*                                                                                                           none *)
(*                                                                                                         ]) *)
(*                                                                                                   ] *)
(*                                                                                               ]), *)
(*                                                                                           process_arg_label_expression *)
(*                                                                                             (process_generic_type *)
(*                                                                                               Ad_arg_label_Da *)
(*                                                                                               Ad_Nolabel_Da *)
(*                                                                                               Ad_None) *)
(*                                                                                             (process_generic_type *)
(*                                                                                               Ad_expression_desc_Da *)
(*                                                                                               Ad_Pexp_apply_Da *)
(*                                                                                               [ *)
(*                                                                                                 process_generic_type *)
(*                                                                                                   Ad_expression_desc_Da *)
(*                                                                                                   Ad_Pexp_ident_Da *)
(*                                                                                                   [ *)
(*                                                                                                     ident *)
(*                                                                                                       Ad_caret *)
(*                                                                                                   ], *)
(*                                                                                                 process_arg_label_expression_list *)
(*                                                                                                   [ *)
(*                                                                                                     process_arg_label_expression *)
(*                                                                                                       (process_generic_type *)
(*                                                                                                         Ad_arg_label_Da *)
(*                                                                                                         Ad_Nolabel_Da *)
(*                                                                                                         Ad_None) *)
(*                                                                                                       (process_generic_type *)
(*                                                                                                         Ad_expression_desc_Da *)
(*                                                                                                         Ad_Pexp_apply_Da *)
(*                                                                                                         [ *)
(*                                                                                                           process_generic_type *)
(*                                                                                                             Ad_expression_desc_Da *)
(*                                                                                                             Ad_Pexp_ident_Da *)
(*                                                                                                             [ *)
(*                                                                                                               ident *)
(*                                                                                                                 Ad_process_generic_type_Da *)
(*                                                                                                             ], *)
(*                                                                                                           process_arg_label_expression_list *)
(*                                                                                                             [ *)
(*                                                                                                               process_arg_label_expression *)
(*                                                                                                                 (process_generic_type *)
(*                                                                                                                   Ad_arg_label_Da *)
(*                                                                                                                   Ad_Nolabel_Da *)
(*                                                                                                                   Ad_None) *)
(*                                                                                                                 (process_generic_type *)
(*                                                                                                                   Ad_expression_desc_Da *)
(*                                                                                                                   Ad_Pexp_constant_Da *)
(*                                                                                                                   [ *)
(*                                                                                                                     process_generic_type *)
(*                                                                                                                       Ad_constant_Da *)
(*                                                                                                                       Ad_Pconst_string_Da *)
(*                                                                                                                       [ *)
(*                                                                                                                         string_value *)
(*                                                                                                                           Ad_type_kind_Da, *)
(*                                                                                                                         process_string_option *)
(*                                                                                                                       ] *)
(*                                                                                                                   ]), *)
(*                                                                                                               process_arg_label_expression *)
(*                                                                                                                 (process_generic_type *)
(*                                                                                                                   Ad_arg_label_Da *)
(*                                                                                                                   Ad_Nolabel_Da *)
(*                                                                                                                   Ad_None) *)
(*                                                                                                                 (process_generic_type *)
(*                                                                                                                   Ad_expression_desc_Da *)
(*                                                                                                                   Ad_Pexp_constant_Da *)
(*                                                                                                                   [ *)
(*                                                                                                                     process_generic_type *)
(*                                                                                                                       Ad_constant_Da *)
(*                                                                                                                       Ad_Pconst_string_Da *)
(*                                                                                                                       [ *)
(*                                                                                                                         string_value *)
(*                                                                                                                           Ad_Ptype_abstract_Da, *)
(*                                                                                                                         process_string_option *)
(*                                                                                                                       ] *)
(*                                                                                                                   ]), *)
(*                                                                                                               process_arg_label_expression *)
(*                                                                                                                 (process_generic_type *)
(*                                                                                                                   Ad_arg_label_Da *)
(*                                                                                                                   Ad_Nolabel_Da *)
(*                                                                                                                   Ad_None) *)
(*                                                                                                                 (process_generic_type *)
(*                                                                                                                   Ad_expression_desc_Da *)
(*                                                                                                                   Ad_Pexp_construct_Da *)
(*                                                                                                                   [ *)
(*                                                                                                                     ident *)
(*                                                                                                                       Ad_empty_list, *)
(*                                                                                                                     none *)
(*                                                                                                                   ]) *)
(*                                                                                                             ] *)
(*                                                                                                         ]), *)
(*                                                                                                     process_arg_label_expression *)
(*                                                                                                       (process_generic_type *)
(*                                                                                                         Ad_arg_label_Da *)
(*                                                                                                         Ad_Nolabel_Da *)
(*                                                                                                         Ad_None) *)
(*                                                                                                       (process_generic_type *)
(*                                                                                                         Ad_expression_desc_Da *)
(*                                                                                                         Ad_Pexp_apply_Da *)
(*                                                                                                         [ *)
(*                                                                                                           process_generic_type *)
(*                                                                                                             Ad_expression_desc_Da *)
(*                                                                                                             Ad_Pexp_ident_Da *)
(*                                                                                                             [ *)
(*                                                                                                               ident *)
(*                                                                                                                 Ad_caret *)
(*                                                                                                             ], *)
(*                                                                                                           process_arg_label_expression_list *)
(*                                                                                                             [ *)
(*                                                                                                               process_arg_label_expression *)
(*                                                                                                                 (process_generic_type *)
(*                                                                                                                   Ad_arg_label_Da *)
(*                                                                                                                   Ad_Nolabel_Da *)
(*                                                                                                                   Ad_None) *)
(*                                                                                                                 (process_generic_type *)
(*                                                                                                                   Ad_expression_desc_Da *)
(*                                                                                                                   Ad_Pexp_apply_Da *)
(*                                                                                                                   [ *)
(*                                                                                                                     process_generic_type *)
(*                                                                                                                       Ad_expression_desc_Da *)
(*                                                                                                                       Ad_Pexp_ident_Da *)
(*                                                                                                                       [ *)
(*                                                                                                                         ident *)
(*                                                                                                                           Ad_process_generic_type_Da *)
(*                                                                                                                       ], *)
(*                                                                                                                     process_arg_label_expression_list *)
(*                                                                                                                       [ *)
(*                                                                                                                         process_arg_label_expression *)
(*                                                                                                                           (process_generic_type *)
(*                                                                                                                             Ad_arg_label_Da *)
(*                                                                                                                             Ad_Nolabel_Da *)
(*                                                                                                                             Ad_None) *)
(*                                                                                                                           (process_generic_type *)
(*                                                                                                                             Ad_expression_desc_Da *)
(*                                                                                                                             Ad_Pexp_constant_Da *)
(*                                                                                                                             [ *)
(*                                                                                                                               process_generic_type *)
(*                                                                                                                                 Ad_constant_Da *)
(*                                                                                                                                 Ad_Pconst_string_Da *)
(*                                                                                                                                 [ *)
(*                                                                                                                                   string_value *)
(*                                                                                                                                     Ad_private_flag_Da, *)
(*                                                                                                                                   process_string_option *)
(*                                                                                                                                 ] *)
(*                                                                                                                             ]), *)
(*                                                                                                                         process_arg_label_expression *)
(*                                                                                                                           (process_generic_type *)
(*                                                                                                                             Ad_arg_label_Da *)
(*                                                                                                                             Ad_Nolabel_Da *)
(*                                                                                                                             Ad_None) *)
(*                                                                                                                           (process_generic_type *)
(*                                                                                                                             Ad_expression_desc_Da *)
(*                                                                                                                             Ad_Pexp_constant_Da *)
(*                                                                                                                             [ *)
(*                                                                                                                               process_generic_type *)
(*                                                                                                                                 Ad_constant_Da *)
(*                                                                                                                                 Ad_Pconst_string_Da *)
(*                                                                                                                                 [ *)
(*                                                                                                                                   string_value *)
(*                                                                                                                                     Ad_Public_Da, *)
(*                                                                                                                                   process_string_option *)
(*                                                                                                                                 ] *)
(*                                                                                                                             ]), *)
(*                                                                                                                         process_arg_label_expression *)
(*                                                                                                                           (process_generic_type *)
(*                                                                                                                             Ad_arg_label_Da *)
(*                                                                                                                             Ad_Nolabel_Da *)
(*                                                                                                                             Ad_None) *)
(*                                                                                                                           (process_generic_type *)
(*                                                                                                                             Ad_expression_desc_Da *)
(*                                                                                                                             Ad_Pexp_construct_Da *)
(*                                                                                                                             [ *)
(*                                                                                                                               ident *)
(*                                                                                                                                 Ad_empty_list, *)
(*                                                                                                                               none *)
(*                                                                                                                             ]) *)
(*                                                                                                                       ] *)
(*                                                                                                                   ]), *)
(*                                                                                                               process_arg_label_expression *)
(*                                                                                                                 (process_generic_type *)
(*                                                                                                                   Ad_arg_label_Da *)
(*                                                                                                                   Ad_Nolabel_Da *)
(*                                                                                                                   Ad_None) *)
(*                                                                                                                 (process_generic_type *)
(*                                                                                                                   Ad_expression_desc_Da *)
(*                                                                                                                   Ad_Pexp_apply_Da *)
(*                                                                                                                   [ *)
(*                                                                                                                     process_generic_type *)
(*                                                                                                                       Ad_expression_desc_Da *)
(*                                                                                                                       Ad_Pexp_ident_Da *)
(*                                                                                                                       [ *)
(*                                                                                                                         ident *)
(*                                                                                                                           Ad_process_generic_type_Da *)
(*                                                                                                                       ], *)
(*                                                                                                                     process_arg_label_expression_list *)
(*                                                                                                                       [ *)
(*                                                                                                                         process_arg_label_expression *)
(*                                                                                                                           (process_generic_type *)
(*                                                                                                                             Ad_arg_label_Da *)
(*                                                                                                                             Ad_Nolabel_Da *)
(*                                                                                                                             Ad_None) *)
(*                                                                                                                           (process_generic_type *)
(*                                                                                                                             Ad_expression_desc_Da *)
(*                                                                                                                             Ad_Pexp_constant_Da *)
(*                                                                                                                             [ *)
(*                                                                                                                               process_generic_type *)
(*                                                                                                                                 Ad_constant_Da *)
(*                                                                                                                                 Ad_Pconst_string_Da *)
(*                                                                                                                                 [ *)
(*                                                                                                                                   string_value *)
(*                                                                                                                                     Ad_core_type_desc_Da, *)
(*                                                                                                                                   process_string_option *)
(*                                                                                                                                 ] *)
(*                                                                                                                             ]), *)
(*                                                                                                                         process_arg_label_expression *)
(*                                                                                                                           (process_generic_type *)
(*                                                                                                                             Ad_arg_label_Da *)
(*                                                                                                                             Ad_Nolabel_Da *)
(*                                                                                                                             Ad_None) *)
(*                                                                                                                           (process_generic_type *)
(*                                                                                                                             Ad_expression_desc_Da *)
(*                                                                                                                             Ad_Pexp_constant_Da *)
(*                                                                                                                             [ *)
(*                                                                                                                               process_generic_type *)
(*                                                                                                                                 Ad_constant_Da *)
(*                                                                                                                                 Ad_Pconst_string_Da *)
(*                                                                                                                                 [ *)
(*                                                                                                                                   string_value *)
(*                                                                                                                                     Ad_Ptyp_constr_Da, *)
(*                                                                                                                                   process_string_option *)
(*                                                                                                                                 ] *)
(*                                                                                                                             ]), *)
(*                                                                                                                         process_arg_label_expression *)
(*                                                                                                                           (process_generic_type *)
(*                                                                                                                             Ad_arg_label_Da *)
(*                                                                                                                             Ad_Nolabel_Da *)
(*                                                                                                                             Ad_None) *)
(*                                                                                                                           (process_generic_type *)
(*                                                                                                                             Ad_expression_desc_Da *)
(*                                                                                                                             Ad_Pexp_construct_Da *)
(*                                                                                                                             [ *)
(*                                                                                                                               ident *)
(*                                                                                                                                 Ad_::_Da, *)
(*                                                                                                                               process_generic_type *)
(*                                                                                                                                 Ad_expression_desc_Da *)
(*                                                                                                                                 Ad_Pexp_tuple_Da *)
(*                                                                                                                                 [ *)
(*                                                                                                                                   process_expression_list *)
(*                                                                                                                                     [ *)
(*                                                                                                                                       process_generic_type *)
(*                                                                                                                                         Ad_expression_desc_Da *)
(*                                                                                                                                         Ad_Pexp_apply_Da *)
(*                                                                                                                                         [ *)
(*                                                                                                                                           process_generic_type *)
(*                                                                                                                                             Ad_expression_desc_Da *)
(*                                                                                                                                             Ad_Pexp_ident_Da *)
(*                                                                                                                                             [ *)
(*                                                                                                                                               ident *)
(*                                                                                                                                                 Ad_ident_Da *)
(*                                                                                                                                             ], *)
(*                                                                                                                                           process_arg_label_expression_list *)
(*                                                                                                                                             [ *)
(*                                                                                                                                               process_arg_label_expression *)
(*                                                                                                                                                 (process_generic_type *)
(*                                                                                                                                                   Ad_arg_label_Da *)
(*                                                                                                                                                   Ad_Nolabel_Da *)
(*                                                                                                                                                   Ad_None) *)
(*                                                                                                                                                 (process_generic_type *)
(*                                                                                                                                                   Ad_expression_desc_Da *)
(*                                                                                                                                                   Ad_Pexp_constant_Da *)
(*                                                                                                                                                   [ *)
(*                                                                                                                                                     process_generic_type *)
(*                                                                                                                                                       Ad_constant_Da *)
(*                                                                                                                                                       Ad_Pconst_string_Da *)
(*                                                                                                                                                       [ *)
(*                                                                                                                                                         string_value *)
(*                                                                                                                                                           Ad_Obj.t_Da, *)
(*                                                                                                                                                         process_string_option *)
(*                                                                                                                                                       ] *)
(*                                                                                                                                                   ]) *)
(*                                                                                                                                             ] *)
(*                                                                                                                                         ], *)
(*                                                                                                                                       process_generic_type *)
(*                                                                                                                                         Ad_expression_desc_Da *)
(*                                                                                                                                         Ad_Pexp_construct_Da *)
(*                                                                                                                                         [ *)
(*                                                                                                                                           ident *)
(*                                                                                                                                             Ad_::_Da, *)
(*                                                                                                                                           process_generic_type *)
(*                                                                                                                                             Ad_expression_desc_Da *)
(*                                                                                                                                             Ad_Pexp_tuple_Da *)
(*                                                                                                                                             [ *)
(*                                                                                                                                               process_expression_list *)
(*                                                                                                                                                 [ *)
(*                                                                                                                                                   process_generic_type *)
(*                                                                                                                                                     Ad_expression_desc_Da *)
(*                                                                                                                                                     Ad_Pexp_apply_Da *)
(*                                                                                                                                                     [ *)
(*                                                                                                                                                       process_generic_type *)
(*                                                                                                                                                         Ad_expression_desc_Da *)
(*                                                                                                                                                         Ad_Pexp_ident_Da *)
(*                                                                                                                                                         [ *)
(*                                                                                                                                                           ident *)
(*                                                                                                                                                             Ad_process_core_type_list_Da *)
(*                                                                                                                                                         ], *)
(*                                                                                                                                                       process_arg_label_expression_list *)
(*                                                                                                                                                         [ *)
(*                                                                                                                                                           process_arg_label_expression *)
(*                                                                                                                                                             (process_generic_type *)
(*                                                                                                                                                               Ad_arg_label_Da *)
(*                                                                                                                                                               Ad_Nolabel_Da *)
(*                                                                                                                                                               Ad_None) *)
(*                                                                                                                                                             (process_generic_type *)
(*                                                                                                                                                               Ad_expression_desc_Da *)
(*                                                                                                                                                               Ad_Pexp_construct_Da *)
(*                                                                                                                                                               [ *)
(*                                                                                                                                                                 ident *)
(*                                                                                                                                                                   Ad_empty_list, *)
(*                                                                                                                                                                 none *)
(*                                                                                                                                                               ]) *)
(*                                                                                                                                                         ] *)
(*                                                                                                                                                     ], *)
(*                                                                                                                                                   process_generic_type *)
(*                                                                                                                                                     Ad_expression_desc_Da *)
(*                                                                                                                                                     Ad_Pexp_construct_Da *)
(*                                                                                                                                                     [ *)
(*                                                                                                                                                       ident *)
(*                                                                                                                                                         Ad_empty_list, *)
(*                                                                                                                                                       none *)
(*                                                                                                                                                     ] *)
(*                                                                                                                                                 ] *)
(*                                                                                                                                             ] *)
(*                                                                                                                                         ] *)
(*                                                                                                                                     ] *)
(*                                                                                                                                 ] *)
(*                                                                                                                             ]) *)
(*                                                                                                                       ] *)
(*                                                                                                                   ]) *)
(*                                                                                                             ] *)
(*                                                                                                         ]) *)
(*                                                                                                   ] *)
(*                                                                                               ]) *)
(*                                                                                         ] *)
(*                                                                                     ]) *)
(*                                                                               ] *)
(*                                                                           ]) *)
(*                                                                     ] *)
(*                                                                 ], *)
(*                                                               process_generic_type *)
(*                                                                 Ad_expression_desc_Da *)
(*                                                                 Ad_Pexp_construct_Da *)
(*                                                                 [ *)
(*                                                                   ident *)
(*                                                                     Ad_empty_list, *)
(*                                                                   none *)
(*                                                                 ] *)
(*                                                             ] *)
(*                                                         ] *)
(*                                                     ]) *)
(*                                               ] *)
(*                                           ], *)
(*                                         process_generic_type *)
(*                                           Ad_expression_desc_Da *)
(*                                           Ad_Pexp_construct_Da *)
(*                                           [ *)
(*                                             ident *)
(*                                               Ad_empty_list, *)
(*                                             none *)
(*                                           ] *)
(*                                       ] *)
(*                                   ] *)
(*                               ] *)
(*                           ] *)
(*                       ] *)
(*                   ]) *)
(*             ] *)
(*         ] *)
(*     ]. *)

End WithUniMath .

(*
: compare Universes.ContextSet.subsetP All_Forall.All2_fold_app_inv
  ctx_inst_impl All_Forall.All2_apply_dep_All All_Forall.OnOne2All_split
  All_Forall.OnOne2All_ind_l All_Forall.OnOne2All_exist
  MCRelations.clos_rt_t_incl CRelationClasses.PartialOrder_inverse
  Lists.foldr1_foldr1_map on_wf_global_env_impl_config
  All_Forall.Alli_All_mix MCRelations.clos_t_rt_incl
  All_Forall.All2_map2_left_All3 All_Forall.All2_mix_inv fold_rec_bis
  All_Forall.OnOne2i_impl_exist_and_All_r All_Forall.All_remove_last
  MCReflect.equiv_reflectT All_Forall.forallb_All cardinal_inv_2b
  All_Forall.All2_map_right_equiv All_Forall.All2_reflexivity
  List.Forall_rect All_Forall.All2_map_inv MCList.rev_ind PeanoNat.Nat.OddT_2
  PeanoNat.Nat.OddT_1 fold_rec_nodep dirprod_hSet_subproof
  All_Forall.All2_right_triv univ_surj_unique infer_sort_impl
  All_Forall.All2_fold_All_fold_mix_left
  Universes.is_not_prop_and_is_not_sprop
  All_Forall.All2_fold_All_fold_mix_right MCList.list_rect_rev
  All_Forall.All2_fold_All_fold_mix_left_inv All_Forall.OnOne2i_nth_error_r
  All_Forall.All_fold_prod All_Forall.All_fold_impl natgthtogthm1
  natgthtogehm1 All_Forall.OnOne2_sym All_Forall.OnOne2_map
  All_Forall.OnOne2_app All_Forall.All2i_app_inv
  All_Forall.All2_from_nth_error strictly_extends_decls_part_trans
  All_Forall.All2i_All_mix_right All_Forall.map_eq_inj
  All_Forall.All2i_len_impl All_Forall.Alli_rev_nth_error
  MCRelations.flip_Symmetric All_Forall.All2_nth_error_Some
  All_Forall.OnOne2_nth_error All_Forall.All2_All_left_pack
  on_global_env_impl_config ByteCompareSpec.reflect_equiv
  All_Forall.All_safe_nth All_Forall.All2_map2_right List.nth_in_or_default
  Universes.cuniv_sup_not_uproplevel All_Forall.All1_map2_right
  MCRelations.clos_rt_trans CRelationClasses.partial_order_antisym
  CRelationClasses.flip_PreOrder All_Forall.allbiP
  All_Forall.All_All2_swap_sum MCOption.nth_map_option_out
  extends_decls_part_refl All_Forall.All_map_inv All_Forall.All_map_All
  extends_decls_part_globals_trans
Ast.predicate_eq_dec
  All_Forall.All2_fold_app_inv_l All_Forall.Alli_shift
  All_Forall.All2_impl_In extends_decls_part_globals_refl univ_surj_ax
  MCRelations.relation_equivalence_inclusion All_Forall.All2_trans'
  PeanoNat.Nat.odd_OddT MCRelations.clos_t_rt strictly_extends_decls_trans
  All_Forall.All_Alli_swap_iff All_Forall.In_All
  strictly_extends_decls_extends_part_globals infer_typing_sort_impl
  All_Forall.All3_map_all ctx_inst_impl_gen PeanoNat.Nat.EvenT_OddT_rect
  extends_strictly_on_decls_l_merge
  StandardFiniteSets.partial_sum_slot_subproof Lists.Unnamed_thm3
  Lists.Unnamed_thm2 Lists.Unnamed_thm1 Lists.Unnamed_thm0
  All_Forall.All2_firstn CRelationClasses.relation_implication_preorder
  All_Forall.alli_Alli MCRelations.clos_t_rt_equiv
  All_Forall.All_fold_All2_fold_impl All_Forall.All2_All_mix_right
  All_Forall.OnOne2All_impl_exist_and_All_r
  All_Forall.OnOne2All_impl_exist_and_All All_Forall.All_fold_app_inv
  All_Forall.All_All2_All2_mix Lists.map_cons extends_r_merge
  All_Forall.All_All_All2 All_Forall.All2_apply_arrow
  MCOption.option_extendsT All_Forall.All2i_trivial BasicAst.All2_fold_map
  MCList.snocP MCRelations.clos_refl_trans_prod_r
  MCRelations.clos_refl_trans_prod_l MCRelations.clos_rt_monotone
  String.eqb_spec All_Forall.All_tip All_Forall.All_rev All_Forall.All_mix
  All_Forall.All_map All_Forall.All_app refine_type
  All_Forall.OnOne2_impl_exist_and_All_r All_Forall.Alli_rev
  All_Forall.Alli_mix All_Forall.Alli_app All_Forall.Alli_All
  All_Forall.All_refl All_Forall.All_prod All_Forall.All_pair
  All_Forall.All_mapi All_Forall.All_impl All_Forall.All_eta3
  All_Forall.All_True Zeven.Zsplit2 All_Forall.All_Alli All_Forall.All_All2
  List.exists_last All_Forall.All2_sym All_Forall.All2_rev
  All_Forall.All2_nth All_Forall.All2_mix All_Forall.All2_map
  All_Forall.All2_app All_Forall.All2_All BasicAst.All2_fold_mapi
  Universes.is_prop_and_is_sprop_val_false PeanoNat.Nat.EvenT_S_OddT
  extends_r_merge_globals BasicAst.All2_fold_cst_map
  extends_strictly_on_decls_trans All_Forall.All2_rect_rev
  All_Forall.All2_fold_All_swap All_Forall.All2_fold_All_left cardinal_inv_2
  All_Forall.All_fold_app All_local_env_impl_ind BasicAst.def_eq_dec
  All_Forall.Alli_shiftn_inv All_Forall.All2_All_mix_left
  All_Forall.All2_nth_error_Some_r All_Forall.Alli_nth_error
  All_Forall.forall_nth_error_All StandardFiniteSets.eqtoweqstn_subproof2
  StandardFiniteSets.eqtoweqstn_subproof1
  StandardFiniteSets.eqtoweqstn_subproof0 All_Forall.forall_nth_error_Alli
  All_Forall.forallbP PeanoNat.Nat.OddT_S_EvenT
  All_Forall.OnOne2All_nth_error_r PeanoNat.Nat.Even_EvenT
  MCRelations.clos_rt_trans_Symmetric MCList.nth_nth_error'
  All_Forall.OnOne2All_nth_error_impl Universes.Level.eqb_spec
  BasicAst.All2_fold_impl_onctx All_Forall.All2_prod_inv plus_n_Sm
  All_Forall.All2i_rev_ctx isapropishinh All_Forall.Alli_mapi
  CRelationClasses.flip_Reflexive All_Forall.All2P Lists.foldr1_cons_nil
  BasicAst.fresh_evar_id ReflectEq.eqb_specT All_Forall.All_fold_Alli_rev
  extends_decls_extends All_Forall.forallb_nth' MCReflect.reflect_reflectT
  All_Forall.All_skipn All_Forall.forallb2P All_Forall.Alli_shiftn
  StandardFiniteSets.eqtoweqstn_subproof All_Forall.All2i_rev_ctx_inv
  All_Forall.All2i_rev_ctx_gen type_local_ctx_impl_gen
  CRelationClasses.flip_StrictOrder Lists.foldr1_cons All_Forall.Forall_All
  cstr_respects_variance_impl on_constructor_impl_config_gen
  List.destruct_list strictly_extends_decls_extends_part map_induction_min
  map_induction_max CRelationClasses.relation_equivalence_equivalence
  All_Forall.OnOne2_impl_All_r All_Forall.All2i_All_right
  PeanoNat.Nat.EvenT_OddT_dec Zpower.Zdiv_rest_correct
  All_Forall.All2i_mapi_rec strictly_extends_decls_part_globals_trans
  All_decls_alpha_pb_impl StandardFiniteSets.dualelement_lt
  All_Forall.All_fold_All2_fold All_Forall.All2i_map_right
  Lists.foldr1_map_nil strictly_extends_decls_part_globals_refl
  All_Forall.All2_map_left_equiv extends_strictly_on_decls_extends
  All_Forall.All2_transitivity All_Forall.OnOne2i_impl_exist_and_All
  All_Forall.OnOne2_All2_All2 map_induction
  Environment.Retroknowledge.extendsT Lists.map_nil
  All_Forall.All2i_All2_mix_left All_Forall.OnOne2_impl_exist_and_All
  cardinal_inv_2 MCRelations.relation_disjunction_refl_r
  MCRelations.relation_disjunction_refl_l All_Forall.All3_impl
  All_Forall.All2i_rev All_Forall.All2i_map All_Forall.All2i_app
  All_Forall.All2_symP All_Forall.All2_swap All_Forall.All2_same
  All_Forall.All2_refl All_Forall.All2_mapi All_Forall.All2_impl
  MCRelations.clos_rt_disjunction_right All_Forall.OnOne2i_All_mix_left
  extends_l_merge PeanoNat.Nat.even_EvenT All_Forall.All2_fold_trans
  All_Forall.All2i_nth_hyp strictly_extends_decls_l_merge_globals
  All_Forall.OnOne2All_nth_error All_Forall.All2_fold_nth_r fold_rel fold_rec
  All_Forall.All2_app_inv isweqtoforallpathsUAH
  All_Forall.OnOne2_All_mix_left extends_decls_refl
  All_Forall.All2i_All2_All2 BasicAst.onctxP All_Forall.All2i_Alli_mix_left
  Lists.foldr_cons All_Forall.OnOne2_nth_error_r Lists.foldr1_nil In_dec
  All_Forall.OnOne2All_sym All_Forall.OnOne2All_map All_Forall.OnOne2All_app
  All_Forall.All2i_mapi All_Forall.All2i_impl MCRelations.clos_rt_refl
  All_Forall.All2_symmetry All_Forall.All_nth_error All_Forall.All_repeat
  All_Forall.All1i_Alli_mix_left on_constructors_impl_config_gen
  All_Forall.Alli_app_inv All_Forall.forallbP_cond extends_refl
  Ascii.eqb_spec All_decls_to_alpha All_Forall.All2_undep
  All_Forall.All2_trans All_Forall.All2_skipn All_Forall.All2_right
  All_Forall.All2_eq_eq All_Forall.All2_apply All_Forall.All2_app_r
  All_Forall.All2i_All_left All_Forall.All_forall All_Forall.All_firstn
  ind_respects_variance_impl All_Forall.OnOne2All_All_mix_left
  All_Forall.All2i_nth_impl_gen strictly_extends_decls_refl
  All_Forall.All2_All_right All_Forall.All2_map_left MCOption.option_map_Some
  extends_strictly_on_decls_refl MCRelations.flip_Transitive
  extends_decls_part_trans lift_typing_impl fold_rec_weak
  MCRelations.clos_sym_Symmetric set_induction_min set_induction_max
  sorts_local_ctx_impl PeanoNat.Nat.OddT_EvenT_rect All_Forall.All2i_len_rev
  All_Forall.All2i_len_app MCReflect.reflectT_reflect
  All_Forall.All2_map_right All_Forall.All2_map_equiv
  All_Forall.forallb2_All2 All_Forall.Alli_rev_All_fold extends_trans
  Zeven.Z_modulo_2 All_Forall.All_All2_fold_swap_sum MCList.rev_case
  lift_judgment_impl Lists.foldr1_map_cons isaset_set_fun_space
  All_Forall.All2_fold_from_nth_error MCList.nth_error_spec
  MCOption.reflect_option_default BasicAst.ondeclP
  CRelationClasses.flip_Antisymmetric All_Forall.All2i_All_mix_left
  All_Forall.OnOne2_All_All fold_rel fold_rec All_Forall.OnOne2i_nth_error
  declared_ind_declared_constructors All_Forall.All_All2_fold_swap
  All_Forall.OnOne2i_mapP All_Forall.OnOne2i_impl extends_l_merge_globals
  CRelationClasses.flip_PER In_dec All_Forall.All2_apply_dep_arrow
  ZArith_dec.Z_notzerop cstr_respects_variance_impl_gen
  All_Forall.All2_map2_left MCRelations.clos_rt_disjunction_left
  set_induction StandardFiniteSets.stn_eq All_Forall.OnOne2_split
  All_Forall.OnOne2_ind_l All_Forall.OnOne2_exist All_Forall.OnOne2_app_r
  All_Forall.All2_map2_right_inv All_Forall.Forall2_All2
  CRelationClasses.flip_Equivalence All_local_env_impl All_local_env_fold
  MCReflect.elimT All_Forall.All2_All_swap All_Forall.All2_All_left
  All_Forall.All2_All2_mix All_Forall.OnOne2i_sym All_Forall.OnOne2i_map
  All_Forall.OnOne2i_app Lists.foldr_nil All_Forall.OnOne2_mapP
  All_Forall.OnOne2_impl strictly_extends_decls_extends_decls
  All_Forall.All1_map2_right_inv All_Forall.All2i_app_inv_r
  All_Forall.All2i_app_inv_l All_Forall.OnOne2All_map_all
  All_Forall.OnOne2All_mapP All_Forall.OnOne2All_impl
  All_Forall.OnOne2All_All3 All_Forall.nth_error_alli
  All_Forall.All2i_map2_right set_induction_bis sorts_local_ctx_impl_gen
  ZArith_dec.Z_noteq_dec All_decls_alpha_impl All_Forall.All2_dep_nth_error
  MCOption.on_SomeP MCList.rev_list_ind extends_decls_trans fold_rec_weak
  strictly_extends_decls_part_refl All_Forall.Alli_All_fold
  All_Forall.map_option_Some map_induction_bis All_Forall.All2_fold_All_right
  fold_rec_bis cardinal_inv_2b All_Forall.All2_fold_sym
  All_Forall.All2_fold_nth All_Forall.All2_fold_app Lists.foldr1_map_cons_nil
  on_wf_global_env_impl PeanoNat.Nat.Odd_OddT natgthandplusm
  All_Forall.OnOne2i_split All_Forall.OnOne2i_ind_l All_Forall.OnOne2i_exist
  All_Forall.OnOne2i_app_r fold_rec_nodep All_decls_impl All_local_env_skipn
  All_Forall.All_prod_inv on_variance_impl Universes.ConstraintType.eq_dec
  All_Forall.Alli_rev_inv All_Forall.All2_fold_refl All_Forall.All2_fold_prod
  All_Forall.All2_fold_impl All_Forall.All2_fold_All2
  StandardFiniteSets.weqfromcoprodofstn_eq2
  StandardFiniteSets.weqfromcoprodofstn_eq1
  CRelationClasses.subrelation_symmetric Ast.branch_eq_dec on_global_env_impl
  isaprop_isInjectiveFunction Uint63.ltbP Uint63.lebP Uint63.eqbP
  All_Forall.All2i_nth_error_r All_Forall.All2i_nth_error_l
  BasicAst.eqdec_binder_annot All_Forall.All2_fold_All_fold_mix natchoice0
  All_Forall.All2_impl_All2 MCReflect.reflectT_pred
  MCRelations.flip_Reflexive MCRelations.iffT_l All_Forall.All_impl_All
  All_Forall.All2i_All2_All2i_All2i All_Forall.All2_nth_error_Some_right
  type_local_ctx_impl All_Forall.OnOne2All_All2_mix_left
  All_Forall.All2_fold_prod_inv All_Forall.All2_dep_from_nth_error
  Lists.Unnamed_thm MCList.nth_error_Some' PeanoNat.Nat.EvenT_2
  PeanoNat.Nat.EvenT_0 All_Forall.map_option_out_All MCReflect.reflectT_pred2
  All_Forall.All2_dep_impl All_Forall.All_rev_map All_Forall.All_rev_inv
  StandardFiniteSets.dualelement_0_empty All_Forall.All_All2_swap
  All_Forall.All_All2_refl All_Forall.All_All2_flex
  strictly_extends_decls_extends_strictly_on_decls
  All_Forall.All1i_map2_right MCRelations.relation_disjunction_Symmetric
  epiissurjectiontosets minusminusmmn All_Forall.OnOne2All_impl_All_r
  All_Forall.All2_fold_All_fold_mix_inv All_Forall.All2_fold_impl_len
  All_Forall.All2_fold_impl_ind MCReflect.reflectT_subrelation'
  All_Forall.All2_app_inv_r All_Forall.All2_app_inv_l.

 *)

From MetaCoq.Utils Require Import utils.
From MetaCoq.Template Require Import All.


MetaCoq Quote Recursively Definition ref_air := Datatypes.pair.
(* MetaCoq Test Quote Recursively Definition tConst. *)
(* MetaCoq Test Quote  Recursively MPfile. *)
(* MetaCoq Test Quote  Recursively tApp. *)
(* MetaCoq Test Quote  Recursively Datatypes.S. *)
(* MetaCoq Test Quote  Recursively tConstruct. *)
(* MetaCoq Test Quote  Recursively inductive_mind. *)
(* MetaCoq Test Quote  Recursively MetaCoq.Template.Ast.term. *)
(* MetaCoq Test Quote  Recursively MetaCoq.Common.Kernames.modpath. *)
(* MetaCoq Test Quote  Recursively Datatypes.O. *)
(* MetaCoq Test Quote  Recursively Datatypes.S. *)
(* MetaCoq Test Quote  Recursively Coq.Init.Datatypes.nat. *)

(* (tConst *)
(*    (Datatypes.pair (MPfile ["Ast"; "Template"; "MetaCoq"]) "predicate_eq_dec") *)
(*    []) *)
(* (tApp *)
(*    (tConst *)
(*       (Datatypes.pair (MPfile ["BasicAst"; "Common"; "MetaCoq"]) *)
(*          "All2_fold_map") []) *)
(*    [tEvar *)
(*       (Datatypes.S *)
(*          (Datatypes.S *)
(*             (Datatypes.S *)
(*                (Datatypes.S *)
(*                   (Datatypes.S *)
(*                      (Datatypes.S *)
(*                         (Datatypes.S *)
(*                            (Datatypes.S *)
(*                               (Datatypes.S *)
(*                                  (Datatypes.S *)
(*                                     (Datatypes.S *)
(*                                        (Datatypes.S *)
(*                                           (Datatypes.S *)
(*                                              (Datatypes.S *)
(*                                                 (Datatypes.S *)
(*                                                  (Datatypes.S *)
(*                                                  (Datatypes.S *)
(*                                                  (Datatypes.S *)
(*                                                  (Datatypes.S *)
(*                                                  (Datatypes.S *)
(*                                                  (Datatypes.S (...)))))))))))))))))))))) *)
(*       []; *)

(* MetaCoq Test Quote  Recursively  Ast.predicate_eq_dec. *)
(* MetaCoq Test Quote BasicAst.All2_fold_map. *)
(* MetaCoq Test Quote BasicAst.All2_fold_mapi. *)
(* MetaCoq Test Quote BasicAst.All2_fold_cst_map. *)
(* MetaCoq Test Quote BasicAst.All2_fold_impl_onctx. *)
(* MetaCoq Test Quote BasicAst.fresh_evar_id. *)
(* MetaCoq Test Quote BasicAst.onctxP . *)
(* MetaCoq Test Quote BasicAst.ondeclP. *)
(* MetaCoq Test Quote MyUU. *)
(* MetaCoq Test Quote Ast.branch_eq_dec. *)
(* MetaCoq Test Quote BasicAst.eqdec_binder_annot. *)

MetaCoq Quote  Recursively Definition reifMyUU := MyUU.
Print reifMyUU.

(* Definition process_ref x := x. *)
  (* match x.declarations with *)
  (* | a =>   a *)
  (* end. *)

(* Definition process_ref2 := process_ref reifMyUU.
Print process_ref2.
 *)








Recursive Extraction Library  All.
