open Preamble

let process_types_coq_unit__Coq_tt :string = "Coq_tt"
    

(* emit_type_decl_kindVARIANT2constructor:Coq_tt
   Coq_tt () -> (process_types_coq_unit__Coq_tt(imp_core_type_list (a,s,0)))}
   |process_type_variant_constructor_declaration_list(p,t,s)}
*)
                                                                       
let process_coq_unit__Coq_tt x :string =match x with 
  | Preamble.Coq_tt -> (process_types_coq_unit__Coq_tt (* imp_core_type_list (a,s,0) *)
    )
   let process_bool__Coq_true x :string =match x with 
    | Coq_true  -> "process_types_bool__Coq_true"
    | Coq_false  -> "process_types_bool__Coq_false"

let process_coprod__Coq_ii1((avar_name0)):string =
  "process_types_coprod__Coq_ii1"^"avar-name0"
  
let process_coprod__Coq_ii1 x :string =match x with 
  | Coq_ii1 (x) -> "process_types_coprod__Coq_ii1" ^ x
                   
let process_nat__O x :string =match x with 
  | O -> "process_types_nat__O"
         
let process_paths__Coq_paths_refl x :string =match x with 
  | Coq_paths_refl  -> "process_types_paths__Coq_paths_refl"

let process_type_decl_FIXME x  = "process_type_decl_FIXME" ^ x
let process_type_decl_total2 (x):string =
  match x with {pr1(* FIXME*);pr2(* FIXME*)} ->(process_type_decl_FIXME pr1)^(process_type_decl_FIXME pr2) 

   
