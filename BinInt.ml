open BinNat
open BinNums
open BinPos
open Bool
open Datatypes
open DecidableClass
open Decimal
open Hexadecimal
open Number
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Z =
 struct
  type t = coq_Z

  (** val zero : coq_Z **)

  let zero =
    Z0

  (** val one : coq_Z **)

  let one =
    Zpos Coq_xH

  (** val two : coq_Z **)

  let two =
    Zpos (Coq_xO Coq_xH)

  (** val double : coq_Z -> coq_Z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (Coq_xO p)
  | Zneg p -> Zneg (Coq_xO p)

  (** val succ_double : coq_Z -> coq_Z **)

  let succ_double = function
  | Z0 -> Zpos Coq_xH
  | Zpos p -> Zpos (Coq_xI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : coq_Z -> coq_Z **)

  let pred_double = function
  | Z0 -> Zneg Coq_xH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (Coq_xI p)

  (** val pos_sub : positive -> positive -> coq_Z **)

  let rec pos_sub x y =
    match x with
    | Coq_xI p ->
      (match y with
       | Coq_xI q -> double (pos_sub p q)
       | Coq_xO q -> succ_double (pos_sub p q)
       | Coq_xH -> Zpos (Coq_xO p))
    | Coq_xO p ->
      (match y with
       | Coq_xI q -> pred_double (pos_sub p q)
       | Coq_xO q -> double (pos_sub p q)
       | Coq_xH -> Zpos (Pos.pred_double p))
    | Coq_xH ->
      (match y with
       | Coq_xI q -> Zneg (Coq_xO q)
       | Coq_xO q -> Zneg (Pos.pred_double q)
       | Coq_xH -> Z0)

  (** val add : coq_Z -> coq_Z -> coq_Z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : coq_Z -> coq_Z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val succ : coq_Z -> coq_Z **)

  let succ x =
    add x (Zpos Coq_xH)

  (** val pred : coq_Z -> coq_Z **)

  let pred x =
    add x (Zneg Coq_xH)

  (** val sub : coq_Z -> coq_Z -> coq_Z **)

  let sub m n =
    add m (opp n)

  (** val mul : coq_Z -> coq_Z -> coq_Z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val pow_pos : coq_Z -> positive -> coq_Z **)

  let pow_pos z =
    Pos.iter (mul z) (Zpos Coq_xH)

  (** val pow : coq_Z -> coq_Z -> coq_Z **)

  let pow x = function
  | Z0 -> Zpos Coq_xH
  | Zpos p -> pow_pos x p
  | Zneg _ -> Z0

  (** val square : coq_Z -> coq_Z **)

  let square = function
  | Z0 -> Z0
  | Zpos p -> Zpos (Pos.square p)
  | Zneg p -> Zpos (Pos.square p)

  (** val compare : coq_Z -> coq_Z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> coq_CompOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val sgn : coq_Z -> coq_Z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos Coq_xH
  | Zneg _ -> Zneg Coq_xH

  (** val leb : coq_Z -> coq_Z -> bool **)

  let leb x y =
    match compare x y with
    | Gt -> Coq_false
    | _ -> Coq_true

  (** val ltb : coq_Z -> coq_Z -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> Coq_true
    | _ -> Coq_false

  (** val geb : coq_Z -> coq_Z -> bool **)

  let geb x y =
    match compare x y with
    | Lt -> Coq_false
    | _ -> Coq_true

  (** val gtb : coq_Z -> coq_Z -> bool **)

  let gtb x y =
    match compare x y with
    | Gt -> Coq_true
    | _ -> Coq_false

  (** val eqb : coq_Z -> coq_Z -> bool **)

  let eqb x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Coq_true
             | _ -> Coq_false)
    | Zpos p -> (match y with
                 | Zpos q -> Pos.eqb p q
                 | _ -> Coq_false)
    | Zneg p -> (match y with
                 | Zneg q -> Pos.eqb p q
                 | _ -> Coq_false)

  (** val max : coq_Z -> coq_Z -> coq_Z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val min : coq_Z -> coq_Z -> coq_Z **)

  let min n m =
    match compare n m with
    | Gt -> m
    | _ -> n

  (** val abs : coq_Z -> coq_Z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val abs_nat : coq_Z -> nat **)

  let abs_nat = function
  | Z0 -> O
  | Zpos p -> Pos.to_nat p
  | Zneg p -> Pos.to_nat p

  (** val abs_N : coq_Z -> coq_N **)

  let abs_N = function
  | Z0 -> N0
  | Zpos p -> Npos p
  | Zneg p -> Npos p

  (** val to_nat : coq_Z -> nat **)

  let to_nat = function
  | Zpos p -> Pos.to_nat p
  | _ -> O

  (** val to_N : coq_Z -> coq_N **)

  let to_N = function
  | Zpos p -> Npos p
  | _ -> N0

  (** val of_nat : nat -> coq_Z **)

  let of_nat = function
  | O -> Z0
  | S n0 -> Zpos (Pos.of_succ_nat n0)

  (** val of_N : coq_N -> coq_Z **)

  let of_N = function
  | N0 -> Z0
  | Npos p -> Zpos p

  (** val to_pos : coq_Z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> Coq_xH

  (** val of_uint : Decimal.uint -> coq_Z **)

  let of_uint d =
    of_N (Pos.of_uint d)

  (** val of_hex_uint : Hexadecimal.uint -> coq_Z **)

  let of_hex_uint d =
    of_N (Pos.of_hex_uint d)

  (** val of_num_uint : uint -> coq_Z **)

  let of_num_uint = function
  | UIntDecimal d0 -> of_uint d0
  | UIntHexadecimal d0 -> of_hex_uint d0

  (** val of_int : Decimal.signed_int -> coq_Z **)

  let of_int = function
  | Decimal.Pos d0 -> of_uint d0
  | Decimal.Neg d0 -> opp (of_uint d0)

  (** val of_hex_int : Hexadecimal.signed_int -> coq_Z **)

  let of_hex_int = function
  | Pos d0 -> of_hex_uint d0
  | Neg d0 -> opp (of_hex_uint d0)

  (** val of_num_int : signed_int -> coq_Z **)

  let of_num_int = function
  | IntDecimal d0 -> of_int d0
  | IntHexadecimal d0 -> of_hex_int d0

  (** val to_int : coq_Z -> Decimal.signed_int **)

  let to_int = function
  | Z0 -> Decimal.Pos (Decimal.D0 Decimal.Nil)
  | Zpos p -> Decimal.Pos (Pos.to_uint p)
  | Zneg p -> Decimal.Neg (Pos.to_uint p)

  (** val to_hex_int : coq_Z -> Hexadecimal.signed_int **)

  let to_hex_int = function
  | Z0 -> Pos (D0 Nil)
  | Zpos p -> Pos (Pos.to_hex_uint p)
  | Zneg p -> Neg (Pos.to_hex_uint p)

  (** val to_num_int : coq_Z -> signed_int **)

  let to_num_int n =
    IntDecimal (to_int n)

  (** val to_num_hex_int : coq_Z -> signed_int **)

  let to_num_hex_int n =
    IntHexadecimal (to_hex_int n)

  (** val iter : coq_Z -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let iter n f x =
    match n with
    | Zpos p -> Pos.iter f x p
    | _ -> x

  (** val pos_div_eucl : positive -> coq_Z -> (coq_Z, coq_Z) prod **)

  let rec pos_div_eucl a b =
    match a with
    | Coq_xI a' ->
      let Coq_pair (q, r) = pos_div_eucl a' b in
      let r' = add (mul (Zpos (Coq_xO Coq_xH)) r) (Zpos Coq_xH) in
      (match ltb r' b with
       | Coq_true -> Coq_pair ((mul (Zpos (Coq_xO Coq_xH)) q), r')
       | Coq_false ->
         Coq_pair ((add (mul (Zpos (Coq_xO Coq_xH)) q) (Zpos Coq_xH)),
           (sub r' b)))
    | Coq_xO a' ->
      let Coq_pair (q, r) = pos_div_eucl a' b in
      let r' = mul (Zpos (Coq_xO Coq_xH)) r in
      (match ltb r' b with
       | Coq_true -> Coq_pair ((mul (Zpos (Coq_xO Coq_xH)) q), r')
       | Coq_false ->
         Coq_pair ((add (mul (Zpos (Coq_xO Coq_xH)) q) (Zpos Coq_xH)),
           (sub r' b)))
    | Coq_xH ->
      (match leb (Zpos (Coq_xO Coq_xH)) b with
       | Coq_true -> Coq_pair (Z0, (Zpos Coq_xH))
       | Coq_false -> Coq_pair ((Zpos Coq_xH), Z0))

  (** val div_eucl : coq_Z -> coq_Z -> (coq_Z, coq_Z) prod **)

  let div_eucl a b =
    match a with
    | Z0 -> Coq_pair (Z0, Z0)
    | Zpos a' ->
      (match b with
       | Z0 -> Coq_pair (Z0, a)
       | Zpos _ -> pos_div_eucl a' b
       | Zneg b' ->
         let Coq_pair (q, r) = pos_div_eucl a' (Zpos b') in
         (match r with
          | Z0 -> Coq_pair ((opp q), Z0)
          | _ -> Coq_pair ((opp (add q (Zpos Coq_xH))), (add b r))))
    | Zneg a' ->
      (match b with
       | Z0 -> Coq_pair (Z0, a)
       | Zpos _ ->
         let Coq_pair (q, r) = pos_div_eucl a' b in
         (match r with
          | Z0 -> Coq_pair ((opp q), Z0)
          | _ -> Coq_pair ((opp (add q (Zpos Coq_xH))), (sub b r)))
       | Zneg b' ->
         let Coq_pair (q, r) = pos_div_eucl a' (Zpos b') in
         Coq_pair (q, (opp r)))

  (** val div : coq_Z -> coq_Z -> coq_Z **)

  let div a b =
    let Coq_pair (q, _) = div_eucl a b in q

  (** val modulo : coq_Z -> coq_Z -> coq_Z **)

  let modulo a b =
    let Coq_pair (_, r) = div_eucl a b in r

  (** val quotrem : coq_Z -> coq_Z -> (coq_Z, coq_Z) prod **)

  let quotrem a b =
    match a with
    | Z0 -> Coq_pair (Z0, Z0)
    | Zpos a0 ->
      (match b with
       | Z0 -> Coq_pair (Z0, a)
       | Zpos b0 ->
         let Coq_pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Coq_pair ((of_N q), (of_N r))
       | Zneg b0 ->
         let Coq_pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Coq_pair ((opp (of_N q)), (of_N r)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Coq_pair (Z0, a)
       | Zpos b0 ->
         let Coq_pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Coq_pair ((opp (of_N q)), (opp (of_N r)))
       | Zneg b0 ->
         let Coq_pair (q, r) = N.pos_div_eucl a0 (Npos b0) in
         Coq_pair ((of_N q), (opp (of_N r))))

  (** val quot : coq_Z -> coq_Z -> coq_Z **)

  let quot a b =
    fst (quotrem a b)

  (** val rem : coq_Z -> coq_Z -> coq_Z **)

  let rem a b =
    snd (quotrem a b)

  (** val even : coq_Z -> bool **)

  let even = function
  | Z0 -> Coq_true
  | Zpos p -> (match p with
               | Coq_xO _ -> Coq_true
               | _ -> Coq_false)
  | Zneg p -> (match p with
               | Coq_xO _ -> Coq_true
               | _ -> Coq_false)

  (** val odd : coq_Z -> bool **)

  let odd = function
  | Z0 -> Coq_false
  | Zpos p -> (match p with
               | Coq_xO _ -> Coq_false
               | _ -> Coq_true)
  | Zneg p -> (match p with
               | Coq_xO _ -> Coq_false
               | _ -> Coq_true)

  (** val div2 : coq_Z -> coq_Z **)

  let div2 = function
  | Z0 -> Z0
  | Zpos p -> (match p with
               | Coq_xH -> Z0
               | _ -> Zpos (Pos.div2 p))
  | Zneg p -> Zneg (Pos.div2_up p)

  (** val quot2 : coq_Z -> coq_Z **)

  let quot2 = function
  | Z0 -> Z0
  | Zpos p -> (match p with
               | Coq_xH -> Z0
               | _ -> Zpos (Pos.div2 p))
  | Zneg p -> (match p with
               | Coq_xH -> Z0
               | _ -> Zneg (Pos.div2 p))

  (** val log2 : coq_Z -> coq_Z **)

  let log2 = function
  | Zpos p0 ->
    (match p0 with
     | Coq_xI p -> Zpos (Pos.size p)
     | Coq_xO p -> Zpos (Pos.size p)
     | Coq_xH -> Z0)
  | _ -> Z0

  (** val sqrtrem : coq_Z -> (coq_Z, coq_Z) prod **)

  let sqrtrem = function
  | Zpos p ->
    let Coq_pair (s, m) = Pos.sqrtrem p in
    (match m with
     | Pos.IsPos r -> Coq_pair ((Zpos s), (Zpos r))
     | _ -> Coq_pair ((Zpos s), Z0))
  | _ -> Coq_pair (Z0, Z0)

  (** val sqrt : coq_Z -> coq_Z **)

  let sqrt = function
  | Zpos p -> Zpos (Pos.sqrt p)
  | _ -> Z0

  (** val gcd : coq_Z -> coq_Z -> coq_Z **)

  let gcd a b =
    match a with
    | Z0 -> abs b
    | Zpos a0 ->
      (match b with
       | Z0 -> abs a
       | Zpos b0 -> Zpos (Pos.gcd a0 b0)
       | Zneg b0 -> Zpos (Pos.gcd a0 b0))
    | Zneg a0 ->
      (match b with
       | Z0 -> abs a
       | Zpos b0 -> Zpos (Pos.gcd a0 b0)
       | Zneg b0 -> Zpos (Pos.gcd a0 b0))

  (** val ggcd : coq_Z -> coq_Z -> (coq_Z, (coq_Z, coq_Z) prod) prod **)

  let ggcd a b =
    match a with
    | Z0 -> Coq_pair ((abs b), (Coq_pair (Z0, (sgn b))))
    | Zpos a0 ->
      (match b with
       | Z0 -> Coq_pair ((abs a), (Coq_pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Coq_pair (g, p) = Pos.ggcd a0 b0 in
         let Coq_pair (aa, bb) = p in
         Coq_pair ((Zpos g), (Coq_pair ((Zpos aa), (Zpos bb))))
       | Zneg b0 ->
         let Coq_pair (g, p) = Pos.ggcd a0 b0 in
         let Coq_pair (aa, bb) = p in
         Coq_pair ((Zpos g), (Coq_pair ((Zpos aa), (Zneg bb)))))
    | Zneg a0 ->
      (match b with
       | Z0 -> Coq_pair ((abs a), (Coq_pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Coq_pair (g, p) = Pos.ggcd a0 b0 in
         let Coq_pair (aa, bb) = p in
         Coq_pair ((Zpos g), (Coq_pair ((Zneg aa), (Zpos bb))))
       | Zneg b0 ->
         let Coq_pair (g, p) = Pos.ggcd a0 b0 in
         let Coq_pair (aa, bb) = p in
         Coq_pair ((Zpos g), (Coq_pair ((Zneg aa), (Zneg bb)))))

  (** val testbit : coq_Z -> coq_Z -> bool **)

  let testbit a = function
  | Z0 -> odd a
  | Zpos p ->
    (match a with
     | Z0 -> Coq_false
     | Zpos a0 -> Pos.testbit a0 (Npos p)
     | Zneg a0 -> negb (N.testbit (Pos.pred_N a0) (Npos p)))
  | Zneg _ -> Coq_false

  (** val shiftl : coq_Z -> coq_Z -> coq_Z **)

  let shiftl a = function
  | Z0 -> a
  | Zpos p -> Pos.iter (mul (Zpos (Coq_xO Coq_xH))) a p
  | Zneg p -> Pos.iter div2 a p

  (** val shiftr : coq_Z -> coq_Z -> coq_Z **)

  let shiftr a n =
    shiftl a (opp n)

  (** val coq_lor : coq_Z -> coq_Z -> coq_Z **)

  let coq_lor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zpos (Pos.coq_lor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.ldiff (Pos.pred_N b0) (Npos a0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.ldiff (Pos.pred_N a0) (Npos b0)))
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_land (Pos.pred_N a0) (Pos.pred_N b0))))

  (** val coq_land : coq_Z -> coq_Z -> coq_Z **)

  let coq_land a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (Pos.coq_land a0 b0)
       | Zneg b0 -> of_N (N.ldiff (Npos a0) (Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> Z0
       | Zpos b0 -> of_N (N.ldiff (Npos b0) (Pos.pred_N a0))
       | Zneg b0 ->
         Zneg (N.succ_pos (N.coq_lor (Pos.pred_N a0) (Pos.pred_N b0))))

  (** val ldiff : coq_Z -> coq_Z -> coq_Z **)

  let ldiff a b =
    match a with
    | Z0 -> Z0
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Pos.ldiff a0 b0)
       | Zneg b0 -> of_N (N.coq_land (Npos a0) (Pos.pred_N b0)))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.coq_lor (Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.ldiff (Pos.pred_N b0) (Pos.pred_N a0)))

  (** val coq_lxor : coq_Z -> coq_Z -> coq_Z **)

  let coq_lxor a b =
    match a with
    | Z0 -> b
    | Zpos a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> of_N (Pos.coq_lxor a0 b0)
       | Zneg b0 -> Zneg (N.succ_pos (N.coq_lxor (Npos a0) (Pos.pred_N b0))))
    | Zneg a0 ->
      (match b with
       | Z0 -> a
       | Zpos b0 -> Zneg (N.succ_pos (N.coq_lxor (Pos.pred_N a0) (Npos b0)))
       | Zneg b0 -> of_N (N.coq_lxor (Pos.pred_N a0) (Pos.pred_N b0)))

  (** val eq_dec : coq_Z -> coq_Z -> sumbool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Coq_left
             | _ -> Coq_right)
    | Zpos p -> (match y with
                 | Zpos p0 -> Pos.eq_dec p p0
                 | _ -> Coq_right)
    | Zneg p -> (match y with
                 | Zneg p0 -> Pos.eq_dec p p0
                 | _ -> Coq_right)

  module Private_BootStrap =
   struct
   end

  (** val coq_Decidable_eq_Z : coq_Z -> coq_Z -> coq_Decidable **)

  let coq_Decidable_eq_Z =
    eqb

  (** val coq_Decidable_lt_Z : coq_Z -> coq_Z -> coq_Decidable **)

  let coq_Decidable_lt_Z =
    ltb

  (** val coq_Decidable_le_Z : coq_Z -> coq_Z -> coq_Decidable **)

  let coq_Decidable_le_Z =
    leb

  (** val coq_Decidable_gt_Z : coq_Z -> coq_Z -> coq_Decidable **)

  let coq_Decidable_gt_Z =
    gtb

  (** val coq_Decidable_ge_Z : coq_Z -> coq_Z -> coq_Decidable **)

  let coq_Decidable_ge_Z =
    geb

  (** val leb_spec0 : coq_Z -> coq_Z -> reflect **)

  let leb_spec0 x y =
    iff_reflect (leb x y)

  (** val ltb_spec0 : coq_Z -> coq_Z -> reflect **)

  let ltb_spec0 x y =
    iff_reflect (ltb x y)

  module Private_OrderTac =
   struct
    module IsTotal =
     struct
     end

    module Tac =
     struct
     end
   end

  (** val measure_right_induction :
      ('a1 -> coq_Z) -> coq_Z -> ('a1 -> __ -> ('a1 -> __ -> 'a2) -> 'a2) ->
      'a1 -> 'a2 **)

  let measure_right_induction f _ iH x =
    let t0 = f x in
    let rec f0 _ y =
      iH y __ (fun y' _ -> let y0 = f y' in f0 y0 y')
    in f0 t0 x

  (** val measure_left_induction :
      ('a1 -> coq_Z) -> coq_Z -> ('a1 -> __ -> ('a1 -> __ -> 'a2) -> 'a2) ->
      'a1 -> 'a2 **)

  let measure_left_induction f _ iH x =
    let t0 = f x in
    let rec f0 _ y =
      iH y __ (fun y' _ -> let y0 = f y' in f0 y0 y')
    in f0 t0 x

  module Private_Tac =
   struct
   end

  module Private_Dec =
   struct
    (** val max_case_strong :
        coq_Z -> coq_Z -> (coq_Z -> coq_Z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1)
        -> (__ -> 'a1) -> 'a1 **)

    let max_case_strong n m compat hl hr =
      let c = coq_CompSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))

    (** val max_case :
        coq_Z -> coq_Z -> (coq_Z -> coq_Z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1
        -> 'a1 **)

    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : coq_Z -> coq_Z -> sumbool **)

    let max_dec n m =
      max_case n m (fun _ _ _ h0 -> h0) Coq_left Coq_right

    (** val min_case_strong :
        coq_Z -> coq_Z -> (coq_Z -> coq_Z -> __ -> 'a1 -> 'a1) -> (__ -> 'a1)
        -> (__ -> 'a1) -> 'a1 **)

    let min_case_strong n m compat hl hr =
      let c = coq_CompSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat m (min n m) __ (hr __)
       | _ -> compat n (min n m) __ (hl __))

    (** val min_case :
        coq_Z -> coq_Z -> (coq_Z -> coq_Z -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1
        -> 'a1 **)

    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : coq_Z -> coq_Z -> sumbool **)

    let min_dec n m =
      min_case n m (fun _ _ _ h0 -> h0) Coq_left Coq_right
   end

  (** val max_case_strong :
      coq_Z -> coq_Z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val max_case : coq_Z -> coq_Z -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : coq_Z -> coq_Z -> sumbool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong :
      coq_Z -> coq_Z -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val min_case : coq_Z -> coq_Z -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val min_dec : coq_Z -> coq_Z -> sumbool **)

  let min_dec =
    Private_Dec.min_dec

  (** val sqrt_up : coq_Z -> coq_Z **)

  let sqrt_up a =
    match compare Z0 a with
    | Lt -> succ (sqrt (pred a))
    | _ -> Z0

  (** val log2_up : coq_Z -> coq_Z **)

  let log2_up a =
    match compare (Zpos Coq_xH) a with
    | Lt -> succ (log2 (pred a))
    | _ -> Z0

  module Private_NZDiv =
   struct
   end

  module Private_Div =
   struct
    module Quot2Div =
     struct
      (** val div : coq_Z -> coq_Z -> coq_Z **)

      let div =
        quot

      (** val modulo : coq_Z -> coq_Z -> coq_Z **)

      let modulo =
        rem
     end

    module NZQuot =
     struct
     end
   end

  (** val lcm : coq_Z -> coq_Z -> coq_Z **)

  let lcm a b =
    abs (mul a (div b (gcd a b)))

  (** val eqb_spec : coq_Z -> coq_Z -> reflect **)

  let eqb_spec x y =
    iff_reflect (eqb x y)

  (** val b2z : bool -> coq_Z **)

  let b2z = function
  | Coq_true -> Zpos Coq_xH
  | Coq_false -> Z0

  (** val setbit : coq_Z -> coq_Z -> coq_Z **)

  let setbit a n =
    coq_lor a (shiftl (Zpos Coq_xH) n)

  (** val clearbit : coq_Z -> coq_Z -> coq_Z **)

  let clearbit a n =
    ldiff a (shiftl (Zpos Coq_xH) n)

  (** val lnot : coq_Z -> coq_Z **)

  let lnot a =
    pred (opp a)

  (** val ones : coq_Z -> coq_Z **)

  let ones n =
    pred (shiftl (Zpos Coq_xH) n)
 end

module Pos2Z =
 struct
 end

module Z2Pos =
 struct
 end
