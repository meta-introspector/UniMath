open Bool
open Datatypes
open DecidableClass
open Decimal
open Hexadecimal
open Number
open Specif

type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

module Nat =
 struct
  type t = nat

  (** val zero : nat **)

  let zero =
    O

  (** val one : nat **)

  let one =
    S O

  (** val two : nat **)

  let two =
    S (S O)

  (** val succ : nat -> nat **)

  let succ x =
    S x

  (** val pred : nat -> nat **)

  let pred n = match n with
  | O -> n
  | S u -> u

  (** val add : nat -> nat -> nat **)

  let rec add n m =
    match n with
    | O -> m
    | S p -> S (add p m)

  (** val double : nat -> nat **)

  let double n =
    add n n

  (** val mul : nat -> nat -> nat **)

  let rec mul n m =
    match n with
    | O -> O
    | S p -> add m (mul p m)

  (** val sub : nat -> nat -> nat **)

  let rec sub n m =
    match n with
    | O -> n
    | S k -> (match m with
              | O -> n
              | S l -> sub k l)

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> Coq_true
            | S _ -> Coq_false)
    | S n' -> (match m with
               | O -> Coq_false
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> Coq_true
    | S n' -> (match m with
               | O -> Coq_false
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m =
    leb (S n) m

  (** val compare : nat -> nat -> comparison **)

  let rec compare n m =
    match n with
    | O -> (match m with
            | O -> Eq
            | S _ -> Lt)
    | S n' -> (match m with
               | O -> Gt
               | S m' -> compare n' m')

  (** val max : nat -> nat -> nat **)

  let rec max n m =
    match n with
    | O -> m
    | S n' -> (match m with
               | O -> n
               | S m' -> S (max n' m'))

  (** val min : nat -> nat -> nat **)

  let rec min n m =
    match n with
    | O -> O
    | S n' -> (match m with
               | O -> O
               | S m' -> S (min n' m'))

  (** val even : nat -> bool **)

  let rec even = function
  | O -> Coq_true
  | S n0 -> (match n0 with
             | O -> Coq_false
             | S n' -> even n')

  (** val odd : nat -> bool **)

  let odd n =
    negb (even n)

  (** val pow : nat -> nat -> nat **)

  let rec pow n = function
  | O -> S O
  | S m0 -> mul n (pow n m0)

  (** val tail_add : nat -> nat -> nat **)

  let rec tail_add n m =
    match n with
    | O -> m
    | S n0 -> tail_add n0 (S m)

  (** val tail_addmul : nat -> nat -> nat -> nat **)

  let rec tail_addmul r n m =
    match n with
    | O -> r
    | S n0 -> tail_addmul (tail_add m r) n0 m

  (** val tail_mul : nat -> nat -> nat **)

  let tail_mul n m =
    tail_addmul O n m

  (** val of_uint_acc : Decimal.uint -> nat -> nat **)

  let rec of_uint_acc d acc =
    match d with
    | Decimal.Nil -> acc
    | Decimal.D0 d0 ->
      of_uint_acc d0 (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)
    | Decimal.D1 d0 ->
      of_uint_acc d0 (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))
    | Decimal.D2 d0 ->
      of_uint_acc d0 (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))
    | Decimal.D3 d0 ->
      of_uint_acc d0 (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))
    | Decimal.D4 d0 ->
      of_uint_acc d0 (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))))
    | Decimal.D5 d0 ->
      of_uint_acc d0 (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))))
    | Decimal.D6 d0 ->
      of_uint_acc d0 (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))))))
    | Decimal.D7 d0 ->
      of_uint_acc d0 (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))))))
    | Decimal.D8 d0 ->
      of_uint_acc d0 (S (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))))))))
    | Decimal.D9 d0 ->
      of_uint_acc d0 (S (S (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))))))))

  (** val of_uint : Decimal.uint -> nat **)

  let of_uint d =
    of_uint_acc d O

  (** val of_hex_uint_acc : Hexadecimal.uint -> nat -> nat **)

  let rec of_hex_uint_acc d acc =
    match d with
    | Nil -> acc
    | D0 d0 ->
      of_hex_uint_acc d0
        (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) acc)
    | D1 d0 ->
      of_hex_uint_acc d0 (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) acc))
    | D2 d0 ->
      of_hex_uint_acc d0 (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) acc)))
    | D3 d0 ->
      of_hex_uint_acc d0 (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) acc))))
    | D4 d0 ->
      of_hex_uint_acc d0 (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) acc)))))
    | D5 d0 ->
      of_hex_uint_acc d0 (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) acc))))))
    | D6 d0 ->
      of_hex_uint_acc d0 (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) acc)))))))
    | D7 d0 ->
      of_hex_uint_acc d0 (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) acc))))))))
    | D8 d0 ->
      of_hex_uint_acc d0 (S (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) acc)))))))))
    | D9 d0 ->
      of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) acc))))))))))
    | Da d0 ->
      of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) acc)))))))))))
    | Db d0 ->
      of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) acc))))))))))))
    | Dc d0 ->
      of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) acc)))))))))))))
    | Dd d0 ->
      of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) acc))))))))))))))
    | De d0 ->
      of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) acc)))))))))))))))
    | Df d0 ->
      of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) acc))))))))))))))))

  (** val of_hex_uint : Hexadecimal.uint -> nat **)

  let of_hex_uint d =
    of_hex_uint_acc d O

  (** val of_num_uint : uint -> nat **)

  let of_num_uint = function
  | UIntDecimal d0 -> of_uint d0
  | UIntHexadecimal d0 -> of_hex_uint d0

  (** val to_little_uint : nat -> Decimal.uint -> Decimal.uint **)

  let rec to_little_uint n acc =
    match n with
    | O -> acc
    | S n0 -> to_little_uint n0 (Decimal.Little.succ acc)

  (** val to_uint : nat -> Decimal.uint **)

  let to_uint n =
    Decimal.rev (to_little_uint n (Decimal.D0 Decimal.Nil))

  (** val to_little_hex_uint : nat -> Hexadecimal.uint -> Hexadecimal.uint **)

  let rec to_little_hex_uint n acc =
    match n with
    | O -> acc
    | S n0 -> to_little_hex_uint n0 (Little.succ acc)

  (** val to_hex_uint : nat -> Hexadecimal.uint **)

  let to_hex_uint n =
    rev (to_little_hex_uint n (D0 Nil))

  (** val to_num_uint : nat -> uint **)

  let to_num_uint n =
    UIntDecimal (to_uint n)

  (** val to_num_hex_uint : nat -> uint **)

  let to_num_hex_uint n =
    UIntHexadecimal (to_hex_uint n)

  (** val of_int : Decimal.signed_int -> nat option **)

  let of_int d =
    match Decimal.norm d with
    | Decimal.Pos u -> Some (of_uint u)
    | Decimal.Neg _ -> None

  (** val of_hex_int : Hexadecimal.signed_int -> nat option **)

  let of_hex_int d =
    match norm d with
    | Pos u -> Some (of_hex_uint u)
    | Neg _ -> None

  (** val of_num_int : signed_int -> nat option **)

  let of_num_int = function
  | IntDecimal d0 -> of_int d0
  | IntHexadecimal d0 -> of_hex_int d0

  (** val to_int : nat -> Decimal.signed_int **)

  let to_int n =
    Decimal.Pos (to_uint n)

  (** val to_hex_int : nat -> Hexadecimal.signed_int **)

  let to_hex_int n =
    Pos (to_hex_uint n)

  (** val to_num_int : nat -> signed_int **)

  let to_num_int n =
    IntDecimal (to_int n)

  (** val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod **)

  let rec divmod x y q u =
    match x with
    | O -> Coq_pair (q, u)
    | S x' ->
      (match u with
       | O -> divmod x' y (S q) y
       | S u' -> divmod x' y q u')

  (** val div : nat -> nat -> nat **)

  let div x y = match y with
  | O -> y
  | S y' -> fst (divmod x y' O y')

  (** val modulo : nat -> nat -> nat **)

  let modulo x = function
  | O -> x
  | S y' -> sub y' (snd (divmod x y' O y'))

  (** val gcd : nat -> nat -> nat **)

  let rec gcd a b =
    match a with
    | O -> b
    | S a' -> gcd (modulo b (S a')) (S a')

  (** val square : nat -> nat **)

  let square n =
    mul n n

  (** val sqrt_iter : nat -> nat -> nat -> nat -> nat **)

  let rec sqrt_iter k p q r =
    match k with
    | O -> p
    | S k' ->
      (match r with
       | O -> sqrt_iter k' (S p) (S (S q)) (S (S q))
       | S r' -> sqrt_iter k' p q r')

  (** val sqrt : nat -> nat **)

  let sqrt n =
    sqrt_iter n O O O

  (** val log2_iter : nat -> nat -> nat -> nat -> nat **)

  let rec log2_iter k p q r =
    match k with
    | O -> p
    | S k' ->
      (match r with
       | O -> log2_iter k' (S p) (S q) q
       | S r' -> log2_iter k' p (S q) r')

  (** val log2 : nat -> nat **)

  let log2 n =
    log2_iter (pred n) O (S O) O

  (** val iter : nat -> ('a1 -> 'a1) -> 'a1 -> 'a1 **)

  let rec iter n f x =
    match n with
    | O -> x
    | S n0 -> f (iter n0 f x)

  (** val div2 : nat -> nat **)

  let rec div2 = function
  | O -> O
  | S n0 -> (match n0 with
             | O -> O
             | S n' -> S (div2 n'))

  (** val testbit : nat -> nat -> bool **)

  let rec testbit a = function
  | O -> odd a
  | S n0 -> testbit (div2 a) n0

  (** val shiftl : nat -> nat -> nat **)

  let rec shiftl a = function
  | O -> a
  | S n0 -> double (shiftl a n0)

  (** val shiftr : nat -> nat -> nat **)

  let rec shiftr a = function
  | O -> a
  | S n0 -> div2 (shiftr a n0)

  (** val bitwise : (bool -> bool -> bool) -> nat -> nat -> nat -> nat **)

  let rec bitwise op n a b =
    match n with
    | O -> O
    | S n' ->
      add (match op (odd a) (odd b) with
           | Coq_true -> S O
           | Coq_false -> O) (mul (S (S O)) (bitwise op n' (div2 a) (div2 b)))

  (** val coq_land : nat -> nat -> nat **)

  let coq_land a b =
    bitwise (fun b1 b2 ->
      match b1 with
      | Coq_true -> b2
      | Coq_false -> Coq_false) a a b

  (** val coq_lor : nat -> nat -> nat **)

  let coq_lor a b =
    bitwise (fun b1 b2 ->
      match b1 with
      | Coq_true -> Coq_true
      | Coq_false -> b2) (max a b) a b

  (** val ldiff : nat -> nat -> nat **)

  let ldiff a b =
    bitwise (fun b0 b' ->
      match b0 with
      | Coq_true -> negb b'
      | Coq_false -> Coq_false) a a b

  (** val coq_lxor : nat -> nat -> nat **)

  let coq_lxor a b =
    bitwise xorb (max a b) a b

  (** val recursion : 'a1 -> (nat -> 'a1 -> 'a1) -> nat -> 'a1 **)

  let rec recursion x f0 = function
  | O -> x
  | S n0 -> f0 n0 (recursion x f0 n0)

  (** val coq_Decidable_eq_nat : nat -> nat -> coq_Decidable **)

  let coq_Decidable_eq_nat =
    eqb

  (** val coq_Decidable_le_nat : nat -> nat -> coq_Decidable **)

  let coq_Decidable_le_nat =
    leb

  (** val eq_dec : nat -> nat -> sumbool **)

  let rec eq_dec n m =
    match n with
    | O -> (match m with
            | O -> Coq_left
            | S _ -> Coq_right)
    | S n0 -> (match m with
               | O -> Coq_right
               | S n1 -> eq_dec n0 n1)

  (** val leb_spec0 : nat -> nat -> reflect **)

  let leb_spec0 x y =
    iff_reflect (leb x y)

  (** val ltb_spec0 : nat -> nat -> reflect **)

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
      ('a1 -> nat) -> nat -> ('a1 -> __ -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1
      -> 'a2 **)

  let measure_right_induction f _ iH x =
    let t0 = f x in
    let rec f0 _ y =
      iH y __ (fun y' _ -> let y0 = f y' in f0 y0 y')
    in f0 t0 x

  (** val measure_left_induction :
      ('a1 -> nat) -> nat -> ('a1 -> __ -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1
      -> 'a2 **)

  let measure_left_induction f _ iH x =
    let t0 = f x in
    let rec f0 _ y =
      iH y __ (fun y' _ -> let y0 = f y' in f0 y0 y')
    in f0 t0 x

  (** val measure_induction :
      ('a1 -> nat) -> ('a1 -> ('a1 -> __ -> 'a2) -> 'a2) -> 'a1 -> 'a2 **)

  let measure_induction f iH x =
    measure_right_induction f O (fun y _ iH' -> iH y (fun y0 _ -> iH' y0 __))
      x

  module Private_Tac =
   struct
   end

  module Private_Dec =
   struct
    (** val max_case_strong :
        nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__
        -> 'a1) -> 'a1 **)

    let max_case_strong n m compat hl hr =
      let c = coq_CompSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat n (max n m) __ (hl __)
       | _ -> compat m (max n m) __ (hr __))

    (** val max_case :
        nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let max_case n m x x0 x1 =
      max_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val max_dec : nat -> nat -> sumbool **)

    let max_dec n m =
      max_case n m (fun _ _ _ h0 -> h0) Coq_left Coq_right

    (** val min_case_strong :
        nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> (__ -> 'a1) -> (__
        -> 'a1) -> 'a1 **)

    let min_case_strong n m compat hl hr =
      let c = coq_CompSpec2Type n m (compare n m) in
      (match c with
       | CompGtT -> compat m (min n m) __ (hr __)
       | _ -> compat n (min n m) __ (hl __))

    (** val min_case :
        nat -> nat -> (nat -> nat -> __ -> 'a1 -> 'a1) -> 'a1 -> 'a1 -> 'a1 **)

    let min_case n m x x0 x1 =
      min_case_strong n m x (fun _ -> x0) (fun _ -> x1)

    (** val min_dec : nat -> nat -> sumbool **)

    let min_dec n m =
      min_case n m (fun _ _ _ h0 -> h0) Coq_left Coq_right
   end

  (** val max_case_strong :
      nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let max_case_strong n m x x0 =
    Private_Dec.max_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val max_case : nat -> nat -> 'a1 -> 'a1 -> 'a1 **)

  let max_case n m x x0 =
    max_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val max_dec : nat -> nat -> sumbool **)

  let max_dec =
    Private_Dec.max_dec

  (** val min_case_strong :
      nat -> nat -> (__ -> 'a1) -> (__ -> 'a1) -> 'a1 **)

  let min_case_strong n m x x0 =
    Private_Dec.min_case_strong n m (fun _ _ _ x1 -> x1) x x0

  (** val min_case : nat -> nat -> 'a1 -> 'a1 -> 'a1 **)

  let min_case n m x x0 =
    min_case_strong n m (fun _ -> x) (fun _ -> x0)

  (** val min_dec : nat -> nat -> sumbool **)

  let min_dec =
    Private_Dec.min_dec

  module Private_Parity =
   struct
   end

  (** val iter_rect :
      ('a1 -> 'a1) -> 'a1 -> 'a2 -> (nat -> 'a1 -> 'a2 -> 'a2) -> nat -> 'a2 **)

  let rec iter_rect f a h0 hS = function
  | O -> h0
  | S n0 ->
    hS n0 (let rec f0 = function
           | O -> a
           | S n2 -> f (f0 n2)
           in f0 n0) (iter_rect f a h0 hS n0)

  module Private_NZPow =
   struct
   end

  module Private_NZSqrt =
   struct
   end

  (** val sqrt_up : nat -> nat **)

  let sqrt_up a =
    match compare O a with
    | Lt -> S (sqrt (pred a))
    | _ -> O

  (** val log2_up : nat -> nat **)

  let log2_up a =
    match compare (S O) a with
    | Lt -> S (log2 (pred a))
    | _ -> O

  module Private_NZGcdProp =
   struct
   end

  module Private_NDivProp =
   struct
    module Private_NZDiv =
     struct
     end
   end

  module Div0 =
   struct
   end

  module Private_NLcmProp =
   struct
    (** val lcm : nat -> nat -> nat **)

    let lcm a b =
      mul a (div b (gcd a b))
   end

  (** val lcm : nat -> nat -> nat **)

  let lcm a b =
    mul a (div b (gcd a b))

  module Lcm0 =
   struct
   end

  (** val eqb_spec : nat -> nat -> reflect **)

  let eqb_spec x y =
    iff_reflect (eqb x y)

  (** val b2n : bool -> nat **)

  let b2n = function
  | Coq_true -> S O
  | Coq_false -> O

  (** val setbit : nat -> nat -> nat **)

  let setbit a n =
    coq_lor a (shiftl (S O) n)

  (** val clearbit : nat -> nat -> nat **)

  let clearbit a n =
    ldiff a (shiftl (S O) n)

  (** val ones : nat -> nat **)

  let ones n =
    pred (shiftl (S O) n)

  (** val lnot : nat -> nat -> nat **)

  let lnot a n =
    coq_lxor a (ones n)

  (** val coq_Even_Odd_dec : nat -> sumbool **)

  let rec coq_Even_Odd_dec = function
  | O -> Coq_left
  | S n0 ->
    (match coq_Even_Odd_dec n0 with
     | Coq_left -> Coq_right
     | Coq_right -> Coq_left)

  type coq_EvenT = nat

  type coq_OddT = nat

  (** val coq_EvenT_0 : coq_EvenT **)

  let coq_EvenT_0 =
    O

  (** val coq_EvenT_2 : nat -> coq_EvenT -> coq_EvenT **)

  let coq_EvenT_2 _ h0 =
    S h0

  (** val coq_OddT_1 : coq_OddT **)

  let coq_OddT_1 =
    O

  (** val coq_OddT_2 : nat -> coq_OddT -> coq_OddT **)

  let coq_OddT_2 _ h0 =
    S h0

  (** val coq_EvenT_S_OddT : nat -> coq_EvenT -> coq_OddT **)

  let coq_EvenT_S_OddT _ = function
  | O -> assert false (* absurd case *)
  | S n -> n

  (** val coq_OddT_S_EvenT : nat -> coq_OddT -> coq_EvenT **)

  let coq_OddT_S_EvenT _ h =
    h

  (** val even_EvenT : nat -> coq_EvenT **)

  let rec even_EvenT = function
  | O -> coq_EvenT_0
  | S n0 ->
    (match n0 with
     | O -> assert false (* absurd case *)
     | S n1 -> let he = even_EvenT n1 in coq_EvenT_2 n1 he)

  (** val odd_OddT : nat -> coq_OddT **)

  let rec odd_OddT = function
  | O -> assert false (* absurd case *)
  | S n0 ->
    (match n0 with
     | O -> coq_OddT_1
     | S n1 -> let he = odd_OddT n1 in coq_OddT_2 n1 he)

  (** val coq_Even_EvenT : nat -> coq_EvenT **)

  let coq_Even_EvenT =
    even_EvenT

  (** val coq_Odd_OddT : nat -> coq_OddT **)

  let coq_Odd_OddT =
    odd_OddT

  (** val coq_EvenT_OddT_dec : nat -> (coq_EvenT, coq_OddT) sum **)

  let coq_EvenT_OddT_dec n =
    match even n with
    | Coq_true -> Coq_inl (even_EvenT n)
    | Coq_false -> Coq_inr (odd_OddT n)

  (** val coq_OddT_EvenT_rect :
      (nat -> coq_EvenT -> 'a2 -> 'a1) -> 'a2 -> (nat -> coq_OddT -> 'a1 ->
      'a2) -> nat -> coq_OddT -> 'a1 **)

  let rec coq_OddT_EvenT_rect hQP hQ0 hPQ n0 h =
    match n0 with
    | O -> assert false (* absurd case *)
    | S n ->
      (match n with
       | O -> hQP O coq_EvenT_0 hQ0
       | S n1 ->
         let hES = coq_OddT_S_EvenT (S n1) h in
         let hO = coq_EvenT_S_OddT n1 hES in
         hQP (S n1) hES (hPQ n1 hO (coq_OddT_EvenT_rect hQP hQ0 hPQ n1 hO)))

  (** val coq_EvenT_OddT_rect :
      (nat -> coq_EvenT -> 'a2 -> 'a1) -> 'a2 -> (nat -> coq_OddT -> 'a1 ->
      'a2) -> nat -> coq_EvenT -> 'a2 **)

  let coq_EvenT_OddT_rect hQP hQ0 hPQ n0 hES =
    match n0 with
    | O -> hQ0
    | S n ->
      let hO = coq_EvenT_S_OddT n hES in
      hPQ n hO (coq_OddT_EvenT_rect hQP hQ0 hPQ n hO)
 end
