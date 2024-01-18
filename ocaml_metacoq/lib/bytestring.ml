open Ascii
open Byte
open Byte0
open ByteCompare
open ByteCompareSpec
open Classes
open Datatypes
open Nat
open OrdersAlt
open ReflectEq
open Specif
open String

(** val byte_parse : byte -> byte **)

let byte_parse b =
  b

(** val byte_print : byte -> byte **)

let byte_print b =
  b

module String =
 struct
  type t =
  | EmptyString
  | String of byte * t

  (** val t_rect : 'a1 -> (byte -> t -> 'a1 -> 'a1) -> t -> 'a1 **)

  let rec t_rect f f0 = function
  | EmptyString -> f
  | String (b, t1) -> f0 b t1 (t_rect f f0 t1)

  (** val t_rec : 'a1 -> (byte -> t -> 'a1 -> 'a1) -> t -> 'a1 **)

  let rec t_rec f f0 = function
  | EmptyString -> f
  | String (b, t1) -> f0 b t1 (t_rec f f0 t1)

  (** val print : t -> byte list **)

  let rec print = function
  | EmptyString -> Coq_nil
  | String (b0, bs0) -> Coq_cons (b0, (print bs0))

  (** val parse : byte list -> t **)

  let rec parse = function
  | Coq_nil -> EmptyString
  | Coq_cons (b0, bs0) -> String (b0, (parse bs0))

  (** val append : t -> t -> t **)

  let rec append x y =
    match x with
    | EmptyString -> y
    | String (x0, xs) -> String (x0, (append xs y))

  (** val to_string : t -> string **)

  let rec to_string = function
  | EmptyString -> String.EmptyString
  | String (x, xs) -> String.String ((ascii_of_byte x), (to_string xs))

  (** val of_string : string -> t **)

  let rec of_string = function
  | String.EmptyString -> EmptyString
  | String.String (x, xs) -> String ((byte_of_ascii x), (of_string xs))

  (** val rev : t -> t -> t **)

  let rec rev acc = function
  | EmptyString -> acc
  | String (s0, ss) -> rev (String (s0, acc)) ss

  (** val substring : nat -> nat -> t -> t **)

  let rec substring n m s =
    match n with
    | O ->
      (match m with
       | O -> EmptyString
       | S m' ->
         (match s with
          | EmptyString -> s
          | String (c, s') -> String (c, (substring O m' s'))))
    | S n' ->
      (match s with
       | EmptyString -> s
       | String (_, s') -> substring n' m s')

  (** val prefix : t -> t -> bool **)

  let rec prefix s1 s2 =
    match s1 with
    | EmptyString -> Coq_true
    | String (x, xs) ->
      (match s2 with
       | EmptyString -> Coq_false
       | String (y, ys) ->
         (match Byte0.eqb x y with
          | Coq_true -> prefix xs ys
          | Coq_false -> Coq_false))

  (** val index : nat -> t -> t -> nat option **)

  let rec index n s1 s2 = match s2 with
  | EmptyString ->
    (match n with
     | O -> (match s1 with
             | EmptyString -> Some O
             | String (_, _) -> None)
     | S _ -> None)
  | String (_, s2') ->
    (match n with
     | O ->
       (match prefix s1 s2 with
        | Coq_true -> Some O
        | Coq_false ->
          (match index O s1 s2' with
           | Some n0 -> Some (S n0)
           | None -> None))
     | S n' ->
       (match index n' s1 s2' with
        | Some n0 -> Some (S n0)
        | None -> None))

  (** val length : t -> nat **)

  let rec length = function
  | EmptyString -> O
  | String (_, l0) -> S (length l0)

  (** val contains : nat -> t list -> t -> bool **)

  let rec contains start keys fullname =
    match keys with
    | Coq_nil -> Coq_true
    | Coq_cons (kh, ktl) ->
      (match index start kh fullname with
       | Some n -> contains (add n (length kh)) ktl fullname
       | None -> Coq_false)

  (** val eqb : t -> t -> bool **)

  let rec eqb a b =
    match a with
    | EmptyString ->
      (match b with
       | EmptyString -> Coq_true
       | String (_, _) -> Coq_false)
    | String (x, xs) ->
      (match b with
       | EmptyString -> Coq_false
       | String (y, ys) ->
         (match ByteCompare.eqb x y with
          | Coq_true -> eqb xs ys
          | Coq_false -> Coq_false))

  (** val compare : t -> t -> comparison **)

  let rec compare xs ys =
    match xs with
    | EmptyString -> (match ys with
                      | EmptyString -> Eq
                      | String (_, _) -> Lt)
    | String (x, xs0) ->
      (match ys with
       | EmptyString -> Gt
       | String (y, ys0) ->
         (match ByteCompare.compare x y with
          | Eq -> compare xs0 ys0
          | x0 -> x0))

  (** val concat : t -> t list -> t **)

  let rec concat sep = function
  | Coq_nil -> EmptyString
  | Coq_cons (s0, xs) ->
    (match xs with
     | Coq_nil -> s0
     | Coq_cons (_, _) -> append s0 (append sep (concat sep xs)))
 end

type bs = String.t

module OT_byte =
 struct
  type t = byte

  (** val compare : t -> t -> byte OrderedType.coq_Compare **)

  let compare x y =
    match ByteCompare.compare x y with
    | Eq -> OrderedType.EQ
    | Lt -> OrderedType.LT
    | Gt -> OrderedType.GT

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec =
    eq_dec (coq_ReflectEq_EqDec byte_reflect_eq)
 end

(** val byte_eqdec : byte coq_EqDec **)

let byte_eqdec =
  coq_ReflectEq_EqDec byte_reflect_eq

module StringOT =
 struct
  type t = String.t

  (** val compare : String.t -> String.t -> comparison **)

  let compare =
    String.compare

  (** val reflect_eq_string : t coq_ReflectEq **)

  let reflect_eq_string =
    String.eqb

  (** val eq_dec : t -> t -> sumbool **)

  let eq_dec =
    eq_dec (coq_ReflectEq_EqDec reflect_eq_string)
 end

module StringOTOrig = Backport_OT(StringOT)

module Tree =
 struct
  type t =
  | Coq_string of String.t
  | Coq_append of t * t

  (** val t_rect :
      (String.t -> 'a1) -> (t -> 'a1 -> t -> 'a1 -> 'a1) -> t -> 'a1 **)

  let rec t_rect f f0 = function
  | Coq_string t1 -> f t1
  | Coq_append (t1, t2) -> f0 t1 (t_rect f f0 t1) t2 (t_rect f f0 t2)

  (** val t_rec :
      (String.t -> 'a1) -> (t -> 'a1 -> t -> 'a1 -> 'a1) -> t -> 'a1 **)

  let rec t_rec f f0 = function
  | Coq_string t1 -> f t1
  | Coq_append (t1, t2) -> f0 t1 (t_rec f f0 t1) t2 (t_rec f f0 t2)

  (** val to_rev_list_aux : t -> String.t list -> String.t list **)

  let rec to_rev_list_aux t0 acc =
    match t0 with
    | Coq_string s -> Coq_cons (s, acc)
    | Coq_append (s, s') -> to_rev_list_aux s' (to_rev_list_aux s acc)

  (** val to_string_acc : String.t -> String.t list -> String.t **)

  let rec to_string_acc acc = function
  | Coq_nil -> acc
  | Coq_cons (s, xs) -> to_string_acc (String.append s acc) xs

  (** val to_string : t -> String.t **)

  let to_string t0 =
    let l = to_rev_list_aux t0 Coq_nil in to_string_acc String.EmptyString l

  (** val string_of_list_aux : ('a1 -> t) -> t -> 'a1 list -> t **)

  let rec string_of_list_aux f sep = function
  | Coq_nil -> Coq_string String.EmptyString
  | Coq_cons (a, l0) ->
    (match l0 with
     | Coq_nil -> f a
     | Coq_cons (_, _) ->
       Coq_append ((f a), (Coq_append (sep, (string_of_list_aux f sep l0)))))

  (** val string_of_list : ('a1 -> t) -> 'a1 list -> t **)

  let string_of_list f l =
    Coq_append ((Coq_string (String.String (Coq_x5b, String.EmptyString))),
      (Coq_append
      ((string_of_list_aux f (Coq_string (String.String (Coq_x2c,
         String.EmptyString))) l), (Coq_string (String.String (Coq_x5d,
      String.EmptyString))))))

  (** val print_list : ('a1 -> t) -> t -> 'a1 list -> t **)

  let print_list =
    string_of_list_aux

  (** val concat : t -> t list -> t **)

  let rec concat sep = function
  | Coq_nil -> Coq_string String.EmptyString
  | Coq_cons (s0, xs) ->
    (match xs with
     | Coq_nil -> s0
     | Coq_cons (_, _) -> Coq_append (s0, (Coq_append (sep, (concat sep xs)))))

  (** val parens : bool -> t -> t **)

  let parens top s =
    match top with
    | Coq_true -> s
    | Coq_false ->
      Coq_append ((Coq_string (String.String (Coq_x28, String.EmptyString))),
        (Coq_append (s, (Coq_string (String.String (Coq_x29,
        String.EmptyString))))))
 end
