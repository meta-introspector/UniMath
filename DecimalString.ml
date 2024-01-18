open Ascii
open Datatypes
open Decimal
open String

(** val uint_of_char : ascii -> uint option -> uint option **)

let uint_of_char a = function
| Some d0 ->
  let Ascii (b, b0, b1, b2, b3, b4, b5, b6) = a in
  (match b with
   | Coq_true ->
     (match b0 with
      | Coq_true ->
        (match b1 with
         | Coq_true ->
           (match b2 with
            | Coq_true -> None
            | Coq_false ->
              (match b3 with
               | Coq_true ->
                 (match b4 with
                  | Coq_true ->
                    (match b5 with
                     | Coq_true -> None
                     | Coq_false ->
                       (match b6 with
                        | Coq_true -> None
                        | Coq_false -> Some (D7 d0)))
                  | Coq_false -> None)
               | Coq_false -> None))
         | Coq_false ->
           (match b2 with
            | Coq_true -> None
            | Coq_false ->
              (match b3 with
               | Coq_true ->
                 (match b4 with
                  | Coq_true ->
                    (match b5 with
                     | Coq_true -> None
                     | Coq_false ->
                       (match b6 with
                        | Coq_true -> None
                        | Coq_false -> Some (D3 d0)))
                  | Coq_false -> None)
               | Coq_false -> None)))
      | Coq_false ->
        (match b1 with
         | Coq_true ->
           (match b2 with
            | Coq_true -> None
            | Coq_false ->
              (match b3 with
               | Coq_true ->
                 (match b4 with
                  | Coq_true ->
                    (match b5 with
                     | Coq_true -> None
                     | Coq_false ->
                       (match b6 with
                        | Coq_true -> None
                        | Coq_false -> Some (D5 d0)))
                  | Coq_false -> None)
               | Coq_false -> None))
         | Coq_false ->
           (match b2 with
            | Coq_true ->
              (match b3 with
               | Coq_true ->
                 (match b4 with
                  | Coq_true ->
                    (match b5 with
                     | Coq_true -> None
                     | Coq_false ->
                       (match b6 with
                        | Coq_true -> None
                        | Coq_false -> Some (D9 d0)))
                  | Coq_false -> None)
               | Coq_false -> None)
            | Coq_false ->
              (match b3 with
               | Coq_true ->
                 (match b4 with
                  | Coq_true ->
                    (match b5 with
                     | Coq_true -> None
                     | Coq_false ->
                       (match b6 with
                        | Coq_true -> None
                        | Coq_false -> Some (D1 d0)))
                  | Coq_false -> None)
               | Coq_false -> None))))
   | Coq_false ->
     (match b0 with
      | Coq_true ->
        (match b1 with
         | Coq_true ->
           (match b2 with
            | Coq_true -> None
            | Coq_false ->
              (match b3 with
               | Coq_true ->
                 (match b4 with
                  | Coq_true ->
                    (match b5 with
                     | Coq_true -> None
                     | Coq_false ->
                       (match b6 with
                        | Coq_true -> None
                        | Coq_false -> Some (D6 d0)))
                  | Coq_false -> None)
               | Coq_false -> None))
         | Coq_false ->
           (match b2 with
            | Coq_true -> None
            | Coq_false ->
              (match b3 with
               | Coq_true ->
                 (match b4 with
                  | Coq_true ->
                    (match b5 with
                     | Coq_true -> None
                     | Coq_false ->
                       (match b6 with
                        | Coq_true -> None
                        | Coq_false -> Some (D2 d0)))
                  | Coq_false -> None)
               | Coq_false -> None)))
      | Coq_false ->
        (match b1 with
         | Coq_true ->
           (match b2 with
            | Coq_true -> None
            | Coq_false ->
              (match b3 with
               | Coq_true ->
                 (match b4 with
                  | Coq_true ->
                    (match b5 with
                     | Coq_true -> None
                     | Coq_false ->
                       (match b6 with
                        | Coq_true -> None
                        | Coq_false -> Some (D4 d0)))
                  | Coq_false -> None)
               | Coq_false -> None))
         | Coq_false ->
           (match b2 with
            | Coq_true ->
              (match b3 with
               | Coq_true ->
                 (match b4 with
                  | Coq_true ->
                    (match b5 with
                     | Coq_true -> None
                     | Coq_false ->
                       (match b6 with
                        | Coq_true -> None
                        | Coq_false -> Some (D8 d0)))
                  | Coq_false -> None)
               | Coq_false -> None)
            | Coq_false ->
              (match b3 with
               | Coq_true ->
                 (match b4 with
                  | Coq_true ->
                    (match b5 with
                     | Coq_true -> None
                     | Coq_false ->
                       (match b6 with
                        | Coq_true -> None
                        | Coq_false -> Some (D0 d0)))
                  | Coq_false -> None)
               | Coq_false -> None)))))
| None -> None

module NilEmpty =
 struct
  (** val string_of_uint : uint -> string **)

  let rec string_of_uint = function
  | Nil -> EmptyString
  | D0 d0 ->
    String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_false, Coq_false)), (string_of_uint d0))
  | D1 d0 ->
    String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_false, Coq_false)), (string_of_uint d0))
  | D2 d0 ->
    String ((Ascii (Coq_false, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_false, Coq_false)), (string_of_uint d0))
  | D3 d0 ->
    String ((Ascii (Coq_true, Coq_true, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_false, Coq_false)), (string_of_uint d0))
  | D4 d0 ->
    String ((Ascii (Coq_false, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false, Coq_false)), (string_of_uint d0))
  | D5 d0 ->
    String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false, Coq_false)), (string_of_uint d0))
  | D6 d0 ->
    String ((Ascii (Coq_false, Coq_true, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false, Coq_false)), (string_of_uint d0))
  | D7 d0 ->
    String ((Ascii (Coq_true, Coq_true, Coq_true, Coq_false, Coq_true,
      Coq_true, Coq_false, Coq_false)), (string_of_uint d0))
  | D8 d0 ->
    String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false, Coq_false)), (string_of_uint d0))
  | D9 d0 ->
    String ((Ascii (Coq_true, Coq_false, Coq_false, Coq_true, Coq_true,
      Coq_true, Coq_false, Coq_false)), (string_of_uint d0))

  (** val uint_of_string : string -> uint option **)

  let rec uint_of_string = function
  | EmptyString -> Some Nil
  | String (a, s0) -> uint_of_char a (uint_of_string s0)

  (** val string_of_int : signed_int -> string **)

  let string_of_int = function
  | Pos d0 -> string_of_uint d0
  | Neg d0 ->
    String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
      Coq_true, Coq_false, Coq_false)), (string_of_uint d0))

  (** val int_of_string : string -> signed_int option **)

  let int_of_string s = match s with
  | EmptyString -> Some (Pos Nil)
  | String (a, s') ->
    (match Ascii.eqb a (Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
             Coq_false, Coq_true, Coq_false, Coq_false)) with
     | Coq_true -> option_map (fun x -> Neg x) (uint_of_string s')
     | Coq_false -> option_map (fun x -> Pos x) (uint_of_string s))
 end

module NilZero =
 struct
  (** val string_of_uint : uint -> string **)

  let string_of_uint d = match d with
  | Nil ->
    String ((Ascii (Coq_false, Coq_false, Coq_false, Coq_false, Coq_true,
      Coq_true, Coq_false, Coq_false)), EmptyString)
  | _ -> NilEmpty.string_of_uint d

  (** val uint_of_string : string -> uint option **)

  let uint_of_string s = match s with
  | EmptyString -> None
  | String (_, _) -> NilEmpty.uint_of_string s

  (** val string_of_int : signed_int -> string **)

  let string_of_int = function
  | Pos d0 -> string_of_uint d0
  | Neg d0 ->
    String ((Ascii (Coq_true, Coq_false, Coq_true, Coq_true, Coq_false,
      Coq_true, Coq_false, Coq_false)), (string_of_uint d0))

  (** val int_of_string : string -> signed_int option **)

  let int_of_string s = match s with
  | EmptyString -> None
  | String (a, s') ->
    (match Ascii.eqb a (Ascii (Coq_true, Coq_false, Coq_true, Coq_true,
             Coq_false, Coq_true, Coq_false, Coq_false)) with
     | Coq_true -> option_map (fun x -> Neg x) (uint_of_string s')
     | Coq_false -> option_map (fun x -> Pos x) (uint_of_string s))
 end
