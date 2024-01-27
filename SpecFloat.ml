open BinInt
open BinNums
open BinPos
open Bool
open Datatypes
open FloatClass
open Zbool
open Zpower

type spec_float =
| S754_zero of bool
| S754_infinity of bool
| S754_nan
| S754_finite of bool * positive * coq_Z

(** val emin : coq_Z -> coq_Z -> coq_Z **)

let emin prec emax =
  Z.sub (Z.sub (Zpos (Coq_xI Coq_xH)) emax) prec

(** val fexp : coq_Z -> coq_Z -> coq_Z -> coq_Z **)

let fexp prec emax e =
  Z.max (Z.sub e prec) (emin prec emax)

(** val digits2_pos : positive -> positive **)

let rec digits2_pos = function
| Coq_xI p -> Pos.succ (digits2_pos p)
| Coq_xO p -> Pos.succ (digits2_pos p)
| Coq_xH -> Coq_xH

(** val coq_Zdigits2 : coq_Z -> coq_Z **)

let coq_Zdigits2 n = match n with
| Z0 -> n
| Zpos p -> Zpos (digits2_pos p)
| Zneg p -> Zpos (digits2_pos p)

(** val canonical_mantissa : coq_Z -> coq_Z -> positive -> coq_Z -> bool **)

let canonical_mantissa prec emax m e =
  coq_Zeq_bool (fexp prec emax (Z.add (Zpos (digits2_pos m)) e)) e

(** val bounded : coq_Z -> coq_Z -> positive -> coq_Z -> bool **)

let bounded prec emax m e =
  match canonical_mantissa prec emax m e with
  | Coq_true -> Z.leb e (Z.sub emax prec)
  | Coq_false -> Coq_false

(** val valid_binary : coq_Z -> coq_Z -> spec_float -> bool **)

let valid_binary prec emax = function
| S754_finite (_, m, e) -> bounded prec emax m e
| _ -> Coq_true

(** val iter_pos : ('a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

let rec iter_pos f n x =
  match n with
  | Coq_xI n' -> iter_pos f n' (iter_pos f n' (f x))
  | Coq_xO n' -> iter_pos f n' (iter_pos f n' x)
  | Coq_xH -> f x

type location =
| Coq_loc_Exact
| Coq_loc_Inexact of comparison

(** val location_rect : 'a1 -> (comparison -> 'a1) -> location -> 'a1 **)

let location_rect f f0 = function
| Coq_loc_Exact -> f
| Coq_loc_Inexact c -> f0 c

(** val location_rec : 'a1 -> (comparison -> 'a1) -> location -> 'a1 **)

let location_rec f f0 = function
| Coq_loc_Exact -> f
| Coq_loc_Inexact c -> f0 c

type shr_record = { shr_m : coq_Z; shr_r : bool; shr_s : bool }

(** val shr_m : shr_record -> coq_Z **)

let shr_m s =
  s.shr_m

(** val shr_r : shr_record -> bool **)

let shr_r s =
  s.shr_r

(** val shr_s : shr_record -> bool **)

let shr_s s =
  s.shr_s

(** val shr_1 : shr_record -> shr_record **)

let shr_1 mrs =
  let { shr_m = m; shr_r = r; shr_s = s } = mrs in
  let s0 = match r with
           | Coq_true -> Coq_true
           | Coq_false -> s in
  (match m with
   | Z0 -> { shr_m = Z0; shr_r = Coq_false; shr_s = s0 }
   | Zpos p0 ->
     (match p0 with
      | Coq_xI p -> { shr_m = (Zpos p); shr_r = Coq_true; shr_s = s0 }
      | Coq_xO p -> { shr_m = (Zpos p); shr_r = Coq_false; shr_s = s0 }
      | Coq_xH -> { shr_m = Z0; shr_r = Coq_true; shr_s = s0 })
   | Zneg p0 ->
     (match p0 with
      | Coq_xI p -> { shr_m = (Zneg p); shr_r = Coq_true; shr_s = s0 }
      | Coq_xO p -> { shr_m = (Zneg p); shr_r = Coq_false; shr_s = s0 }
      | Coq_xH -> { shr_m = Z0; shr_r = Coq_true; shr_s = s0 }))

(** val loc_of_shr_record : shr_record -> location **)

let loc_of_shr_record mrs =
  let { shr_m = _; shr_r = shr_r0; shr_s = shr_s0 } = mrs in
  (match shr_r0 with
   | Coq_true ->
     (match shr_s0 with
      | Coq_true -> Coq_loc_Inexact Gt
      | Coq_false -> Coq_loc_Inexact Eq)
   | Coq_false ->
     (match shr_s0 with
      | Coq_true -> Coq_loc_Inexact Lt
      | Coq_false -> Coq_loc_Exact))

(** val shr_record_of_loc : coq_Z -> location -> shr_record **)

let shr_record_of_loc m = function
| Coq_loc_Exact -> { shr_m = m; shr_r = Coq_false; shr_s = Coq_false }
| Coq_loc_Inexact c ->
  (match c with
   | Eq -> { shr_m = m; shr_r = Coq_true; shr_s = Coq_false }
   | Lt -> { shr_m = m; shr_r = Coq_false; shr_s = Coq_true }
   | Gt -> { shr_m = m; shr_r = Coq_true; shr_s = Coq_true })

(** val shr : shr_record -> coq_Z -> coq_Z -> (shr_record, coq_Z) prod **)

let shr mrs e n = match n with
| Zpos p -> Coq_pair ((iter_pos shr_1 p mrs), (Z.add e n))
| _ -> Coq_pair (mrs, e)

(** val shr_fexp :
    coq_Z -> coq_Z -> coq_Z -> coq_Z -> location -> (shr_record, coq_Z) prod **)

let shr_fexp prec emax m e l =
  shr (shr_record_of_loc m l) e
    (Z.sub (fexp prec emax (Z.add (coq_Zdigits2 m) e)) e)

(** val round_nearest_even : coq_Z -> location -> coq_Z **)

let round_nearest_even mx = function
| Coq_loc_Exact -> mx
| Coq_loc_Inexact c ->
  (match c with
   | Eq ->
     (match Z.even mx with
      | Coq_true -> mx
      | Coq_false -> Z.add mx (Zpos Coq_xH))
   | Lt -> mx
   | Gt -> Z.add mx (Zpos Coq_xH))

(** val binary_round_aux :
    coq_Z -> coq_Z -> bool -> coq_Z -> coq_Z -> location -> spec_float **)

let binary_round_aux prec emax sx mx ex lx =
  let Coq_pair (mrs', e') = shr_fexp prec emax mx ex lx in
  let Coq_pair (mrs'', e'') =
    shr_fexp prec emax
      (round_nearest_even mrs'.shr_m (loc_of_shr_record mrs')) e'
      Coq_loc_Exact
  in
  (match mrs''.shr_m with
   | Z0 -> S754_zero sx
   | Zpos m ->
     (match Z.leb e'' (Z.sub emax prec) with
      | Coq_true -> S754_finite (sx, m, e'')
      | Coq_false -> S754_infinity sx)
   | Zneg _ -> S754_nan)

(** val shl_align : positive -> coq_Z -> coq_Z -> (positive, coq_Z) prod **)

let shl_align mx ex ex' =
  match Z.sub ex' ex with
  | Zneg d -> Coq_pair ((shift_pos d mx), ex')
  | _ -> Coq_pair (mx, ex)

(** val binary_round :
    coq_Z -> coq_Z -> bool -> positive -> coq_Z -> spec_float **)

let binary_round prec emax sx mx ex =
  let Coq_pair (mz, ez) =
    shl_align mx ex (fexp prec emax (Z.add (Zpos (digits2_pos mx)) ex))
  in
  binary_round_aux prec emax sx (Zpos mz) ez Coq_loc_Exact

(** val binary_normalize :
    coq_Z -> coq_Z -> coq_Z -> coq_Z -> bool -> spec_float **)

let binary_normalize prec emax m e szero =
  match m with
  | Z0 -> S754_zero szero
  | Zpos m0 -> binary_round prec emax Coq_false m0 e
  | Zneg m0 -> binary_round prec emax Coq_true m0 e

(** val coq_SFopp : spec_float -> spec_float **)

let coq_SFopp = function
| S754_zero sx -> S754_zero (negb sx)
| S754_infinity sx -> S754_infinity (negb sx)
| S754_nan -> S754_nan
| S754_finite (sx, mx, ex) -> S754_finite ((negb sx), mx, ex)

(** val coq_SFabs : spec_float -> spec_float **)

let coq_SFabs = function
| S754_zero _ -> S754_zero Coq_false
| S754_infinity _ -> S754_infinity Coq_false
| S754_nan -> S754_nan
| S754_finite (_, mx, ex) -> S754_finite (Coq_false, mx, ex)

(** val coq_SFcompare : spec_float -> spec_float -> comparison option **)

let coq_SFcompare f1 f2 =
  match f1 with
  | S754_zero _ ->
    (match f2 with
     | S754_zero _ -> Some Eq
     | S754_infinity s -> Some (match s with
                                | Coq_true -> Gt
                                | Coq_false -> Lt)
     | S754_nan -> None
     | S754_finite (s, _, _) ->
       Some (match s with
             | Coq_true -> Gt
             | Coq_false -> Lt))
  | S754_infinity s ->
    (match f2 with
     | S754_infinity s0 ->
       Some
         (match s with
          | Coq_true -> (match s0 with
                         | Coq_true -> Eq
                         | Coq_false -> Lt)
          | Coq_false -> (match s0 with
                          | Coq_true -> Gt
                          | Coq_false -> Eq))
     | S754_nan -> None
     | _ -> Some (match s with
                  | Coq_true -> Lt
                  | Coq_false -> Gt))
  | S754_nan -> None
  | S754_finite (s1, m1, e1) ->
    (match f2 with
     | S754_zero _ -> Some (match s1 with
                            | Coq_true -> Lt
                            | Coq_false -> Gt)
     | S754_infinity s -> Some (match s with
                                | Coq_true -> Gt
                                | Coq_false -> Lt)
     | S754_nan -> None
     | S754_finite (s2, m2, e2) ->
       Some
         (match s1 with
          | Coq_true ->
            (match s2 with
             | Coq_true ->
               (match Z.compare e1 e2 with
                | Eq -> coq_CompOpp (Pos.compare_cont Eq m1 m2)
                | Lt -> Gt
                | Gt -> Lt)
             | Coq_false -> Lt)
          | Coq_false ->
            (match s2 with
             | Coq_true -> Gt
             | Coq_false ->
               (match Z.compare e1 e2 with
                | Eq -> Pos.compare_cont Eq m1 m2
                | x -> x))))

(** val coq_SFeqb : spec_float -> spec_float -> bool **)

let coq_SFeqb f1 f2 =
  match coq_SFcompare f1 f2 with
  | Some c -> (match c with
               | Eq -> Coq_true
               | _ -> Coq_false)
  | None -> Coq_false

(** val coq_SFltb : spec_float -> spec_float -> bool **)

let coq_SFltb f1 f2 =
  match coq_SFcompare f1 f2 with
  | Some c -> (match c with
               | Lt -> Coq_true
               | _ -> Coq_false)
  | None -> Coq_false

(** val coq_SFleb : spec_float -> spec_float -> bool **)

let coq_SFleb f1 f2 =
  match coq_SFcompare f1 f2 with
  | Some c -> (match c with
               | Gt -> Coq_false
               | _ -> Coq_true)
  | None -> Coq_false

(** val coq_SFclassify : coq_Z -> spec_float -> float_class **)

let coq_SFclassify prec = function
| S754_zero s -> (match s with
                  | Coq_true -> NZero
                  | Coq_false -> PZero)
| S754_infinity s -> (match s with
                      | Coq_true -> NInf
                      | Coq_false -> PInf)
| S754_nan -> NaN
| S754_finite (s, m, _) ->
  (match s with
   | Coq_true ->
     (match Pos.eqb (digits2_pos m) (Z.to_pos prec) with
      | Coq_true -> NNormal
      | Coq_false -> NSubn)
   | Coq_false ->
     (match Pos.eqb (digits2_pos m) (Z.to_pos prec) with
      | Coq_true -> PNormal
      | Coq_false -> PSubn))

(** val coq_SFmul :
    coq_Z -> coq_Z -> spec_float -> spec_float -> spec_float **)

let coq_SFmul prec emax x y =
  match x with
  | S754_zero sx ->
    (match y with
     | S754_zero sy -> S754_zero (xorb sx sy)
     | S754_finite (sy, _, _) -> S754_zero (xorb sx sy)
     | _ -> S754_nan)
  | S754_infinity sx ->
    (match y with
     | S754_infinity sy -> S754_infinity (xorb sx sy)
     | S754_finite (sy, _, _) -> S754_infinity (xorb sx sy)
     | _ -> S754_nan)
  | S754_nan -> S754_nan
  | S754_finite (sx, mx, ex) ->
    (match y with
     | S754_zero sy -> S754_zero (xorb sx sy)
     | S754_infinity sy -> S754_infinity (xorb sx sy)
     | S754_nan -> S754_nan
     | S754_finite (sy, my, ey) ->
       binary_round_aux prec emax (xorb sx sy) (Zpos (Pos.mul mx my))
         (Z.add ex ey) Coq_loc_Exact)

(** val cond_Zopp : bool -> coq_Z -> coq_Z **)

let cond_Zopp b m =
  match b with
  | Coq_true -> Z.opp m
  | Coq_false -> m

(** val coq_SFadd :
    coq_Z -> coq_Z -> spec_float -> spec_float -> spec_float **)

let coq_SFadd prec emax x y =
  match x with
  | S754_zero sx ->
    (match y with
     | S754_zero sy ->
       (match eqb sx sy with
        | Coq_true -> x
        | Coq_false -> S754_zero Coq_false)
     | S754_nan -> S754_nan
     | _ -> y)
  | S754_infinity sx ->
    (match y with
     | S754_infinity sy ->
       (match eqb sx sy with
        | Coq_true -> x
        | Coq_false -> S754_nan)
     | S754_nan -> S754_nan
     | _ -> x)
  | S754_nan -> S754_nan
  | S754_finite (sx, mx, ex) ->
    (match y with
     | S754_zero _ -> x
     | S754_infinity _ -> y
     | S754_nan -> S754_nan
     | S754_finite (sy, my, ey) ->
       let ez = Z.min ex ey in
       binary_normalize prec emax
         (Z.add (cond_Zopp sx (Zpos (fst (shl_align mx ex ez))))
           (cond_Zopp sy (Zpos (fst (shl_align my ey ez))))) ez Coq_false)

(** val coq_SFsub :
    coq_Z -> coq_Z -> spec_float -> spec_float -> spec_float **)

let coq_SFsub prec emax x y =
  match x with
  | S754_zero sx ->
    (match y with
     | S754_zero sy ->
       (match eqb sx (negb sy) with
        | Coq_true -> x
        | Coq_false -> S754_zero Coq_false)
     | S754_infinity sy -> S754_infinity (negb sy)
     | S754_nan -> S754_nan
     | S754_finite (sy, my, ey) -> S754_finite ((negb sy), my, ey))
  | S754_infinity sx ->
    (match y with
     | S754_infinity sy ->
       (match eqb sx (negb sy) with
        | Coq_true -> x
        | Coq_false -> S754_nan)
     | S754_nan -> S754_nan
     | _ -> x)
  | S754_nan -> S754_nan
  | S754_finite (sx, mx, ex) ->
    (match y with
     | S754_zero _ -> x
     | S754_infinity sy -> S754_infinity (negb sy)
     | S754_nan -> S754_nan
     | S754_finite (sy, my, ey) ->
       let ez = Z.min ex ey in
       binary_normalize prec emax
         (Z.sub (cond_Zopp sx (Zpos (fst (shl_align mx ex ez))))
           (cond_Zopp sy (Zpos (fst (shl_align my ey ez))))) ez Coq_false)

(** val new_location_even : coq_Z -> coq_Z -> location **)

let new_location_even nb_steps k =
  match coq_Zeq_bool k Z0 with
  | Coq_true -> Coq_loc_Exact
  | Coq_false ->
    Coq_loc_Inexact (Z.compare (Z.mul (Zpos (Coq_xO Coq_xH)) k) nb_steps)

(** val new_location_odd : coq_Z -> coq_Z -> location **)

let new_location_odd nb_steps k =
  match coq_Zeq_bool k Z0 with
  | Coq_true -> Coq_loc_Exact
  | Coq_false ->
    Coq_loc_Inexact
      (match Z.compare (Z.add (Z.mul (Zpos (Coq_xO Coq_xH)) k) (Zpos Coq_xH))
               nb_steps with
       | Eq -> Lt
       | x -> x)

(** val new_location : coq_Z -> coq_Z -> location **)

let new_location nb_steps =
  match Z.even nb_steps with
  | Coq_true -> new_location_even nb_steps
  | Coq_false -> new_location_odd nb_steps

(** val coq_SFdiv_core_binary :
    coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z -> coq_Z -> ((coq_Z, coq_Z)
    prod, location) prod **)

let coq_SFdiv_core_binary prec emax m1 e1 m2 e2 =
  let d1 = coq_Zdigits2 m1 in
  let d2 = coq_Zdigits2 m2 in
  let e' =
    Z.min (fexp prec emax (Z.sub (Z.add d1 e1) (Z.add d2 e2))) (Z.sub e1 e2)
  in
  let s = Z.sub (Z.sub e1 e2) e' in
  let m' = match s with
           | Z0 -> m1
           | Zpos _ -> Z.shiftl m1 s
           | Zneg _ -> Z0 in
  let Coq_pair (q, r) = Z.div_eucl m' m2 in
  Coq_pair ((Coq_pair (q, e')), (new_location m2 r))

(** val coq_SFdiv :
    coq_Z -> coq_Z -> spec_float -> spec_float -> spec_float **)

let coq_SFdiv prec emax x y =
  match x with
  | S754_zero sx ->
    (match y with
     | S754_infinity sy -> S754_zero (xorb sx sy)
     | S754_finite (sy, _, _) -> S754_zero (xorb sx sy)
     | _ -> S754_nan)
  | S754_infinity sx ->
    (match y with
     | S754_zero sy -> S754_infinity (xorb sx sy)
     | S754_finite (sy, _, _) -> S754_infinity (xorb sx sy)
     | _ -> S754_nan)
  | S754_nan -> S754_nan
  | S754_finite (sx, mx, ex) ->
    (match y with
     | S754_zero sy -> S754_infinity (xorb sx sy)
     | S754_infinity sy -> S754_zero (xorb sx sy)
     | S754_nan -> S754_nan
     | S754_finite (sy, my, ey) ->
       let Coq_pair (p, lz) =
         coq_SFdiv_core_binary prec emax (Zpos mx) ex (Zpos my) ey
       in
       let Coq_pair (mz, ez) = p in
       binary_round_aux prec emax (xorb sx sy) mz ez lz)

(** val coq_SFsqrt_core_binary :
    coq_Z -> coq_Z -> coq_Z -> coq_Z -> ((coq_Z, coq_Z) prod, location) prod **)

let coq_SFsqrt_core_binary prec emax m e =
  let d = coq_Zdigits2 m in
  let e' =
    Z.min (fexp prec emax (Z.div2 (Z.add (Z.add d e) (Zpos Coq_xH))))
      (Z.div2 e)
  in
  let s = Z.sub e (Z.mul (Zpos (Coq_xO Coq_xH)) e') in
  let m' = match s with
           | Z0 -> m
           | Zpos _ -> Z.shiftl m s
           | Zneg _ -> Z0 in
  let Coq_pair (q, r) = Z.sqrtrem m' in
  let l =
    match coq_Zeq_bool r Z0 with
    | Coq_true -> Coq_loc_Exact
    | Coq_false ->
      Coq_loc_Inexact (match Z.leb r q with
                       | Coq_true -> Lt
                       | Coq_false -> Gt)
  in
  Coq_pair ((Coq_pair (q, e')), l)

(** val coq_SFsqrt : coq_Z -> coq_Z -> spec_float -> spec_float **)

let coq_SFsqrt prec emax x = match x with
| S754_zero _ -> x
| S754_infinity s -> (match s with
                      | Coq_true -> S754_nan
                      | Coq_false -> x)
| S754_nan -> S754_nan
| S754_finite (s, mx, ex) ->
  (match s with
   | Coq_true -> S754_nan
   | Coq_false ->
     let Coq_pair (p, lz) = coq_SFsqrt_core_binary prec emax (Zpos mx) ex in
     let Coq_pair (mz, ez) = p in
     binary_round_aux prec emax Coq_false mz ez lz)

(** val coq_SFnormfr_mantissa : coq_Z -> spec_float -> coq_N **)

let coq_SFnormfr_mantissa prec = function
| S754_finite (_, mx, ex) ->
  (match Z.eqb ex (Z.opp prec) with
   | Coq_true -> Npos mx
   | Coq_false -> N0)
| _ -> N0

(** val coq_SFldexp : coq_Z -> coq_Z -> spec_float -> coq_Z -> spec_float **)

let coq_SFldexp prec emax f e =
  match f with
  | S754_finite (sx, mx, ex) -> binary_round prec emax sx mx (Z.add ex e)
  | _ -> f

(** val coq_SFfrexp :
    coq_Z -> coq_Z -> spec_float -> (spec_float, coq_Z) prod **)

let coq_SFfrexp prec emax f = match f with
| S754_finite (sx, mx, ex) ->
  (match Pos.leb (Z.to_pos prec) (digits2_pos mx) with
   | Coq_true ->
     Coq_pair ((S754_finite (sx, mx, (Z.opp prec))), (Z.add ex prec))
   | Coq_false ->
     let d = Z.sub prec (Zpos (digits2_pos mx)) in
     Coq_pair ((S754_finite (sx, (shift_pos (Z.to_pos d) mx), (Z.opp prec))),
     (Z.sub (Z.add ex prec) d)))
| _ -> Coq_pair (f, (Z.sub (Z.mul (Zneg (Coq_xO Coq_xH)) emax) prec))

(** val coq_SFone : coq_Z -> coq_Z -> spec_float **)

let coq_SFone prec emax =
  binary_round prec emax Coq_false Coq_xH Z0

(** val coq_SFulp : coq_Z -> coq_Z -> spec_float -> spec_float **)

let coq_SFulp prec emax x =
  coq_SFldexp prec emax (coq_SFone prec emax)
    (fexp prec emax (snd (coq_SFfrexp prec emax x)))

(** val coq_SFpred_pos : coq_Z -> coq_Z -> spec_float -> spec_float **)

let coq_SFpred_pos prec emax x = match x with
| S754_finite (_, mx, _) ->
  let d =
    match Pos.eqb (Coq_xO mx) (shift_pos (Z.to_pos prec) Coq_xH) with
    | Coq_true ->
      coq_SFldexp prec emax (coq_SFone prec emax)
        (fexp prec emax (Z.sub (snd (coq_SFfrexp prec emax x)) (Zpos Coq_xH)))
    | Coq_false -> coq_SFulp prec emax x
  in
  coq_SFsub prec emax x d
| _ -> x

(** val coq_SFmax_float : coq_Z -> coq_Z -> spec_float **)

let coq_SFmax_float prec emax =
  S754_finite (Coq_false,
    (Pos.sub (shift_pos (Z.to_pos prec) Coq_xH) Coq_xH), (Z.sub emax prec))

(** val coq_SFsucc : coq_Z -> coq_Z -> spec_float -> spec_float **)

let coq_SFsucc prec emax x = match x with
| S754_zero _ -> coq_SFldexp prec emax (coq_SFone prec emax) (emin prec emax)
| S754_infinity s ->
  (match s with
   | Coq_true -> coq_SFopp (coq_SFmax_float prec emax)
   | Coq_false -> x)
| S754_nan -> x
| S754_finite (s, _, _) ->
  (match s with
   | Coq_true -> coq_SFopp (coq_SFpred_pos prec emax (coq_SFopp x))
   | Coq_false -> coq_SFadd prec emax x (coq_SFulp prec emax x))

(** val coq_SFpred : coq_Z -> coq_Z -> spec_float -> spec_float **)

let coq_SFpred prec emax f =
  coq_SFopp (coq_SFsucc prec emax (coq_SFopp f))
