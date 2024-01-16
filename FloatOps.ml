open BinInt
open BinNums
open Datatypes
open PrimFloat
open SpecFloat
open Uint63

(** val prec : coq_Z **)

let prec =
  Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI Coq_xH)))))

(** val emax : coq_Z **)

let emax =
  Zpos (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO
    (Coq_xO (Coq_xO Coq_xH))))))))))

(** val shift : coq_Z **)

let shift =
  Zpos (Coq_xI (Coq_xO (Coq_xI (Coq_xO (Coq_xI (Coq_xI (Coq_xO (Coq_xO
    (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))))))))

module Z =
 struct
  (** val frexp : float -> (float, coq_Z) prod **)

  let frexp f =
    let Coq_pair (m, se) = frshiftexp f in
    Coq_pair (m, (Z.sub (to_Z se) shift))

  (** val ldexp : float -> coq_Z -> float **)

  let ldexp f e =
    let e' =
      Z.max (Z.min e (Z.sub emax (emin prec emax)))
        (Z.sub (Z.sub (emin prec emax) emax) (Zpos Coq_xH))
    in
    ldshiftexp f (of_Z (Z.add e' shift))
 end

(** val ulp : float -> float **)

let ulp f =
  Z.ldexp one (fexp prec emax (snd (Z.frexp f)))

(** val coq_Prim2SF : float -> spec_float **)

let coq_Prim2SF f =
  match is_nan f with
  | Coq_true -> S754_nan
  | Coq_false ->
    (match PrimFloat.is_zero f with
     | Coq_true -> S754_zero (get_sign f)
     | Coq_false ->
       (match is_infinity f with
        | Coq_true -> S754_infinity (get_sign f)
        | Coq_false ->
          let Coq_pair (r, exp) = Z.frexp f in
          let e = BinInt.Z.sub exp prec in
          let Coq_pair (shr, e') =
            shr_fexp prec emax (to_Z (normfr_mantissa r)) e Coq_loc_Exact
          in
          (match shr.shr_m with
           | Zpos p -> S754_finite ((get_sign f), p, e')
           | _ -> S754_zero Coq_false)))

(** val coq_SF2Prim : spec_float -> float **)

let coq_SF2Prim = function
| S754_zero s -> (match s with
                  | Coq_true -> neg_zero
                  | Coq_false -> zero)
| S754_infinity s ->
  (match s with
   | Coq_true -> neg_infinity
   | Coq_false -> infinity)
| S754_nan -> nan
| S754_finite (s, m, e) ->
  let pm = of_uint63 (of_Z (Zpos m)) in
  let f = Z.ldexp pm e in
  (match s with
   | Coq_true -> PrimFloat.opp f
   | Coq_false -> f)
