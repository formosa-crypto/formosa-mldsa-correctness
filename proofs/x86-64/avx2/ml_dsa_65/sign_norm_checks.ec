require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Signature.

from Spec require import GFq Rq Parameters VecMat MLDSA_W32_Rep.

import PolyLVec PolyKVec.
import CDR Round Zq PolyReduceZq BigZMod.

require import Array256 Array1280 Array1536.

require import Polynomial Row_vector.


lemma __apply_cs2_and_check_norm_ll : islossless M.__apply_cs2_and_check_norm.
proof.
proc.
wp; while (0 <= base <= 6 * n /\ base %% n = 0) (6*n - base); last by auto => /#.  
move => ?.
admit. (* lossless *)
qed.

lemma __apply_cs2_and_check_norm_correct
      (_w0mc : W32.t Array1536.t) (_w0 : W32.t Array1536.t)
      (_s2 : W32.t Array1536.t) (_c : W32.t Array256.t)
      (_incr : W64.t)
      :
    hoare [ M.__apply_cs2_and_check_norm :
        w0_minus_cs2 = _w0mc /\ w0 = _w0 /\ s2 = _s2 /\
        verifier_challenge = _c /\ infinity_norm_check_result = _incr /\
        (_incr = W64.zero \/ _incr = W64.one) /\
        wpoly_ntt_orng _c /\
        wpolykvec_ntt_orng (kvec_unflatten256 _s2) /\
        (* w0 = LowBits(Ay), coefficients in (-gamma2, gamma2] = (-261888, 261888] *)
        wpolykvec_srng (kvec_unflatten256 _w0) (gamma2 - 1) gamma2
        ==>
        (_incr = W64.one => res.`2 = W64.one) /\
        (_incr = W64.zero =>
           res.`2 = W64.zero =>
           (* ||w0 - cs2||_inf < gamma2 - Beta = 261692 *)
           wpolykvec_infnorm (gamma2 - Beta) (kvec_unflatten256 res.`1) /\
           lifts_wpolykvec (kvec_unflatten256 res.`1) =
             (lifts_wpolykvec (kvec_unflatten256 _w0)) -
             (PolyKVec.invnttv (PolyKVec.ntt_smul
               (lifts_wpoly _c)
               (lifts_wpolykvec (kvec_unflatten256 _s2)))))
    ].
proof.
have kvec_val := mldsa65_kvec.
have gamma2_val := mldsa65_gamma2.
have tau_val := mldsa65_tau.
have eta_val := mldsa65_Eta.
proc => /=.
case (infinity_norm_check_result <> zero).
+ rcondt ^if;1: by auto.
  rcondf ^while;1: by auto.
  by auto => /#.
conseq (: _ ==>
  infinity_norm_check_result = zero =>
   (wpolykvec_infnorm (gamma2 - Beta) (kvec_unflatten256 w0_minus_cs2) /\
   lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2) =
   lifts_wpolykvec (kvec_unflatten256 _w0) -
   invnttv (ntt_smul (lifts_wpoly _c) (lifts_wpolykvec (kvec_unflatten256 _s2)))));
 1: by move => |> &hr ?? infncr rr => ?; rewrite to_uint_eq /= /#.
 
rcondf ^if; 1: by auto.
while (#{/~_incr}{~infinity_norm_check_result}pre /\
       (infinity_norm_check_result = zero \/ infinity_norm_check_result = one) /\
       0 <= base <= 6*n /\ base %% n = 0 /\
       (infinity_norm_check_result <> zero => base = 6*n) /\
      (
       infinity_norm_check_result = zero =>
       ((forall k, 0 <= k < base %/ n =>
           wpoly_srng (gamma2 - Beta - 1) (gamma2 - Beta - 1) ((kvec_unflatten256 w0_minus_cs2)).[k]) /\
       (forall k, 0 <= k < base %/ n =>
         (lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2)).[k] =
         (lifts_wpolykvec (kvec_unflatten256 _w0) -
         invnttv (ntt_smul (lifts_wpoly _c) (lifts_wpolykvec (kvec_unflatten256 _s2)))).[k]))
      )
      ); last first.

+ auto => /> ???; split; 1:smt().
  move => bs wmcs *;do split. 
  + by rewrite /wpolykvec_infnorm /wpolykvec_srng allP => *; smt().
  by apply KArray.tP => *;smt().

(* ── Loop body: one row at index i = base %/ n ──────────────────────── *)

seq 6 : (#pre /\
    lifts_wpoly (Array256.init (fun i => w0_minus_cs2.[base + i])) =
      (lifts_wpolykvec (kvec_unflatten256 _w0) -
       PolyKVec.invnttv (PolyKVec.ntt_smul
         (lifts_wpoly _c)
         (lifts_wpolykvec (kvec_unflatten256 _s2)))).[base %/ n] /\
    (* coefficients are centered representatives: to_sint = crepr *)
    wpoly_srng ((q-1) %/ 2) ((q-1) %/ 2)
               (Array256.init (fun i => w0_minus_cs2.[base + i]))).
+ admit.

wp.
ecall (polynomial____check_infinity_norm_correct
        (Array256.init (fun i => w0_minus_cs2.[base + i]))
        (gamma2 - Beta)).

auto => |> &hr  ?????? ?H H0 H1 H2 H3; split;1:smt().
move => ?? rr Ht Hf.
case (rr = W64.zero) => Hrr /=.
+ (* norm passed: rr = zero, new_incr = zero, update invariant *)
  do split; 1..3: smt().
  + move => k ??; case (k < base{hr} %/ n) => ?;1: by smt(). 
    have : wpoly_infnorm_lt (gamma2 - Beta) (init (fun (i : int) => _w0mc.[base{hr} + i])) by smt(W64.to_uint_eq W64.of_uintK W64.to_uintK pow2_64).
    rewrite /wpoly_infnorm_lt  /wpoly_srng !allP /= /kvec_unflatten256 => Hr kk kkb.
    rewrite initiE 1:/# /= get_of_list 1:/# /= nth_sub 1:/# /=.
    have := Hr kk _;1:smt().
    by rewrite initiE 1:/# /= /#.
 + move => k kb ?; case (k < base{hr} %/ n) => ?;1: by smt().
   have -> : k = base{hr} %/ n by smt().
   rewrite -H2 /lifts_wpolykvec mapiE 1:/#;congr;rewrite initiE 1:/# /= tP => j jb.
   rewrite get_of_list 1:/# nth_sub 1:/# initiE 1:/# /= /#.
by smt(W64.to_uint_eq W64.of_uintK W64.to_uintK pow2_64).
qed.

lemma __apply_cs2_and_check_norm_ph
      (_w0mc : W32.t Array1536.t) (_w0 : W32.t Array1536.t)
      (_s2 : W32.t Array1536.t) (_c : W32.t Array256.t)
      (_incr : W64.t)
      :
    phoare [ M.__apply_cs2_and_check_norm :
        w0_minus_cs2 = _w0mc /\ w0 = _w0 /\ s2 = _s2 /\
        verifier_challenge = _c /\ infinity_norm_check_result = _incr /\
        (_incr = W64.zero \/ _incr = W64.one) /\
        wpoly_ntt_orng _c /\
        wpolykvec_ntt_orng (kvec_unflatten256 _s2) /\
        (* w0 = LowBits(Ay), coefficients in (-gamma2, gamma2] = (-261888, 261888] *)
        wpolykvec_srng (kvec_unflatten256 _w0) (gamma2 - 1) gamma2
        ==>
        (_incr = W64.one => res.`2 = W64.one) /\
        (_incr = W64.zero =>
           res.`2 = W64.zero =>
           (* ||w0 - cs2||_inf < gamma2 - Beta = 261692 *)
           wpolykvec_infnorm (gamma2 - Beta) (kvec_unflatten256 res.`1) /\
           lifts_wpolykvec (kvec_unflatten256 res.`1) =
             (lifts_wpolykvec (kvec_unflatten256 _w0)) -
             (PolyKVec.invnttv (PolyKVec.ntt_smul
               (lifts_wpoly _c)
               (lifts_wpolykvec (kvec_unflatten256 _s2)))))
    ] = 1%r
  by conseq (__apply_cs2_and_check_norm_ll)
            (__apply_cs2_and_check_norm_correct _w0mc _w0 _s2 _c _incr).

(* ================================================================== *)
(* __apply_ct0_and_check_norm                                          *)
(* Called second; incr = result of cs2 check (0 or 1).               *)
(* Computes ct0 per row (K=6); checks infnorm < gamma2.              *)
(* If check passes: conditionally adds ct0 to w0_minus_cs2.           *)
(* Spec: ct0 = invnttv (ntt_smul ch t0h); output = w0mc + ct0        *)
(* Threshold: gamma2 = (q-1)/32 = 261888                              *)
(* ================================================================== *)

lemma __apply_ct0_and_check_norm_ll : islossless M.__apply_ct0_and_check_norm.
proof.
proc.
admit.
qed.

lemma __apply_ct0_and_check_norm_correct
      (_r : W32.t Array1536.t) (_w0mc : W32.t Array1536.t)
      (_t0 : W32.t Array1536.t) (_c : W32.t Array256.t)
      (_incr : W64.t)
      :
    hoare [ M.__apply_ct0_and_check_norm :
        w0_minus_cs2_plus_ct0 = _r /\ w0_minus_cs2 = _w0mc /\
        t0 = _t0 /\ verifier_challenge = _c /\
        infinity_norm_check_result = _incr /\
        (_incr = W64.zero \/ _incr = W64.one) /\
        wpoly_ntt_orng _c /\
        wpolykvec_ntt_orng (kvec_unflatten256 _t0) /\
        (* only needed when _incr = 0 (loop runs): w0mc passed cs2 norm check *)
        (_incr = W64.zero =>
          wpolykvec_infnorm (gamma2 - Beta) (kvec_unflatten256 _w0mc))
        ==>
        (_incr = W64.one => res.`2 = W64.one) /\
        (_incr = W64.zero =>
           res.`2 = W64.zero =>
           let ct0 = PolyKVec.invnttv (PolyKVec.ntt_smul
                       (lifts_wpoly _c)
                       (lifts_wpolykvec (kvec_unflatten256 _t0))) in
           (* ||ct0||_inf < gamma2 = 261888 *)
           PolyKVec.infnorm ct0 gamma2 /\
           lifts_wpolykvec (kvec_unflatten256 res.`1) =
             (lifts_wpolykvec (kvec_unflatten256 _w0mc)) + ct0)
    ].
proof.
admitted. (* 
have kvec_val := mldsa65_kvec.
have gamma2_val := mldsa65_gamma2.
have tau_val  := mldsa65_tau.
have eta_val  := mldsa65_Eta.
proc => /=.
case (infinity_norm_check_result <> zero).
+ rcondt ^if; 1: by auto.
  rcondf ^while; 1: by auto.
  by auto => /#.
conseq (: _ ==>
  infinity_norm_check_result = zero =>
  (let ct0 = PolyKVec.invnttv (PolyKVec.ntt_smul
               (lifts_wpoly _c) (lifts_wpolykvec (kvec_unflatten256 _t0))) in
   PolyKVec.infnorm ct0 gamma2 /\
   lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2_plus_ct0) =
     lifts_wpolykvec (kvec_unflatten256 _w0mc) + ct0));
 1: by move => |> &hr ?? infncr rr => ?; rewrite to_uint_eq /= /#.
rcondf ^if; 1: by auto.
while (#{/~_incr}{~infinity_norm_check_result}pre /\
       (infinity_norm_check_result = zero \/ infinity_norm_check_result = one) /\
       0 <= base <= 6*n /\ base %% n = 0 /\
       (infinity_norm_check_result <> zero => base = 6*n) /\
       (infinity_norm_check_result = zero =>
         let ct0 = PolyKVec.invnttv (PolyKVec.ntt_smul
                     (lifts_wpoly _c) (lifts_wpolykvec (kvec_unflatten256 _t0))) in
         (forall k, 0 <= k < base %/ n =>
           PolyKVec.infnorm_poly ct0.[k] gamma2) /\
         (forall k, 0 <= k < base %/ n =>
           (lifts_wpolykvec (kvec_unflatten256 w0_minus_cs2_plus_ct0)).[k] =
           (lifts_wpolykvec (kvec_unflatten256 _w0mc)).[k] + ct0.[k]))
      ); last first.
+ auto => /> ???; split; 1: smt().
  move => bs r *; do split.
  + move => k ?; rewrite /PolyKVec.infnorm_poly; smt().
  + by apply KArray.tP => *; smt().
admit. (* loop body: gamma2 threshold not yet in polynomial____check_infinity_norm_correct *)
qed. *)

lemma __apply_ct0_and_check_norm_ph
      (_r : W32.t Array1536.t) (_w0mc : W32.t Array1536.t)
      (_t0 : W32.t Array1536.t) (_c : W32.t Array256.t)
      (_incr : W64.t)
      :
    phoare [ M.__apply_ct0_and_check_norm :
        w0_minus_cs2_plus_ct0 = _r /\ w0_minus_cs2 = _w0mc /\
        t0 = _t0 /\ verifier_challenge = _c /\
        infinity_norm_check_result = _incr /\
        (_incr = W64.zero \/ _incr = W64.one) /\
        wpoly_ntt_orng _c /\
        wpolykvec_ntt_orng (kvec_unflatten256 _t0) /\
        (_incr = W64.zero =>
          wpolykvec_infnorm (gamma2 - Beta) (kvec_unflatten256 _w0mc))
        ==>
        (_incr = W64.one => res.`2 = W64.one) /\
        (_incr = W64.zero =>
           res.`2 = W64.zero =>
           let ct0 = PolyKVec.invnttv (PolyKVec.ntt_smul
                       (lifts_wpoly _c)
                       (lifts_wpolykvec (kvec_unflatten256 _t0))) in
           PolyKVec.infnorm ct0 gamma2 /\
           lifts_wpolykvec (kvec_unflatten256 res.`1) =
             (lifts_wpolykvec (kvec_unflatten256 _w0mc)) + ct0)
    ] = 1%r
  by conseq (__apply_ct0_and_check_norm_ll)
            (__apply_ct0_and_check_norm_correct _r _w0mc _t0 _c _incr).

(* ================================================================== *)
(* __compute_z_and_check_norm                                          *)
(* Called third; incr = combined result of cs2+ct0 checks (0 or 1).  *)
(* Computes z = mask + c*s1 per column (L=5); checks infnorm < gamma1-Beta *)
(* Spec: z = y + invnttv (ntt_smul ch s1h)                           *)
(* Threshold: gamma1 - Beta = 2^19 - tau*Eta = 524092                *)
(* ================================================================== *)

lemma __compute_z_and_check_norm_ll : islossless M.__compute_z_and_check_norm.
proof.
proc.
admit.
qed.

lemma __compute_z_and_check_norm_correct
      (_s1 : W32.t Array1280.t) (_c : W32.t Array256.t)
      (_mask : W32.t Array1280.t) (_z0 : W32.t Array1280.t)
      (_incr : W64.t)
      :
    hoare [ M.__compute_z_and_check_norm :
        s1 = _s1 /\ verifier_challenge = _c /\
        mask = _mask /\ signer_response = _z0 /\
        infinity_norm_check_result = _incr /\
        (_incr = W64.zero \/ _incr = W64.one) /\
        wpoly_ntt_orng _c /\
        wpolylvec_ntt_orng (lvec_unflatten256 _s1) /\
        (* only needed when _incr = 0 (loop runs): mask from ExpandMask *)
        (_incr = W64.zero =>
          wpolylvec_srng (lvec_unflatten256 _mask) (gamma1 - 1) gamma1)
        ==>
        (_incr = W64.one => res.`2 = W64.one) /\
        (_incr = W64.zero =>
           res.`2 = W64.zero =>
           (* ||z||_inf < gamma1 - Beta = 524092 *)
           wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 res.`1) /\
           lifts_wpolylvec (lvec_unflatten256 res.`1) =
             (lifts_wpolylvec (lvec_unflatten256 _mask)) +
             (PolyLVec.invnttv (PolyLVec.ntt_smul
               (lifts_wpoly _c)
               (lifts_wpolylvec (lvec_unflatten256 _s1)))) /\
           wpolylvec_srng (lvec_unflatten256 res.`1) (gamma1 - 1) gamma1)
    ].
proof.
admitted.
(* 
have lvec_val  := mldsa65_lvec.
have gamma1_val := mldsa65_gamma1.
have tau_val   := mldsa65_tau.
have eta_val   := mldsa65_Eta.
proc => /=.
case (infinity_norm_check_result <> zero).
+ rcondt ^if; 1: by auto.
  rcondf ^while; 1: by auto.
  by auto => /#.
conseq (: _ ==>
  infinity_norm_check_result = zero =>
  (wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 signer_response) /\
   lifts_wpolylvec (lvec_unflatten256 signer_response) =
     lifts_wpolylvec (lvec_unflatten256 _mask) +
     PolyLVec.invnttv (PolyLVec.ntt_smul
       (lifts_wpoly _c) (lifts_wpolylvec (lvec_unflatten256 _s1))) /\
   wpolylvec_srng (lvec_unflatten256 signer_response) (gamma1 - 1) gamma1));
 1: by move => |> &hr ?? infncr rr => ?; rewrite to_uint_eq /= /#.
rcondf ^if; 1: by auto.
while (#{/~_incr}{~infinity_norm_check_result}pre /\
       (infinity_norm_check_result = zero \/ infinity_norm_check_result = one) /\
       0 <= base <= 5*n /\ base %% n = 0 /\
       (infinity_norm_check_result <> zero => base = 5*n) /\
       (infinity_norm_check_result = zero =>
         ((forall k, 0 <= k < base %/ n =>
             wpoly_srng (gamma1 - Beta - 1) (gamma1 - Beta - 1) ((lvec_unflatten256 signer_response)).[k]) /\
          (forall k, 0 <= k < base %/ n =>
            (lifts_wpolylvec (lvec_unflatten256 signer_response)).[k] =
            (lifts_wpolylvec (lvec_unflatten256 _mask) +
             PolyLVec.invnttv (PolyLVec.ntt_smul
               (lifts_wpoly _c) (lifts_wpolylvec (lvec_unflatten256 _s1)))).[k]))
       )
      ); last first.
+ auto => /> ???; split; 1: smt().
  move => bs srs *; do split.
  + by rewrite /wpolylvec_infnorm_lt /wpolylvec_srng allP => *; smt().
  + by apply LArray.tP => *; smt().
  + admit. (* gamma1 range on z: follows from norm check but needs NTT bounds *)

(* ── Loop body: one column at index base %/ n ──────────────────── *)
seq 6 : (#pre /\
    lifts_wpoly (Array256.init (fun i => signer_response.[base + i])) =
      (lifts_wpolylvec (lvec_unflatten256 _mask) +
       PolyLVec.invnttv (PolyLVec.ntt_smul
         (lifts_wpoly _c)
         (lifts_wpolylvec (lvec_unflatten256 _s1)))).[base %/ n] /\
    (* coefficients are centered representatives: to_sint = crepr *)
    wpoly_srng ((q-1) %/ 2) ((q-1) %/ 2)
               (Array256.init (fun i => signer_response.[base + i]))).
+ admit.

wp.
ecall (polynomial____check_infinity_norm_correct
        (Array256.init (fun i => signer_response.[base + i]))
        (gamma1 - Beta)).

auto => |> &hr ?????? ?H H0 H1 H2 H3; split; 1: smt().
move => ?? rr Ht Hf.
case (rr = W64.zero) => Hrr /=.
+ (* norm passed: update invariant for new column *)
  do split; 1..3: smt().
  + move => k ??; case (k < base{hr} %/ n) => ?; 1: by smt().
    have : wpoly_infnorm_lt (gamma1 - Beta) (init (fun (i : int) => _mask.[base{hr} + i])) by smt(W64.to_uint_eq W64.of_uintK W64.to_uintK pow2_64).
    rewrite /wpoly_infnorm_lt /wpoly_srng !allP /= /lvec_unflatten256 => Hr kk kkb.
    rewrite initiE 1:/# /= get_of_list 1:/# /= nth_sub 1:/# /=.
    have := Hr kk _; 1: smt().
    by rewrite initiE 1:/# /= /#.
  + move => k kb ?; case (k < base{hr} %/ n) => ?; 1: by smt().
    have -> : k = base{hr} %/ n by smt().
    rewrite -H2 /lifts_wpolylvec mapiE 1:/#; congr; rewrite initiE 1:/# /= tP => j jb.
    rewrite get_of_list 1:/# nth_sub 1:/# initiE 1:/# /= /#.
by smt(W64.to_uint_eq W64.of_uintK W64.to_uintK pow2_64).
qed.*)

lemma __compute_z_and_check_norm_ph
      (_s1 : W32.t Array1280.t) (_c : W32.t Array256.t)
      (_mask : W32.t Array1280.t) (_z0 : W32.t Array1280.t)
      (_incr : W64.t)
      :
    phoare [ M.__compute_z_and_check_norm :
        s1 = _s1 /\ verifier_challenge = _c /\
        mask = _mask /\ signer_response = _z0 /\
        infinity_norm_check_result = _incr /\
        (_incr = W64.zero \/ _incr = W64.one) /\
        wpoly_ntt_orng _c /\
        wpolylvec_ntt_orng (lvec_unflatten256 _s1) /\
        (_incr = W64.zero =>
          wpolylvec_srng (lvec_unflatten256 _mask) (gamma1 - 1) gamma1)
        ==>
        (_incr = W64.one => res.`2 = W64.one) /\
        (_incr = W64.zero =>
           res.`2 = W64.zero =>
           wpolylvec_infnorm_lt (gamma1 - Beta) (lvec_unflatten256 res.`1) /\
           lifts_wpolylvec (lvec_unflatten256 res.`1) =
             (lifts_wpolylvec (lvec_unflatten256 _mask)) +
             (PolyLVec.invnttv (PolyLVec.ntt_smul
               (lifts_wpoly _c)
               (lifts_wpolylvec (lvec_unflatten256 _s1)))) /\
           wpolylvec_srng (lvec_unflatten256 res.`1) (gamma1 - 1) gamma1)
    ] = 1%r
  by conseq (__compute_z_and_check_norm_ll)
            (__compute_z_and_check_norm_correct _s1 _c _mask _z0 _incr).

(* ================================================================== *)
(* __make_hint_vector                                                  *)
(* Called fourth; incr = combined result of all three norm checks.    *)
(* Computes h = MakeHint(-ct0, w-cs2+ct0) per row (K=6).            *)
(* Checks total hint count <= omega = 55.                             *)
(* Note: ct0 at spec level is passed as parameter by the caller.      *)
(* ================================================================== *)

lemma __make_hint_vector_ll : islossless M.__make_hint_vector.
proof.
proc.
admit.
qed.

lemma __make_hint_vector_correct
      (_r : W32.t Array1536.t) (_w1 : W32.t Array1536.t)
      (_h : W32.t Array1536.t) (_incr : W64.t)
      (_ct0 : polykvec)
      :
    hoare [ M.__make_hint_vector :
        w0_minus_cs2_plus_ct0 = _r /\ w1 = _w1 /\ hint_0 = _h /\
        infinity_norm_check_result = _incr /\
        (_incr = W64.zero \/ _incr = W64.one)
        ==>
        (_incr = W64.one => res.`2 = W64.one) /\
        (_incr = W64.zero =>
           res.`2 = W64.zero =>
           liftu_wpolykvec (kvec_unflatten256 res.`1) =
             PolyKVec.MakeHint (PolyKVec.zerov - _ct0)
                               (lifts_wpolykvec (kvec_unflatten256 _r)) /\
           PolyKVec.hammw (liftu_wpolykvec (kvec_unflatten256 res.`1)) w_hint)
    ].
proof.
admitted.
(* 
have kvec_val  := mldsa65_kvec.
have w_hint_val := mldsa65_w_hint.
proc => /=.
case (infinity_norm_check_result <> zero).
+ rcondt ^if; 1: by auto.
  rcondf ^while; 1: by auto.
  by auto => /#.
conseq (: _ ==>
  infinity_norm_check_result = zero =>
  (liftu_wpolykvec (kvec_unflatten256 hint_0) =
     PolyKVec.MakeHint (PolyKVec.zerov - _ct0)
                       (lifts_wpolykvec (kvec_unflatten256 _r)) /\
   PolyKVec.hammw (liftu_wpolykvec (kvec_unflatten256 hint_0)) w_hint));
 1: by move => |> &hr ?? infncr rr => ?; rewrite to_uint_eq /= /#.
rcondf ^if; 1: by auto.
while (#{/~_incr}{~infinity_norm_check_result}pre /\
       (infinity_norm_check_result = zero \/ infinity_norm_check_result = one) /\
       0 <= base <= 6*n /\ base %% n = 0 /\
       (infinity_norm_check_result <> zero => base = 6*n) /\
       (infinity_norm_check_result = zero =>
         (forall k, 0 <= k < base %/ n =>
           (liftu_wpolykvec (kvec_unflatten256 hint_0)).[k] =
           (PolyKVec.MakeHint (PolyKVec.zerov - _ct0)
                              (lifts_wpolykvec (kvec_unflatten256 _r))).[k])
       )
      ); last first.
+ auto => /> ???; split; 1: smt().
  move => bs h *; do split.
  + by apply KArray.tP => *; smt().
  + admit. (* hammw <= w_hint: follows from loop count but needs accounting *)
admit. (* loop body: MakeHint spec connection *)
qed. *)

lemma __make_hint_vector_ph
      (_r : W32.t Array1536.t) (_w1 : W32.t Array1536.t)
      (_h : W32.t Array1536.t) (_incr : W64.t)
      (_ct0 : polykvec)
      :
    phoare [ M.__make_hint_vector :
        w0_minus_cs2_plus_ct0 = _r /\ w1 = _w1 /\ hint_0 = _h /\
        infinity_norm_check_result = _incr /\
        (_incr = W64.zero \/ _incr = W64.one)
        ==>
        (_incr = W64.one => res.`2 = W64.one) /\
        (_incr = W64.zero =>
           res.`2 = W64.zero =>
           liftu_wpolykvec (kvec_unflatten256 res.`1) =
             PolyKVec.MakeHint (PolyKVec.zerov - _ct0)
                               (lifts_wpolykvec (kvec_unflatten256 _r)) /\
           PolyKVec.hammw (liftu_wpolykvec (kvec_unflatten256 res.`1)) w_hint)
    ] = 1%r
  by conseq (__make_hint_vector_ll)
            (__make_hint_vector_correct _r _w1 _h _incr _ct0).
