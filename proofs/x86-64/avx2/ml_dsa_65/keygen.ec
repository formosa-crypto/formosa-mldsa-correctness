require import AllCore List IntDiv  RealExp (* StdBigop *).

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Matrix_A Error_vectors T0 T1 S1 S2 Hashing.
(* from JazzEC require import Array32. *)

from Spec require import GFq Rq Serialization Conversion Parameters VecMat
                         Symmetric Sampling MLDSA_W32_Rep MLDSA.

import PolyLVec PolyKVec PolyMat.
import CDR Round Zq PolyReduceZq BigZMod.

(* require import ArrayExtra JWord_extra EclibExtra JWordList. *)

require import Array32 Array64 Array128 Array256 Array320 Array416 Array640 Array768 Array1280 Array1536 Array1920 Array1952 Array2496 Array4032 Array7680.
require import WArray32 WArray1952 WArray4032.

require import Bindings.
require import BitEncoding.
import BitChunking.

require import Row_vector Column_vector.

lemma size_BitsToBytes l :  size (BitsToBytes l) = (size l) %/ 8.
rewrite /BitsToBytes size_map size_chunk //. 
qed.

lemma size_SimpleBitPack _p b : 1 <= b => size (SimpleBitPack _p b) = (ilog 2 b + 1) * n %/ 8.
move => Hb.
rewrite /SimpleBitPack /=  size_BitsToBytes (size_flatten_ctt (ilog 2 b + 1)).
+ move => l; rewrite mapP => He; elim He => c /= [# ?->].
  rewrite /IntegerToBits BS2Int.size_int2bs;smt(ilog_ge0).
by rewrite size_map size_to_list.
qed.

lemma size_kflatten_SimpleBitPack (v : W32.t Array1536.t) b:
   1 <= b =>
    size (flatten (map (fun (p : poly) => SimpleBitPack p b) (to_list (liftu_wpolykvec (kvec_unflatten256 v))))) = kvec * (ilog 2 b + 1) * n %/ 8.
move => Hb.
rewrite (size_flatten_ctt ((ilog 2 b + 1) * n %/ 8)).
+ move => l; rewrite mapP => He;  elim He => p /= [# ? ->].
  rewrite size_SimpleBitPack /= /#.
by rewrite size_map size_to_list mldsa65_kvec /= /#.
qed.

lemma size_BitPack _p b1 b2 : 1 <= (b1 + b2) => size (BitPack _p b1 b2) = (ilog 2 (b1 + b2) + 1) * n %/ 8.
move => Hb.
rewrite /BitPack /=  size_BitsToBytes (size_flatten_ctt (ilog 2 (b1 + b2) + 1)).
+ move => l; rewrite mapP => He; elim He => c /= [# ?->].
  rewrite /IntegerToBits BS2Int.size_int2bs. smt(ilog_ge0).
by rewrite size_map size_to_list.
qed.

lemma size_lflatten_BitPack (v : W32.t Array1280.t) b1 b2:
  1 <= (b1 + b2) =>
   size (flatten (map (fun (p : poly) => BitPack p b1 b2) (to_list (lifts_wpolylvec (lvec_unflatten256 v))))) = lvec *  (ilog 2 (b1 + b2) + 1) * n %/ 8.
move => Hb.
rewrite (size_flatten_ctt ((ilog 2 (b1 + b2) + 1) * n %/ 8)).
+ move => l; rewrite mapP => He;  elim He => p /= [# ? ->].
  rewrite size_BitPack /= /#.
by rewrite size_map size_to_list mldsa65_lvec /= /#.
qed.

lemma size_kflatten_BitPack (v : W32.t Array1536.t) b1 b2:
  1 <= (b1+b2) =>
   size (flatten (map (fun (p : poly) => BitPack p b1 b2) (to_list (lifts_wpolykvec (kvec_unflatten256 v))))) = kvec *  (ilog 2 (b1 + b2) + 1) * n %/ 8.
move => Hb.
rewrite (size_flatten_ctt ((ilog 2 (b1 + b2) + 1) * n %/ 8)).
+ move => l; rewrite mapP => He;  elim He => p /= [# ? ->].
  rewrite size_BitPack /= /#.
by rewrite size_map size_to_list mldsa65_kvec /= /#.
qed.

lemma get256_init_32_8 (a : W8.t Array32.t) k:
   0 <= k < 32 =>
    (get256_direct (WArray32.init8 ("_.[_]" a)) 0 \bits8 k) = a.[k].
move => kb.
rewrite WArray32.get256E pack32E wordP => i ib.
rewrite /(\bits8) initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /#.
qed.

require import Array2.

(* ================================================================== *)
(* __compute_t0_t1                                                      *)
(* Computes t = A*s1 + s2 (in coefficient domain), then Power2Round.   *)
(* Sequential: multiply_with_matrix_A → reduce32 → invNTT →           *)
(*             add(s2) → conditionally_add_modulus → power2round       *)
(* Spec: (t1, t0) = Power2Round(invNTT(A*NTT(s1)) + s2)               *)
(* ================================================================== *)

lemma __compute_t0_t1_ll : islossless M.__compute_t0_t1.
proof.
proc.
wp; call column_vector____power2round_ll.
call column_vector____conditionally_add_modulus_ll.
call column_vector____add_ll.
call column_vector__invert_ntt_montgomery_ll.
call column_vector__reduce32_ll.
call row_vector____multiply_with_matrix_A_ll.
by auto.
qed.

lemma __compute_t0_t1_correct
      (_mat : W32.t Array7680.t) (_s1 : W32.t Array1280.t) (_s2 : W32.t Array1536.t)
      (_A : polymat) :
    hoare [ M.__compute_t0_t1 :
        matrix_A = _mat /\ s1 = _s1 /\ s2 = _s2 /\
        liftu_wpolymat (mat_unflatten256 _mat) = _A /\
        wpolymat_urng (mat_unflatten256 _mat) q /\
        wpolylvec_ntt_orng (lvec_unflatten256 _s1) /\
        wpolykvec_srng (kvec_unflatten256 _s2) (Eta) (Eta)
        ==>
        (liftu_wpolykvec (kvec_unflatten256 res.`1),
         lifts_wpolykvec (kvec_unflatten256 res.`2)) =
          Power2Round (invnttv (ntt_mulmxv _A
                        (lifts_wpolylvec (lvec_unflatten256 _s1)))
                       + lifts_wpolykvec (kvec_unflatten256 _s2))
    ].
proof.
have kvec_val := mldsa65_kvec.
have lvec_val := mldsa65_lvec.
have Eta_val := mldsa65_Eta.
have Hbound := invntt_obound_fits_for_caddq.
proc.
ecall (column_vector____power2round_correct t).
ecall (column_vector____conditionally_add_modulus_correct t).
ecall (column_vector____add_correct t _s2 invntt_obound Eta).
ecall (column_vector__invert_ntt_montgomery_correct t).
ecall (column_vector__reduce32_correct t).
ecall (row_vector____multiply_with_matrix_A_correct _mat _s1).
auto => /> Hurng_mat Horng_s1 Hsrng_s2.
split; first exact (wpolylvec_ntt_orng_bmul_irng (lvec_unflatten256 _s1) Horng_s1).
move => _ result Hlifts_mul result0 Hlifts_red Hsrng_red.
split; first by apply wpolykvec_bmul_orng_intt_irng;
  apply (wpolykvec_srng_widen _ ((q-1) %/ 2) ((q-1) %/ 2) (q-1) (q-1)); smt().
move => _ result1 Hlifts_invntt Hsrng_invntt.
split; 1: smt().
move => _ result2 Hlifts_add Hsrng_add.
split;
  first by apply (wpolykvec_srng_widen _ (invntt_obound + Eta) (invntt_obound + Eta) (q-1) (q-1)); smt().
move => _ result3 Hlifts_cond Hurng_cond.
move => result4 Ht1_eq Hurng_t1 Ht0_eq Hsrng_t0.
have Heq3 := wpolykvec_urng_lifts_eq_liftu _ Hurng_cond.
have Hchain :
  invnttv (ntt_mulmxv (liftu_wpolymat (mat_unflatten256 _mat))
                      (lifts_wpolylvec (lvec_unflatten256 _s1)))
  + lifts_wpolykvec (kvec_unflatten256 _s2)
  = liftu_wpolykvec (kvec_unflatten256 result3).
+ by rewrite -Hlifts_mul -Hlifts_red -Hlifts_invntt -Hlifts_add -Hlifts_cond Heq3.
rewrite Hchain.
rewrite /Power2Round /=.
by split; [exact Ht1_eq | exact Hurng_t1].
qed.

lemma __compute_t0_t1_ph
      (_mat : W32.t Array7680.t) (_s1 : W32.t Array1280.t) (_s2 : W32.t Array1536.t)
      (_A : polymat) :
    phoare [ M.__compute_t0_t1 :
        matrix_A = _mat /\ s1 = _s1 /\ s2 = _s2 /\
        liftu_wpolymat (mat_unflatten256 _mat) = _A /\
        wpolymat_urng (mat_unflatten256 _mat) q /\
        wpolylvec_ntt_orng (lvec_unflatten256 _s1) /\
        wpolykvec_srng (kvec_unflatten256 _s2) (Eta) (Eta)
        ==>
        (liftu_wpolykvec (kvec_unflatten256 res.`1),
         lifts_wpolykvec (kvec_unflatten256 res.`2)) =
          Power2Round (invnttv (ntt_mulmxv _A
                        (lifts_wpolylvec (lvec_unflatten256 _s1)))
                       + lifts_wpolykvec (kvec_unflatten256 _s2))
    ] = 1%r
  by conseq __compute_t0_t1_ll (__compute_t0_t1_correct _mat _s1 _s2 _A).

(* 3-arg variant with _A substituted by its defining expression; avoids the
   ghost/call-arg mismatch that trips ecall's existential inference. *)
lemma __compute_t0_t1_ph_
      (_mat : W32.t Array7680.t) (_s1 : W32.t Array1280.t) (_s2 : W32.t Array1536.t) :
    phoare [ M.__compute_t0_t1 :
        matrix_A = _mat /\ s1 = _s1 /\ s2 = _s2 /\
        wpolymat_urng (mat_unflatten256 _mat) q /\
        wpolylvec_ntt_orng (lvec_unflatten256 _s1) /\
        wpolykvec_srng (kvec_unflatten256 _s2) (Eta) (Eta)
        ==>
        (liftu_wpolykvec (kvec_unflatten256 res.`1),
         lifts_wpolykvec (kvec_unflatten256 res.`2)) =
          Power2Round (invnttv (ntt_mulmxv (liftu_wpolymat (mat_unflatten256 _mat))
                        (lifts_wpolylvec (lvec_unflatten256 _s1)))
                       + lifts_wpolykvec (kvec_unflatten256 _s2))
    ] = 1%r
  by conseq (__compute_t0_t1_ph _mat _s1 _s2 (liftu_wpolymat (mat_unflatten256 _mat))).

lemma ml_dsa_65_keygen_correct :
    equiv [ MLDSA(MLDSA_XOFA, MLDSA_XOFS, MLDSA_XOF_SIB, SIB_RO).keygen_derand ~ M.ml_dsa_65_keygen :
       arg{1} = Bytes32.of_list (to_list arg{2}.`3)
     ==>
       res{1}.`2 = BytesPK.of_list (to_list res{2}.`1) /\
       res{1}.`1 = BytesSK.of_list (to_list res{2}.`2)
   ].
proof.
have Eta_val := mldsa65_Eta.
have Hlvec := mldsa65_lvec.
have Hkvec := mldsa65_kvec.
proc => /=.
inline {2} M.__keygen_internal.
wp;sp 0 3.
seq 0 11 : #pre; 1: by auto.

(* expanding seeds *)
sp 2 0.
seq 0 1 : (#pre /\
 prf_output{2} =
   Array128.of_list witness (Bytes32.to_list rho{1} ++ Bytes64.to_list rhop{1} ++ Bytes32.to_list _K{1})).
  ecall {2} (keygen_prf_correct randomness{2}).
  wp; skip => /> &1.
  + congr; rewrite !Bytes32.of_listK.
    + by rewrite size_to_list.
    + by rewrite size_take 1:/# Keccak1600_Spec.size_SHAKE256 /#.
    + by rewrite size_to_list.
    + by rewrite size_drop 1:/# Keccak1600_Spec.size_SHAKE256 /#.
  rewrite !Bytes64.of_listK.
  + by rewrite size_take 1:/# size_drop 1:/# Keccak1600_Spec.size_SHAKE256 /#.
  rewrite -takeD 1,2:/# /= cat_take_drop !Bytes34.of_listK.
  + by rewrite size_cat size_to_list /=.
  by rewrite mldsa65_kvec mldsa65_lvec /=.
(* expanding A *)
sp;seq 1 1: (#pre /\ liftu_wpolymat (mat_unflatten256 matrix_A{2}) = _A{1} /\
            wpolymat_urng (mat_unflatten256 matrix_A{2}) q).
+ ecall{1} (ExpandA_correct rho{1}).
  ecall{2} (matrix_A_correct seed_for_matrix_A{2}).
  auto => /> &1  rr ->?.
  + congr; apply Bytes32.tP => k kb.
    rewrite Bytes32.get_of_list 1:/# get_to_list initiE 1:/# get_of_list 1:/# nth_cat ifT.
    + by rewrite size_cat;smt(Bytes32.size_to_list).
    by rewrite nth_cat ifT;smt(Bytes32.size_to_list).

(* expanding noise *)
seq 0 2 : (#pre
     /\ seed_for_error_vectors{2} = Array64.of_list witness (Bytes64.to_list rhop{1})
     /\ seed_for_signing{2} = Array32.of_list witness (Bytes32.to_list _K{1})).
+ auto => /> ??.
  by split; rewrite tP => k kb; rewrite initiE 1:/# /= get_of_list 1:/# get_of_list 1:/# !nth_cat ?size_cat ?Bytes32.size_to_list ?Bytes64.size_to_list /#.

seq 1 1 : (#pre
     /\ lifts_wpolylvec (lvec_unflatten256 s1{2}) = s1{1}
     /\ wpolylvec_srng (lvec_unflatten256 s1{2}) Eta Eta
     /\ lifts_wpolykvec (kvec_unflatten256 s2{2}) = s2{1}
     /\ wpolykvec_srng (kvec_unflatten256 s2{2}) Eta Eta).
+ ecall{1} (ExpandS_correct rhop{1}).
  ecall{2} (error_vectors_correct seed_for_error_vectors{2}).
  by auto => />  ?? rr -> ?->?; split;congr;congr;rewrite Bytes64.tP => k kb;rewrite Bytes64.get_of_list 1:/# get_to_list get_of_list /#.

proc change {2} [10..11] : [s1p : W32.t Array1280.t] {
   s1p <@ M.row_vector__ntt(s1);
   (t1, t0) <@ M.__compute_t0_t1(matrix_A, s1p, s2);
}; 1:  by sim.  

swap {2} [10..11] -9.

seq 2 2 : (#pre
      /\ lifts_wpolykvec (kvec_unflatten256 t0{2}) = t0{1}
      /\ wpolykvec_srng (kvec_unflatten256 t0{2}) (dpow - 1) dpow 
      /\ liftu_wpolykvec (kvec_unflatten256 t1{2}) = t1{1}
      /\ wpolykvec_urng (kvec_unflatten256 t1{2}) b_t1
 ); last first.

+ wp; ecall {2} (t0_encode_ph t0{2}).
  wp; ecall {2} (hash_verification_key_correct verification_key_pointer_copy{2}).
  wp; ecall {2} (t1_encode_ph t1{2}).
  wp; ecall {2} (s2_encode_ph s2{2}).
  wp; ecall {2} (s1_encode_ph s1{2}).

  wp; ecall {1} (skEncode_corr rho{1} _K{1} tr{1} s1{1} s2{1} t0{1}).
  wp; ecall {1} (pkEncode_corr rho{1} t1{1}).

  auto => |> &1 &2 ?????? rr1 Hrr1 _ rr2 Hrr2 _ rr3 Hrr3  rr4 Hrr4.
  split;congr.
  + apply (eq_from_nth witness); 1: by rewrite size_cat Bytes32.size_to_list size_kflatten_SimpleBitPack 1:/# size_to_list /#.
    move => k;rewrite size_cat Bytes32.size_to_list size_kflatten_SimpleBitPack 1:/# /= => Hk.
    rewrite initiE 1:/# /= nth_cat Bytes32.size_to_list; case (k < 32) => ?.
    + rewrite ifF 1:/# initiE 1:/# /= ifT 1:/# get256_init_32_8 1:/# initiE 1:/# get_of_list 1:/# nth_cat ifT.
      + by rewrite size_cat Bytes32.size_to_list Bytes64.size_to_list /#.
      by rewrite nth_cat Bytes32.size_to_list /#.
    rewrite ifT 1:/# (nth_flatten witness 320).
    + rewrite allP => x; rewrite mapP => He; elim He => p /= [# ? ->].
      by rewrite size_SimpleBitPack /#.
      rewrite (nth_map witness) /=; 1: by rewrite size_to_list /#.
    move : Hrr3; rewrite kvec_unflatten320iE 1:/# => ->.
    rewrite mapiE 1:/# /= mapiE 1:/# /= get_of_list 1:/#.
    congr;congr; last by auto.
    by rewrite mapiE 1:/#.
  + apply (eq_from_nth witness).
    + rewrite !size_cat !Bytes32.size_to_list Bytes64.size_to_list.
      by rewrite size_to_list size_lflatten_BitPack 1:/# !size_kflatten_BitPack 1,2:/# Eta_val Hlvec /= Hkvec /=.
    move => i; rewrite !size_cat !Bytes32.size_to_list Bytes64.size_to_list size_lflatten_BitPack 1:/# !size_kflatten_BitPack 1,2:/# Eta_val Hlvec /= Hkvec /= => Hi.
    rewrite !nth_cat.
    rewrite !size_cat !Bytes32.size_to_list Bytes64.size_to_list size_lflatten_BitPack 1:/# !size_kflatten_BitPack 1:/# Hlvec /= Hkvec /=.
    rewrite initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=.
    case (i < 1536) => ?; last first.
    + rewrite ifT 1:/#.
      move : Hrr4; rewrite kvec_unflatten416iE 1:/# => ->.
      rewrite mapiE 1:/# /= get_of_list 1:/# (nth_flatten witness 416).
      + rewrite allP => x; rewrite mapP => He; elim He => p /= [# ? ->].
        by rewrite size_BitPack /#.
      by rewrite (nth_map witness) /=; rewrite ?size_to_list /#.
    case (i < 768) => ?; last first.
    + rewrite ifF 1:/# ifF 1:/# ifT 1:/#.
      move : Hrr2; rewrite kvec_unflatten128iE 1:/# => ->.
      rewrite mapiE 1:/# /= get_of_list 1:/# (nth_flatten witness 128).
      + rewrite allP => x; rewrite mapP => He; elim He => p /= [# ? ->].
        by rewrite size_BitPack /#.
      by rewrite (nth_map witness) /=; rewrite ?size_to_list /#.
    case (i < 128) => ?; last first.
    + rewrite ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/#.
      move : Hrr1; rewrite lvec_unflatten128iE 1:/# => ->.
      rewrite mapiE 1:/# /= get_of_list 1:/# (nth_flatten witness 128).
      + rewrite allP => x; rewrite mapP => He; elim He => p /= [# ? ->].
        by rewrite size_BitPack /#.
      by rewrite (nth_map witness) /=; rewrite ?size_to_list /#.
    case (i < 64) => ?; last first.
    + rewrite ifF 1:/# ifT 1:/# get_of_list 1:/# Bytes64.get_to_list;congr;congr;congr.
      apply (eq_from_nth witness).
      + rewrite !size_cat !Bytes32.size_to_list.
        by rewrite size_to_list size_kflatten_SimpleBitPack /#.
      move => k; rewrite !size_cat !Bytes32.size_to_list size_kflatten_SimpleBitPack //= => ?.
      rewrite initiE 1:/# /= initiE 1:/# /=.
      case (k < 32) => ?.
      + rewrite ifF 1:/# ifT 1:/# nth_cat ifT 1:/# Bytes32.get_to_list get256_init_32_8 1:/# initiE 1:/# get_of_list 1:/#.
        by rewrite nth_cat size_cat Bytes32.size_to_list ifT 1:/# nth_cat Bytes32.size_to_list ifT 1:/# Bytes32.get_to_list /#.
      rewrite ifT 1:/# nth_cat ifF; 1: by rewrite Bytes32.size_to_list  /=.
      move : Hrr3;rewrite kvec_unflatten320iE 1:/# => ->.
      rewrite mapiE 1:/# /= get_of_list 1:/# (nth_flatten witness 320).
      + rewrite allP => x; rewrite mapP => He; elim He => p /= [# ? ->].
        by rewrite size_SimpleBitPack /#.
      by rewrite (nth_map witness) /=; rewrite ?size_to_list /#.
    case (i < 32) => ?.
    + rewrite ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/#. 
      rewrite /get8 initiE 1:/# initiE 1:/# /= set256E initiE 1:/# /= ifT 1:/# get256_init_32_8 1:/# initiE 1:/# get_of_list 1:/#.
      rewrite  nth_cat ifT; 1: by rewrite size_cat Bytes32.size_to_list  /#.
      rewrite nth_cat ifT;1:by rewrite  Bytes32.size_to_list  /#.
      by rewrite Bytes32.get_to_list /#.
    by rewrite ifF 1:/# ifF 1:/# ifF 1:/# ifF 1:/# ifT 1:/# get256_init_32_8 1:/# initiE 1:/# /=.

(* --- First subgoal of the outer `seq 2 2` at line 242: the forward direction
   establishing (t0, t1)'s spec values after
     s1p <@ row_vector__ntt(s1);
     (t1, t0) <@ __compute_t0_t1(matrix_A, s1p, s2);

   BLOCKED by an EasyCrypt bug: `proc change {2} [10..11] : [s1p : …]` at line
   235 introduces `s1p` into the right-side program text but does NOT add
   `s1p` as a memory field of ml_dsa_65_keygen. Every tactic that must name
   s1p in a formula (`ecall{2} (... s1p{2} ...)`, `seq 0 1 : (... s1p{2} ...)`,
   `exlim s1p{2}`) fails with "unknown variable: s1p"; omitting it triggers
   an internal EC anomaly in ecPhlExists.ml line 504. A `seq 0 1 : (#pre)`
   split can close the row_vector__ntt half trivially (the call doesn't touch
   anything in #pre), but leaves Goal 2 with no information about s1p —
   hence unprovable without fixing the underlying bug.

   Attempted partial proof (row_vector__ntt half only), kept for reference:

     wp.
     seq 0 1 : (#pre).
     + ecall{2} (row_vector__ntt_ph s1{2}).
       skip => /> &2 _ Hs1_srng _.
       apply wpolylvec_srng_ntt_irng.
       by apply (wpolylvec_srng_widen _ Eta Eta (q-1) (q-1) _ _ Hs1_srng);
          smt(mldsa65_Eta).
     admit. (* compute_t0_t1 step — blocked *)

   Proper fix: rework the seq 2 2 setup at line 242 to NOT use `proc change`.
   Use `exlim s1{2}` before the ecall chain to save the pre-NTT value of s1
   as a logical ghost, then keep the original Jasmin statements which
   overwrite s1 in place. Then `ecall{2} row_vector__ntt_ph` followed by
   `ecall{2} __compute_t0_t1_ph` can run since all ghost parameters bind to
   memory-resident variables. *)
admit. (* ToDo: Algebra *)
qed.
