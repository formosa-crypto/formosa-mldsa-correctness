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

lemma keygen_internal
    (RO <: LeakyRO):
    equiv [ MLDSA(MLDSA_XOFA, MLDSA_XOFS, RO).keygen_derand ~ M.__keygen_internal :
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
seq 0 13 : #pre; 1: by auto.

(* expanding seeds *)
sp 2 0.
seq 0 2 : (#pre /\
 prf_output{2} =
   Array128.of_list witness (Bytes32.to_list rho{1} ++ Bytes64.to_list rhop{1} ++ Bytes32.to_list _K{1})).
+ admit. (* TODO: REFACTORING TO USE FORMOSA-KECCAK *)

(* expanding A *)
sp;seq 1 1: (#pre /\ liftu_wpolymat (mat_unflatten256 matrix_A{2}) = _A{1} /\
            wpolymat_urng (mat_unflatten256 matrix_A{2}) 1).
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
   t <@ M.row_vector____multiply_with_matrix_A(matrix_A, s1p);
}; 1: by sim.

swap {2} [10..16] -9.

seq 2 7 : (#pre
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

  auto => /> ?????? rr1 Hrr1 rr2 Hrr2 rr3 Hrr3  rr4 Hrr4.
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
    
admit. (* ToDo: Algebra *)
qed.
