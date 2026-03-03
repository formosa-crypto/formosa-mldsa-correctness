require import AllCore List (* IntDiv RealExp StdBigop *).

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2 Mldsa_65_prelude Matrix_A Error_vectors T0 T1 S1 S2 Hashing.
(* from JazzEC require import Array32. *)

from Spec require import GFq Rq Serialization Conversion Parameters VecMat
                         Symmetric Sampling MLDSA_W32_Rep MLDSA.

import PolyLVec PolyKVec PolyMat.
import CDR Round Zq PolyReduceZq BigZMod.

(* require import ArrayExtra JWord_extra EclibExtra JWordList. *)

require import Array32 Array64 Array128 Array256 Array320 Array640 Array768 Array1280 Array1536 Array1920 Array1952 Array2496 Array4032 Array7680.
require import WArray32 WArray1952 WArray4032.

require import Bindings.

lemma keygen_internal
    (RO <: LeakyRO):
    equiv [ MLDSA(MLDSA_XOFA, MLDSA_XOFS, RO).keygen_derand ~ M.__keygen_internal :
       Bytes32.to_list arg{1} = to_list arg{2}.`3
     ==>
       BytesPK.to_list res{1}.`2 = to_list res{2}.`1 /\
       BytesSK.to_list res{1}.`1 = to_list res{2}.`2
   ].
proof.
have Hkvec := mldsa65_kvec.
proc => /=.
seq 0 13 : #pre; 1: by auto.

(* expanding seeds *)
sp 2 0.
seq 0 2 : (#pre /\
 to_list prf_output{2} =
   Bytes32.to_list rho{1} ++ Bytes64.to_list rhop{1} ++ Bytes32.to_list _K{1}).
+ admit. (* TODO: REFACTORING TO USE FORMOSA-KECCAK *)

(* expanding A *)
seq 1 2: (#pre /\ liftu_wpolymat (mat_unflatten256 matrix_A{2}) = _A{1} /\
            wpolymat_urng (mat_unflatten256 matrix_A{2}) 1).
+ ecall{1} (ExpandA_correct rho{1}).
  ecall{2} (matrix_A_correct seed_for_matrix_A{2}).
  auto => /> &1 &2 _ _ H.
  have Hn : forall i, 0 <= i < 128 => prf_output{2}.[i] =
                     nth witness (Bytes32.to_list rho{1} ++ Bytes64.to_list rhop{1} ++ Bytes32.to_list _K{1}) i.
  + by  move => kk kkb;rewrite -H  ?size_to_list 1:/#  !get_to_list.
  move => rr -> ?;congr.
  apply Bytes32.tP => k kb;rewrite Bytes32.get_of_list // get_to_list initiE 1:/# /=.  
  by rewrite  Hn 1:/# -catA nth_cat ?Bytes32.size_to_list ifT 1:/#  Bytes32.get_to_list.

(* expanding noise *)
seq 0 2 : (#pre
     /\ to_list seed_for_error_vectors{2} = Bytes64.to_list rhop{1}
     /\ to_list seed_for_signing{2} = Bytes32.to_list _K{1}).
+ auto => /> &1 &2 _ _ H ?.
  have Hn : forall i, 0 <= i < 128 => prf_output{2}.[i] =
                     nth witness (Bytes32.to_list rho{1} ++ Bytes64.to_list rhop{1} ++ Bytes32.to_list _K{1}) i.
  + by  move => kk kkb;rewrite -H  ?size_to_list 1:/#  !get_to_list.
  split;apply (eq_from_nth witness);rewrite size_to_list ?Bytes32.size_to_list ?Bytes64.size_to_list //= => k kb; rewrite initiE 1:/# /= Hn 1:/# -catA nth_cat ?Bytes32.size_to_list ifF 1:/# nth_cat ?Bytes64.size_to_list.
  + by rewrite ifT 1:/# Bytes64.get_to_list /#.
  by rewrite ifF 1:/# Bytes32.get_to_list /#.

seq 1 1 : (#pre
     /\ lifts_wpolylvec (lvec_unflatten256 s1{2}) = s1{1}
     /\ wpolylvec_srng (lvec_unflatten256 s1{2}) Eta Eta
     /\ lifts_wpolykvec (kvec_unflatten256 s2{2}) = s2{1}
     /\ wpolykvec_srng (kvec_unflatten256 s2{2}) Eta Eta).
+ ecall{1} (ExpandS_correct rhop{1}).
  ecall{2} (error_vectors_correct seed_for_error_vectors{2}).
  auto => /> &1 &2 _ _ _ _ ->.
  by rewrite !Bytes64.to_listK => _ rr -> ? -> ?.

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

  auto => /> &1 &2 ?????????? rr1 Hrr11 rr2 Hrr21 Hrr22 rr3 Hrr31  rr4 Hrr41 Hrr42 rr5 Hrr5.
  split.
  + rewrite BytesPK.of_listK. 
    + rewrite size_cat Bytes32.size_to_list (size_flatten_ctt 320).
      + move =>x; rewrite mapP => He; elim He => xx /=.
        rewrite /to_list mkseqP => [# He ->]; elim He => xxx /= => [# ??].
        rewrite mapiE 1:/# initiE 1:/# /= => ->.
        rewrite SimpleBitPack_liftE. admit.
        by rewrite size_to_list.
      by rewrite size_map /= size_to_list /#.
    admit.
  admit.

admit.

qed.
