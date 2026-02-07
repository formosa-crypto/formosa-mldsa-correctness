require import AllCore List IntDiv RealExp.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2.
from JazzEC require import Array256 Array128.
from Spec require import GFq Rq Serialization Conversion Parameters VecMat MLDSA_W32_Rep.
import BitEncoding BitChunking.

import CDR Round Zq.

require import ArrayExtra JWord_extra EclibExtra JWordList.

require import Array640 Array1280.

import VecMat PolyKVec.

require import Array1536 Array3309.

op  decoded_unflatten(a : 'a Array1536.t) =
     KArray.init (fun i => Array256.of_list witness (sub a (256*i) 256)).

     
op count_nonzero_coeffs(p : poly) = size (filter (fun c => c = Zq.one) (to_list p)).
op count_nonzero_coeffs_kvec(v : polykvec) =
     foldl (+) 0 (map count_nonzero_coeffs (to_list v)).

(* Helper: count ones in first i complete polynomials plus first j coeffs of poly i *)
op count_nonzero_prefix(h : polykvec) (i j : int) : int =
  foldl (+) 0 (map count_nonzero_coeffs (mkseq (fun k => h.[k]) i)) +
  (if 0 <= i < kvec then
     size (filter (fun c => c = Zq.one) (mkseq (fun k => h.[i].[k]) j))
   else 0).

op touch_hint(sig_in sig_out : W8.t Array3309.t) =
    forall k, 0<=k<3248 =>
       sig_in.[k] = sig_out.[k].

lemma encode_hint _signature _hint :
    w_hint = 55 =>
    kvec = 6 =>
    equiv [ HintPackUnpack.hintBitPack ~ M.signature____encode_hint :
       wpolykvec_urng (decoded_unflatten hint_0{2}) 2
    /\ count_nonzero_coeffs_kvec (decoded_unflatten _hint) = w_hint
    /\ arg{1} = decoded_unflatten _hint
    /\ arg{2}.`1 = _signature
    /\ liftu_wpolykvec (decoded_unflatten arg{2}.`2) =  decoded_unflatten _hint
     ==>
      res{1} = mkseq (fun i => res{2}.[3248 + i]) (w_hint+kvec) /\
      touch_hint _signature res{2}
   ].
proof.
move => w_hint_eq kvec_eq.
proc => /=.
seq 3 4 : (#{/~signature{2} = _signature}pre
   /\ y{1} = mkseq (fun i => signature{2}.[3248 + i]) (w_hint+kvec)
   /\ touch_hint _signature signature{2}
   /\ index{1} = 0
   /\ hints_written{2} = 0
   /\ i{1} = 0
   /\ i{2} = 0).
+ (* Initialize y to zeros and set counters to 0 *)
  conseq (: _ ==>
     y{1} = mkseq (fun (i0 : int) => signature{2}.[3248 + i0]) hint_bytes
     /\ touch_hint _signature{2} signature{2}
     /\ index{1} = 0
     /\ i{1} = 0
     /\ hints_written{2} = 0
     /\ i{2} = 0); 1: by smt().
  inline *; wp.
  while {2} (0 <= i{2} <= w_hint+kvec
   /\ (forall k, 0 <= k < i{2} =>
               signature{2}.[3248 + k] = W8.zero)
   /\ touch_hint _signature signature{2});
   last by auto => />; smt(eq_in_mkseq).
  by auto => /> &hr; smt(get_setE).
  by move => ?;while(true) (61-i); auto => /> /#.
(* Main nested loops *)
seq 1 2 : (#{/~i{1}}{i{2}}{index{1}}{hints_written{2}}pre
    /\ count_nonzero_coeffs_kvec (decoded_unflatten _hint) = w_hint
   /\ touch_hint _signature signature{2}
   /\ size y{1} = w_hint + kvec
   /\ i{1} = kvec
   /\ i{2} = kvec
   /\ index{1} = hints_written{2}
   /\ index{1} = w_hint
   /\ (forall k, 0 <= k < index{1} =>
        y{1}.[k] = signature{2}.[3248 + k])
   /\ (forall k, 0 <= k < kvec =>
        y{1}.[w_hint + k] = signature{2}.[3248 + w_hint + k])); last first.
+ auto => /> &1 &2 ????H2.
  + apply (eq_from_nth W8.zero); 1: by rewrite size_mkseq;smt().
    move => i ib; rewrite nth_mkseq 1:/# /=. 
    case (i < w_hint) => ?;1:smt().
    by have  := H2 (i - w_hint) _; smt().
+ (* Outer loop over polynomials *)
  while (
    wpolykvec_urng (decoded_unflatten hint_0{2}) 2 /\
    count_nonzero_coeffs_kvec (decoded_unflatten _hint) = w_hint /\
    h{1} = decoded_unflatten _hint /\
    liftu_wpolykvec (decoded_unflatten hint_0{2}) = decoded_unflatten _hint /\           
    size y{1} = hint_bytes /\
    0 <= i{1} <= kvec /\
    i{1} = i{2} /\
    0 <= index{1} <= w_hint /\
    index{1} = hints_written{2} /\
    index{1} = count_nonzero_prefix (decoded_unflatten _hint) i{1} 0 /\
    (* Encoding matches for positions written so far *)
    (forall k, 0 <= k < index{1} =>
      y{1}.[k] = signature{2}.[3248 + k]) /\
    (* Cumulative counts match for completed polynomials *)
    (forall k, 0 <= k < i{1} =>
       y{1}.[w_hint + k] = signature{2}.[3248 + w_hint + k]) /\
    touch_hint _signature signature{2} /\
    condition1{2} = (i{2} < 6)
  ); last first.
 + auto => /> &1 &2 ???;do split;1..3,5..7:smt(size_mkseq).
    + by rewrite /count_nonzero_prefix /= !mkseq0 /=.
    + move => y1 c1 i2 s2 ????????H2??;do split;1..2,4..: smt().
      + by rewrite /count_nonzero_prefix ifF 1:/# /= /#.
  wp. (* Inner while loop *)
  while (
       wpolykvec_urng (decoded_unflatten hint_0{2}) 2 /\
       count_nonzero_coeffs_kvec (decoded_unflatten _hint) = w_hint /\
        h{1} = decoded_unflatten _hint /\
        liftu_wpolykvec (decoded_unflatten hint_0{2}) = decoded_unflatten _hint /\           
        size y{1} = hint_bytes /\
        0 <= i{1} < kvec /\
        i{1} = i{2} /\
        0 <= index{1} <= w_hint /\
        index{1} = hints_written{2} /\
        index{1} = count_nonzero_prefix (decoded_unflatten _hint) i{1} j{1} /\
        0 <= j{1} <= 256 /\
        j{1} = j{2} /\
        (forall k, 0 <= k < index{1} =>
          y{1}.[k] = signature{2}.[3248 + k]) /\
        (forall k, 0 <= k < i{1} =>
          y{1}.[w_hint + k] = signature{2}.[3248 + w_hint + k]) /\
        touch_hint _signature signature{2} /\
        condition2{2} = (j{2} < 256)
  ); last first.
  + auto => /> &1 &2 Hrng ????????????  y1 c1 j2 s2 ????????H2??; do split;1..3,8..:smt(size_put).
    + rewrite /count_nonzero_prefix ifT 1:/#.
      case (i{2} + 1 = kvec) => ?.
      + rewrite ifF 1:/# /= mkseqS /= 1:/# map_rcons -cats1 foldl_cat /= /#.
      rewrite ifT 1:/# mkseq0 /= mkseqS /= 1:/# map_rcons -cats1 foldl_cat /= /#.
   + move => k??; rewrite nth_put;smt(get_setE).
   + move => k??;rewrite nth_put 1:/# /=.
     case (i{2} = k) => * ;smt(get_setE).
   + by smt(get_setE).

 seq 0 4 : (#pre /\
     to_uint hint_coefficient{2} =
        asint h{1}.[i{1}].[j{1}]).
 + auto => /> &1 &2 Hrng ? Hh2 ???????????.
   move : Hrng; rewrite /wpolykvec_urng allP /= => Hrng.
   have := Hrng i{2} _;1:smt().
   rewrite /wpoly_urng allP /= => Hrngp.
   have := Hrngp j{2} _; 1:smt().
   move : Hh2; rewrite /liftu_wpolykvec tP => Hh2.
   have := Hh2 i{2} _; 1:smt().
   rewrite mapiE 1:/# /=.
   rewrite /liftu_wpoly tP => Hh2p.
   have := Hh2p j{2} _;1:smt().
   rewrite mapiE 1:/# /=.
   rewrite /(`<<`) /= /decoded_unflatten initiE 1:/# /=.
   rewrite get_of_list 1:/# /= nth_sub 1:/# /=.
   rewrite initiE 1:/# /= get_of_list 1:/# /= nth_sub 1:/# /=.
   by move => <-; rewrite incoeffK /#.

if.
 + auto => /> &1 &2 Hrng ? Hh2 ???????????.
   move : Hrng; rewrite /wpolykvec_urng allP /= => Hrng.
   have := Hrng i{2} _;1:smt().
   rewrite /wpoly_urng allP /= => Hrngp.
   have := Hrngp j{2} _; 1:smt().
   move : Hh2; rewrite /liftu_wpolykvec tP => Hh2.
   have := Hh2 i{2} _; 1:smt().
   rewrite mapiE 1:/# /=.
   rewrite /liftu_wpoly tP => Hh2p.
   have := Hh2p j{2} _;1:smt().
   rewrite mapiE 1:/# /=.
   rewrite /decoded_unflatten initiE 1:/# /=.
   rewrite get_of_list 1:/# /= nth_sub 1:/# /=.
   rewrite initiE 1:/# /= get_of_list 1:/# /=.
   rewrite nth_sub 1:/# /=.
   move => <- => +; rewrite !to_uint_eq /= incoeffK.
   by rewrite /one -!eq_incoeff /#.
  + auto => /> &1 &2 ???????????????Hone; do split; 1..2,5..6,9:smt(get_setE size_put). 
   + admit.
   + move : Hone;rewrite /decoded_unflatten /count_nonzero_prefix ifT 1:/# ifT 1:/# /= mkseqS 1:/# initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /= => ->.
     by rewrite filter_rcons /= size_rcons /#.
   + smt(get_setE size_put nth_put). 
   + move => k kbl kbh; rewrite nth_put.
     + admit.
     case (count_nonzero_prefix (decoded_unflatten _hint) i{2} j{2} = w_hint + k);  smt(get_setE). 
+ auto => /> &1 &2 ???????????????Hone; do split; 2..:smt().
   + move : Hone;rewrite /decoded_unflatten /count_nonzero_prefix ifT 1:/# ifT 1:/# /= mkseqS 1:/# initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /=.
     rewrite filter_rcons /= /#. 
qed.
