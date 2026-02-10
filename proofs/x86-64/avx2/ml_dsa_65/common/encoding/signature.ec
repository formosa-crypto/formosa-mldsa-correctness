require import AllCore List IntDiv RealExp StdBigop.

from Jasmin require import JModel_x86.

from JazzEC require import Ml_dsa_65_avx2.
from JazzEC require import Array256 Array61 Array1536 Array3309.
from Spec require import GFq Rq Serialization Conversion Parameters VecMat MLDSA_W32_Rep.
import BitEncoding BitChunking.

import CDR Round Zq.

require import ArrayExtra JWord_extra EclibExtra JWordList.

import VecMat PolyKVec.

op  decoded_unflatten(a : 'a Array1536.t) =
     KArray.init (fun i => Array256.of_list witness (sub a (256*i) 256)).

lemma decoded_unflattenE i j (h : 'a Array1536.t) (P : 'a -> bool) :
   kvec = 6 =>
   0 <= i < kvec =>
   0 <= j < 256 =>
        all (all P) (decoded_unflatten h) =>
        P h.[i*256+j].
move => ???;rewrite allP => Hii.
have := Hii i _;1:smt().
rewrite allP => Hjj. 
have := Hjj j _;1:smt().
by rewrite initiE 1:/# /= get_of_list 1:/# /= nth_sub /#. 
qed.

lemma decoded_unflattenP i j (h1 : 'a Array1536.t) (h2 : 'b Array1536.t) (F : 'a -> 'b) :
   kvec = 6 =>
   0 <= i < kvec =>
   0 <= j < 256 =>
        map (map F) (decoded_unflatten h1) = decoded_unflatten h2 =>
        F h1.[i*256+j] = h2.[i*256+j].
move => ???; rewrite tP => Hii.
have := Hii i _; 1:smt().
rewrite tP => Hjj.
have := Hjj j _; 1:smt().
rewrite mapiE 1:/# /= mapiE 1:/# /= initiE 1:/# initiE 1:/# /=.
by rewrite !get_of_list 1,2:/# /= !nth_sub /#. 
qed.

lemma decode_hint :
    w_hint = 55 =>
    kvec = 6 =>
    equiv [ HintPackUnpack.hintBitUnpack ~ M.signature____decode_hint :
       arg{1} = to_list arg{2}.`2 
     ==>
      (res{1} = None  => res{2}.`2 = -W64.one) /\
      (res{1} <> None =>
         res{2}.`2 = W64.zero /\
         liftu_wpolykvec (decoded_unflatten res{2}.`1) = oget res{1} /\
         wpolykvec_urng (decoded_unflatten res{2}.`1) 2)
   ].
proof.
move => whint kvec.
proc => /=.
wp; conseq (_: _ ==>
      (error{1} => ill_formed_hint{2} = W64.one) /\
      (!error{1} =>
         ill_formed_hint{2} = W64.zero /\
   liftu_wpolykvec (decoded_unflatten hints{2}) = h{1} /\
   wpolykvec_urng (decoded_unflatten hints{2}) 2)).
+ auto => /> error1 h1 h2 error2 He Hne;split;1:smt().
  move => ?; move : Hne; have ->/= : error1 = false; 1:smt().
  move => [#] ->?? /=;split;1:by ring.
  by smt().

(* Initialization *)
seq 3 2  :
  (#pre /\
   !error{1} /\
   index{1} = previous_true_hints_seen{2} /\
   (error{1} => ill_formed_hint{2} = W64.one) /\
   (!error{1} => ill_formed_hint{2} = W64.zero));
   1: by auto => />.

(* Check for zero *)
seq 2 5 :
  (#{/~!error{1}}{~index{1} = previous_true_hints_seen{2}}pre /\
   (!error{1} => index{1} = previous_true_hints_seen{2}) /\
   (error{1} => ill_formed_hint{2} = W64.one) /\
   (!error{1} => ill_formed_hint{2} = W64.zero) /\
   (!error{1} =>
      liftu_wpolykvec (decoded_unflatten hints{2}) = h{1} /\
      wpolykvec_urng (decoded_unflatten hints{2}) 2)
  ); last first.
+ while (#post /\
     y{1} = to_list hint_encoded{2} /\
     (!error{1} => index{1} = encoded_offset {2})); last first.
   + auto => /> &1 &2 ??Hne?;split; 1: smt().
     do split;rewrite /SETcc.
     + move => ??;case (55 <= previous_true_hints_seen{2}) => ?.
       + rewrite wordP => i ib; rewrite orwE /=;smt(W8.nth_one). 
       by rewrite Hne 1:/# or0w /truncateu8 /= /#.
     + case (55 <= previous_true_hints_seen{2}) => ?.
       + rewrite wordP => Hw; have /= := Hw 0 _;1:smt().
       by rewrite W8.nth_one /=.
    by rewrite or0w /truncateu8 /= to_uint_eq /= => ?;smt(W64.to_uint1 W64.to_uint0).
   case (to_uint (nth witness y{1} index{1}) <> 0).
   + rcondt {1} ^if;1: by auto.
     rcondt {2} ^if; 1: by  auto => /> *; rewrite to_uint_eq to_uint_zeroextu64 /#.
     rcondf {2} ^if; 1: by auto => />;by smt(W64.to_uint1 W64.to_uint0).
     auto => /> &1 &2 ?????;rewrite /SETcc.
     case (55 <= encoded_offset{2}) => ?;1: smt(W8.wordP orwE W8.nth_one).
     by rewrite or0w /truncateu8 /= to_uint_eq /=.
   + rcondf {1} ^if;1: by auto.
     rcondf {2} ^if; 1: by auto => /> *;rewrite to_uint_eq  to_uint_zeroextu64 /#.
     rcondt {2} ^if; 1: by auto => />;by smt(W64.to_uint1 W64.to_uint0).
     auto => /> &1 &2 ??????;split;1:smt().
     rewrite /SETcc;split.
     +  case (55 <= encoded_offset{2} + 1) => ?;1: smt(W8.wordP orwE W8.nth_one).
        by rewrite or0w /truncateu8 /= to_uint_eq /=;by smt(W64.to_uint1 W64.to_uint0).
     case (55 <= encoded_offset{2} + 1) => ?;2: smt(W64.to_uint1 W64.to_uint0).
     rewrite wordP => Hw; have /= := Hw 0 _;1:smt().
     by rewrite W8.nth_one /=.

(* Main loop *)
while (0 <= i{1} <= kvec /\
    i{1} = encoded_offset{2} /\
   y{1} = to_list hint_encoded{2} /\
   (error{1} => ill_formed_hint{2} = W64.one) /\
  (!error{1} => index{1} = previous_true_hints_seen{2}) /\
  (error{1} => ill_formed_hint{2} = W64.one) /\
  (!error{1} => ill_formed_hint{2} = W64.zero) /\
  (!error{1} =>
     forall k, 0 <= k < i{1} =>
       (liftu_wpolykvec (decoded_unflatten hints{2})).[k] = h{1}.[k] /\
       wpoly_urng 2 (decoded_unflatten hints{2}).[k])); last first.
+ auto => /> &1 &2 *;do split;1..3:smt().
  move => e1 h1 d12 eo2 h2 if2 ?????????H H0;split.
  + rewrite tP => k kb.
    have := H H0 k _;smt().
  rewrite /wpolykvec_urng allP => k kb.
  by have := H H0 k _;smt().

seq 0 2 : (#pre /\ decoded_offset{2} = 256*encoded_offset{2});
  1: by auto => /> &1 &2 ???????;rewrite /(`<<`) /= /#.

(* Set Zero *)
seq 1 2 : (#pre /\ 
      (liftu_wpolykvec (decoded_unflatten hints{2})).[i{1}] = h{1}.[i{1}] /\
      wpoly_urng 2 (decoded_unflatten hints{2}).[i{1}]).
 + wp; conseq />;1:smt().
   while {2} (0 <= j{2} <= n /\ 0 <= encoded_offset{2} < kvec /\
      decoded_offset{2} = encoded_offset{2} * n /\
     (forall (k : int),
        0 <= k < encoded_offset{2} =>
          (liftu_wpolykvec (decoded_unflatten hints{2})).[k] =
            h{1}.[k] /\
     wpoly_urng 2 (decoded_unflatten hints{2}).[k]) /\
     (forall jj, 0 <= jj < j{2} =>
  (decoded_unflatten hints{2}).[encoded_offset{2}].[jj] = W32.zero)) (n - j{2}); last first.
   + auto => /> &1 &2 ????????;split;1:smt().
   move  => h2 j2;split;1:smt().
   move => ??????H; do split.
   + move => k kbl kbh.
     split.
     + by rewrite mapiE 1:/# get_setE 1:/# ifF 1:/#; smt(KArray.mapiE).
     by smt(KArray.allP).
   + rewrite get_setE 1:/# ifT 1:/# tP => k kb.
    by  rewrite mapiE 1:/# /= Array256.initiE 1:/# /=  mapiE 1:/# /= H 1:/# /=.
   + rewrite /wpoly_urng allP => k kb /=.
     by rewrite H /#.
 + move => &1 _z;auto => /> &2 ???? H H0 ?; do split; 1,2,5:smt().
   + move => k kbl kbh.
     have  := H k _;1:smt().
     rewrite mapiE 1:/# /= tP /wpoly_urng allP => [# HH HH0].
     split.
     + rewrite mapiE 1:/# /= tP => kk kkb.
       rewrite mapiE 1:/# /= initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /=.
       by have := HH kk kkb; rewrite  initiE 1:/# /= mapiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /= get_setE /#.
   +  rewrite allP => kk kkb /=;rewrite initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /= get_setE 1:/#.
     have /= := HH0 kk kkb.
     rewrite initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /= => HH1.
     by smt().
   + move => jj jjbl jjbh.
     rewrite initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /=.
     case (jj = j{2}) => ?.
     + by rewrite get_setE 1:/# ifT 1:/#.
     rewrite get_setE 1:/# ifF 1:/#.
     have /= := H0 jj _;1:smt().
     by rewrite initiE 1:/# /= get_of_list 1:/# nth_sub /#.

 sp 0 1;if{2}.
 + rcondt{1} 1.
   + auto => /> &2 ??????????H;left.
     by move : H; rewrite to_uint_zeroextu64 /#.
     auto => /> &1 &2 *;do split;1:smt(W64.to_uint_eq W64.to_uint0 W64.to_uint1). 
     move => ?; rewrite /SETcc /= wordP.
     smt(@W8 @W64).
 if{2}.
 + rcondt{1} 1;1: by auto => /> &2 ??????????; rewrite to_uint_zeroextu64 /= /#.
   auto => /> &1 &2 *;do split;1:smt(W64.to_uint_eq W64.to_uint0 W64.to_uint1). 
   move => ?; rewrite /SETcc /= wordP.
   smt(@W8 @W64).

   
rcondf{1} 1.
+ auto => /> &2 ?????????H H0.
  move :H H0; rewrite !to_uint_zeroextu64 /= => *.
  by rewrite oraE  negb_or /#.

seq 1 4 : (#pre /\
    j{2} = index{1} /\
    _first{1} = previous_true_hints_seen{2} /\
    ((done2{2} = W8.zero) =
      (index{1} < to_uint (nth witness y{1} (w_hint + i{1})) && !error{1}))).
 + auto => /> &1 &2 ?????????.
   rewrite /SETcc to_uint_zeroextu64 /= => H H0.
   have -> : truncateu8 ill_formed_hint{2} = W8.zero; last by rewrite W8.orw0;smt(W8.to_uint_eq W8.to_uint0 W8.to_uint1).
   have -> : ill_formed_hint{2} = W64.zero by smt().
   by simplify.


 seq 1 1 : (
  (* Core equalities and bounds *)
  0 <= i{1} <= kvec /\
  i{1} < kvec /\
  i{1} = encoded_offset{2} /\
  y{1} = to_list hint_encoded{2} /\
  j{2} = index{1} /\
  _first{1} = previous_true_hints_seen{2} /\
  index{1} <= to_uint hint_encoded{2}.[w_hint + encoded_offset{2}] /\

  
  (* Hint encoding *)
  current_true_hints_seen{2} = to_uint (zeroextu64 hint_encoded{2}.[55 + encoded_offset{2}]) /\
  
  (* Offset relation *)
  decoded_offset{2} = n * encoded_offset{2} /\
  
  (* Ill-formed hint state *)
  (error{1} => ill_formed_hint{2} = W64.one) /\
  (!error{1} => ill_formed_hint{2} = W64.zero) /\
  
  (* Correctness invariants *)
  (!error{1} =>
    forall (k : int), 0 <= k < i{1} + 1=>
      (liftu_wpolykvec (decoded_unflatten hints{2})).[k] = h{1}.[k] /\
      wpoly_urng 2 (decoded_unflatten hints{2}).[k]) /\
  
  (* Loop control *)
  done2{2} <> W8.zero /\
  ((done2{2} = W8.zero) <=>
    (index{1} < to_uint (nth witness y{1} (w_hint + i{1})) && !error{1}))

 ); last first.
 + if{2}; auto => /> &1 &2 [#] *; do split;3:smt(W8u8.to_uint_zeroextu64).
   move => ?; do split;1..3:smt(W8u8.to_uint_zeroextu64).
   + by move => ?; rewrite /SETcc /truncateu8 /= /#.
   + rewrite /SETcc /truncateu8 /=;smt(@W8u8 @W8 @W64).
   + rewrite /SETcc /truncateu8 /=;smt(@W8u8 @W8 @W64).
   + rewrite /SETcc /truncateu8 /=;smt(@W8u8 @W8 @W64).

 while (#{/~done2{2} <> W8.zero}post); last by auto => />;smt(W8u8.to_uint_zeroextu64).

if {1}.
+ seq 1 2 : (#{/~!error{1}}pre /\ error{1} /\ ill_formed_hint{2} = W64.one).
  + rcondt {2} 2; 1: by  auto => /> /#.
    rcondt {2} 3;1: by auto => /> &hr *;rewrite uleE /= !to_uint_zeroextu64 /#.
    by auto.
    auto => /> => &1 &2 [#] ????????;split;1:smt(@W64).
    move => ?; rewrite /SETcc !to_uint_zeroextu64 /truncateu8 /=.
    rewrite !wordP;split =>  *;smt(@W8 W8.orwE W8.nth_one).

seq 0 2 : (#pre /\
    hint_at_j{2} = zeroextu64 hint_encoded{2}.[j{2}]).
+ auto => /> &1 &2 ???????????.
  by rewrite !to_uint_eq !uleE /= !to_uint_zeroextu64 /#.

rcondt {2} 1; 1: by auto => /> /#.

auto => /> &1 &2 ??????H????.
have ? : 0<= to_uint hint_encoded{2}.[index{1}]  < 256 by smt(W8.to_uint_cmp pow2_8).
have -> : to_uint (W64.of_int (n * encoded_offset{2}) + zeroextu64 hint_encoded{2}.[index{1}]) =
      n*encoded_offset{2} + to_uint hint_encoded{2}.[index{1}].
+ rewrite to_uintD_small; 1: by rewrite of_uintK /= to_uint_zeroextu64 /#.
  by rewrite of_uintK /= modz_small 1:/# to_uint_zeroextu64 /#.

  
do split;1:smt().
+ move => k kbl kbh;split.
  rewrite mapiE 1:/# initiE 1:/# /= tP => kk kkb.
  rewrite mapiE 1:/# /= get_of_list 1:/# /= nth_sub 1:/# /=.
  have := H _ k _;1,2:smt().
  rewrite mapiE 1:/# initiE 1:/# /= tP => [# H1 H2].
  have := H1 kk _;1:smt().
  rewrite mapiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /= => H3.
  rewrite !get_setE 1,2:/#. 
  case (k = encoded_offset{2}) => ? ; last by smt().
  case (kk = to_uint hint_encoded{2}.[index{1}]) => ?;2: by smt(Array256.get_setE).
  by rewrite ifT 1:/# /=; smt(Array256.get_setE).

+ rewrite /wpoly_urng allP => kk kkb /=.
  have [?+] := H _ k _;1,2:smt().
  rewrite /wpoly_urng allP /= => H1.
  rewrite initiE 1:/# /= get_of_list 1:/# /= nth_sub 1:/# /= get_setE 1:/#.
  have := H1 kk _;1:smt().
  rewrite initiE 1:/# initiE 1:/# /= nth_sub 1:/#.
  by case (n * k + kk = n * encoded_offset{2} + to_uint hint_encoded{2}.[index{1}]) => //=.

+ rewrite /SETcc to_uint_zeroextu64 /=; smt(@W8 @W64).
+ rewrite /SETcc to_uint_zeroextu64 /=; smt(@W8 @W64).
+ rewrite /SETcc to_uint_zeroextu64 /=; smt(@W8 @W64).
+ rewrite /SETcc to_uint_zeroextu64 /=; smt(@W8 @W64).
    
qed.






 
op count_nonzero_coeffs(p : poly) = count (fun c => c = Zq.one) (to_list p).

import Bigint BIA. 
op count_nonzero_coeffs_kvec(v : polykvec) =
     big predT count_nonzero_coeffs (to_list v).

op count_nonzero_prefix(v : polykvec) (i j : int) : int =
  big predT count_nonzero_coeffs (take i (to_list v)) +
  (if 0 <= i < kvec then
     count (fun c => c = Zq.one) (take j (to_list v.[i]))
   else 0).

lemma count_nonzero_prefix_one(v : coeff Array1536.t) (i j : int)  :
   0 <= i < kvec =>
   0 <= j < n =>
   (decoded_unflatten v).[i].[j] = Zq.one =>
   count_nonzero_coeffs_kvec (decoded_unflatten v) <= w_hint =>
      count_nonzero_prefix (decoded_unflatten v) i j < w_hint.
move => ???.
rewrite /count_nonzero_coeffs_kvec /count_nonzero_prefix ifT 1:/#.
have {1}<- := cat_take_drop i (to_list (decoded_unflatten v)).
rewrite big_cat.
have {1}<- := cat_take_drop 1 (drop i (to_list (decoded_unflatten v))).
rewrite (drop_take1_nth witness);1: by rewrite size_to_list 1:/#.
rewrite big_cat /= drop_drop 1,2:/# /= big_cons big_nil /= ifT 1:/#.
have :  count (fun (c : coeff) => c = Zq.one) (take j (to_list (decoded_unflatten v).[i])) <
  count_nonzero_coeffs (decoded_unflatten v).[i]; last by smt(count_ge0 sumr_ge0_seq).
rewrite /count_nonzero_coeffs.
have {2}<- := cat_take_drop j (to_list (decoded_unflatten v).[i]).
rewrite count_cat.
have {1}<- := cat_take_drop 1 (drop j (to_list (decoded_unflatten v).[i])).
rewrite (drop_take1_nth witness);1: by rewrite size_to_list 1:/#.
by rewrite count_cat /= drop_drop 1,2:/# /=;smt(count_ge0).
qed.

op touch_hint(sig_in sig_out : W8.t Array3309.t) =
    forall k, 0<=k<3248 =>
       sig_in.[k] = sig_out.[k].

lemma encode_hint _signature _hint :
    w_hint = 55 =>
    kvec = 6 =>
    equiv [ HintPackUnpack.hintBitPack ~ M.signature____encode_hint :
       wpolykvec_urng (decoded_unflatten hint_0{2}) 2
    /\ count_nonzero_coeffs_kvec (decoded_unflatten _hint) <= w_hint
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
     /\ touch_hint _signature signature{2}
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
  by auto => /> &hr; smt(Array3309.get_setE).
  by move => ?;while(true) (61-i); auto => /> /#.
(* Main nested loops *)
seq 1 2 : (#{/~i{1}}{i{2}}{index{1}}{hints_written{2}}pre
    /\ count_nonzero_coeffs_kvec (decoded_unflatten _hint) <= w_hint
   /\ touch_hint _signature signature{2}
   /\ size y{1} = w_hint + kvec
   /\ i{1} = kvec
   /\ i{2} = i{1}
   /\ index{1} = hints_written{2}
   /\ index{1} <= w_hint
   /\  y{1} = mkseq (fun (i0 : int) => signature{2}.[3248 + i0]) hint_bytes); last by auto.
+ (* Outer loop over polynomials *)
  while (
    wpolykvec_urng (decoded_unflatten hint_0{2}) 2 /\
    count_nonzero_coeffs_kvec (decoded_unflatten _hint) <= w_hint /\
    h{1} = decoded_unflatten _hint /\
    liftu_wpolykvec (decoded_unflatten hint_0{2}) = decoded_unflatten _hint /\           
    size y{1} = hint_bytes /\
    0 <= i{1} <= kvec /\
    i{1} = i{2} /\
    0 <= index{1} <= w_hint /\
    index{1} = hints_written{2} /\
    index{1} = count_nonzero_prefix (decoded_unflatten _hint) i{1} 0 /\
   y{1} = mkseq (fun (i0 : int) => signature{2}.[3248 + i0]) hint_bytes /\
    touch_hint _signature signature{2} /\
    condition1{2} = (i{2} < 6)
  ); last first.
 + auto => /> &1 &2 ???;do split;1..3,5..6:smt(size_mkseq).
    + by rewrite /count_nonzero_prefix /= !take0 big_nil /#. 
  wp. (* Inner while loop *)
  while (
       wpolykvec_urng (decoded_unflatten hint_0{2}) 2 /\
       count_nonzero_coeffs_kvec (decoded_unflatten _hint) <= w_hint /\
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
        y{1} = mkseq (fun (i0 : int) => signature{2}.[3248 + i0]) hint_bytes /\
        touch_hint _signature signature{2} /\
        condition2{2} = (j{2} < 256)
  ); last first.
  + auto => /> &1 &2 Hrng ?????????  c1 j2 s2 *; do split;1..3,7..:smt(size_put).
    + rewrite /count_nonzero_prefix ifT 1:/#.
      case (i{1} + 1 = kvec) => ?. 
      + rewrite ifF 1:/# /= (take_nth witness) /=;1:smt(KArray.size_to_list).
        by rewrite big_rcons ifT 1:/# (take_oversize j2) ?size_to_list /#.
      rewrite ifT 1:/# (take_nth witness);1:smt(KArray.size_to_list).
      by rewrite big_rcons ifT 1:/# /= take0 /= (take_oversize j2) ?size_to_list /#.
   + apply (eq_from_nth witness);1:smt(size_put size_mkseq).
     move => k; rewrite size_put size_mkseq /max ifT 1:/# /= => kb.
     by rewrite nth_put 1:/# /=; smt(nth_mkseq Array3309.get_setE).
   + by smt(Array3309.get_setE).

 seq 0 4 : (#pre /\
     to_uint hint_coefficient{2} = asint h{1}.[i{1}].[j{1}]).
 + auto => /> &2 Hrng ? Hh2 ?????????. 
   have  /= Hrngp := decoded_unflattenE i{2} j{2} hint_0{2} (fun (ii : W32.t) => 0 <= to_uint ii < 2) _ _ _ _;1..4:smt().
   have  /= Hh2p := decoded_unflattenP i{2} j{2} hint_0{2} _hint (fun (ii : W32.t) => incoeff (to_uint ii)) _ _ _ _;1..4: smt(). 
   rewrite /(`<<`) /= /decoded_unflatten initiE 1:/# /=.
   by rewrite get_of_list 1:/# /= nth_sub 1:/# /=; smt(incoeffK).

if.
 + auto => /> &2 Hrng ? Hh2 ?????????.
   have  /= Hrngp := decoded_unflattenE i{2} j{2} hint_0{2} (fun (ii : W32.t) => 0 <= to_uint ii < 2) _ _ _ _;1..4:smt().
   have  /= Hh2p := decoded_unflattenP i{2} j{2} hint_0{2} _hint (fun (ii : W32.t) => incoeff (to_uint ii)) _ _ _ _;1..4: smt(). 
   rewrite /(`<<`) /= /decoded_unflatten initiE 1:/# /=.

   rewrite initiE 1:/# /= nth_sub 1:/# /=.
   rewrite mulrC -Hh2p => H.
   by rewrite !to_uint_eq /=;smt( incoeffK).

 + auto => /> &1 &2 ????????????Hone; do split; 1..2,5..6,8:smt(Array3309.get_setE size_put). 
   + by smt(count_nonzero_prefix_one). 
   + move : Hone;rewrite /decoded_unflatten /count_nonzero_prefix ifT 1:/# ifT 1:/# /= (take_nth witness);1: by rewrite size_to_list /#.
     rewrite initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /= => -> /=.
     by rewrite -cats1 count_cat /= /#.
   + apply (eq_from_nth witness);1:smt(size_put size_mkseq).
     move => k; rewrite size_put size_mkseq /max ifT 1:/# /= => kb.
     by rewrite nth_put 1:/# /=; smt(nth_mkseq Array3309.get_setE).
+ auto => /> &1 &2 ????????????Hone; do split; 2..:smt().
   + move : Hone;rewrite /decoded_unflatten /count_nonzero_prefix ifT 1:/# ifT 1:/# /=  (take_nth witness);1: by rewrite size_to_list /#.
     rewrite initiE 1:/# /= get_of_list 1:/# nth_sub 1:/# /=.
     by rewrite -cats1 count_cat /= /#.
qed.


