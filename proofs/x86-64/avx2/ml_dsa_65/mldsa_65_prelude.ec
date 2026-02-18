require import AllCore List IntDiv RealExp StdBigop.

from Spec require import GFq Rq Serialization Conversion Parameters VecMat MLDSA_W32_Rep.

from JazzEC require import Array1280 Array640 Array1536 Array768 Array256 Array128 Array3200.

import LArray KArray.

axiom mldsa65_lvec: lvec = 5.
axiom mldsa65_kvec: kvec = 6.
axiom mldsa65_w_hint : w_hint = 55.
axiom mldsa65_lambda : lambda = 192.
axiom mldsa65_gamma1 : gamma1 = 524288. (* 2**19 *) 



op  lvec_unflatten640(a : 'a Array3200.t) =
     LArray.init (fun i => Array640.of_list witness (sub a (640*i) 640)).
op  lvec_unflatten256(a : 'a Array1280.t) =
     LArray.init (fun i => Array256.of_list witness (sub a (256*i) 256)).
op  lvec_unflatten128(a : 'a Array640.t) =
     LArray.init (fun i => Array128.of_list witness (sub a (128*i) 128)).

op  kvec_unflatten256(a : 'a Array1536.t) =
     KArray.init (fun i => Array256.of_list witness (sub a (256*i) 256)).
op  kvec_unflatten128(a : 'a Array768.t) =
     KArray.init (fun i => Array128.of_list witness (sub a (128*i) 128)).

lemma kvec_unflatten256E i j (h : 'a Array1536.t) (P : 'a -> bool) :
   0 <= i < kvec =>
   0 <= j < 256 =>
        all (all P) (kvec_unflatten256 h) =>
        P h.[i*256+j].
have eq_kvec := mldsa65_kvec.
move => ??;rewrite allP => Hii. 
have := Hii i _;1:smt().
rewrite allP => Hjj. 
have := Hjj j _;1:smt().
by rewrite initiE 1:/# /= get_of_list 1:/# /= nth_sub /#. 
qed.

lemma kvec_unflatten256P i j (h1 : 'a Array1536.t) (h2 : ('b Array256.t) KArray.t) (F : 'a -> 'b) :
   0 <= i < kvec =>
   0 <= j < 256 =>
        map (map F) (kvec_unflatten256 h1) = h2 =>
        F h1.[i*256+j] = h2.[i].[j].
have eq_kvec := mldsa65_kvec.
move => ??; rewrite tP => Hii.
have := Hii i _; 1:smt().
rewrite tP => Hjj.
have := Hjj j _; 1:smt().
rewrite mapiE 1:/# /= mapiE 1:/# /= initiE 1:/# initiE 1:/# /=.
by rewrite  /= !nth_sub /#. 
qed.
