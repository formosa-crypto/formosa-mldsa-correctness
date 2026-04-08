require import AllCore List IntDiv RealExp StdBigop.

from Spec require import GFq Rq Serialization Conversion Parameters VecMat MLDSA_W32_Rep.

from JazzEC require import Array320 Array416 Array1280 Array640 Array1536 Array768 Array256 Array128 Array1920 Array3200 Array7680 Array2496.

import LArray KArray.

axiom mldsa65_lvec: lvec = 5.
axiom mldsa65_kvec: kvec = 6.
axiom mldsa65_w_hint : w_hint = 55.
axiom mldsa65_lambda : lambda = 192.
axiom mldsa65_gamma1 : gamma1 = 524288. (* 2**19 *)
axiom mldsa65_gamma2 : gamma2 = 261888. (* (q-1)/32 *)
axiom mldsa65_Eta : Eta = 4.
axiom mldsa65_tau : tau = 49.

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

op  kvec_unflatten320(a : 'a Array1920.t) =
     KArray.init (fun i => Array320.of_list witness (sub a (320*i) 320)).

op  kvec_unflatten416(a : 'a Array2496.t) =
     KArray.init (fun i => Array416.of_list witness (sub a (416*i) 416)).

lemma lvec_unflatten640iE (v : 'a Array3200.t) i :
   0 <= i < 3200 => v.[i] = (lvec_unflatten640 v).[i %/ 640].[i %% 640].
move => Hi; rewrite initiE /=; 1: smt(mldsa65_lvec).
rewrite get_of_list 1:/# /= nth_sub /#.
qed.

lemma lvec_unflatten256iE (v : 'a Array1280.t) i :
   0 <= i < 1280 => v.[i] = (lvec_unflatten256 v).[i %/ 256].[i %% 256].
move => Hi; rewrite initiE /=; 1: smt(mldsa65_lvec).
rewrite get_of_list 1:/# /= nth_sub /#.
qed.

lemma lvec_unflatten128iE (v : 'a Array640.t) i :
   0 <= i < 640 => v.[i] = (lvec_unflatten128 v).[i %/ 128].[i %% 128].
move => Hi; rewrite initiE /=; 1: smt(mldsa65_lvec).
rewrite get_of_list 1:/# /= nth_sub /#.
qed.

lemma kvec_unflatten256iE (v : 'a Array1536.t) i :
   0 <= i < 1536 => v.[i] = (kvec_unflatten256 v).[i %/ 256].[i %% 256].
move => Hi; rewrite initiE /=; 1: smt(mldsa65_kvec).
rewrite get_of_list 1:/# /= nth_sub /#.
qed.

lemma kvec_unflatten128iE (v : 'a Array768.t) i :
   0 <= i < 768 => v.[i] = (kvec_unflatten128 v).[i %/ 128].[i %% 128].
move => Hi; rewrite initiE /=; 1: smt(mldsa65_kvec).
rewrite get_of_list 1:/# /= nth_sub /#.
qed.

lemma kvec_unflatten320iE (v : 'a Array1920.t) i :
   0 <= i < 1920 => v.[i] = (kvec_unflatten320 v).[i %/ 320].[i %% 320].
move => Hi; rewrite initiE /=; 1: smt(mldsa65_kvec).
rewrite get_of_list 1:/# /= nth_sub /#.
qed.

lemma kvec_unflatten416iE (v : 'a Array2496.t) i :
   0 <= i < 2496 => v.[i] = (kvec_unflatten416 v).[i %/ 416].[i %% 416].
move => Hi; rewrite initiE /=; 1: smt(mldsa65_kvec).
rewrite get_of_list 1:/# /= nth_sub /#.
qed.



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

op mat_unflatten256(a : 'a Array7680.t) =
     KLMatrix.init (fun i => Array256.of_list witness (sub a (256*i) 256)).
     
