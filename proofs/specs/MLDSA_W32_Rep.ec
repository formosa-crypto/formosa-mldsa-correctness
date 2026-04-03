require import AllCore IntDiv List.

from Jasmin require import JWord.

require import GFq Rq VecMat.
require import Array256.

import Parameters CDR Round Zq PolyLVec PolyKVec PolyMat.

(******************************************************)
(* Representations of polys as 32-bit word arrays     *)
(******************************************************)

type wpoly = W32.t Array256.t.

op liftu_wpoly (pw : wpoly) : poly =
  map (fun w => incoeff (W32.to_uint w)) pw.

op lifts_wpoly (pw : wpoly) : poly =
  map (fun w => incoeff (W32.to_sint w)) pw.

op unlift_poly (p : poly) : wpoly = map (fun c => W32.of_int (asint c)) p.

op poly_urng(b : int, p : poly) = all (fun i => 0 <= asint i < b) p.
op poly_srng(bl bh : int, p : poly) = all (fun i => -bl <= crepr i <= bh) p.

op wpoly_urng(b : int, pw : wpoly) = all (fun i => 0 <= W32.to_uint i < b) pw.
op wpoly_srng(bl bh : int, pw : wpoly) = all (fun i => -bl <= W32.to_sint i <= bh) pw.
op wpoly_infnorm_lt(b : int, pw : wpoly) = wpoly_srng (b-1) (b-1) pw.

(* Abstract predicate: coefficients are in NTT-domain normal form.
   To be instantiated once the NTT bridge lemmas are available. *)
op wpoly_ntt_rng : wpoly -> bool.

lemma wpoly_infnorm_liftE (b : int) (pw : wpoly) :
    0 < b <= q %/ 2 =>
    wpoly_infnorm_lt b pw => infnorm_lt (lifts_wpoly pw) b.
move => Hb.
rewrite /wpoly_infnorm_lt /infnorm_lt /wpoly_srng /lifts_wpoly !allP /=.
move => H j; rewrite mem_iota /= => Hj; have := H j _; 1: smt().
rewrite mapiE 1:/# /=.
move => [Hl Hr]; have /# := incoeffK_centered (to_sint pw.[j]) _; 1: smt().
qed.

 
type wpolylvec = wpoly LArray.t. 

op liftu_wpolylvec(wv : wpolylvec) : polylvec =
  map liftu_wpoly wv.

op lifts_wpolylvec (wv : wpolylvec) : polylvec =
  map lifts_wpoly wv.

op unlift_polylvec (v : polylvec) : wpolylvec = map unlift_poly v.

op polylvec_urng(p : polylvec, b : int) = all (poly_urng b) p.
op polylvec_srng(p : polylvec, bl bh : int) = all (poly_srng bl bh) p.

op wpolylvec_urng(pw : wpolylvec, b : int) = all (wpoly_urng b) pw.
op wpolylvec_srng(pw : wpolylvec, bl bh : int) = all (wpoly_srng bl bh) pw.
op wpolylvec_infnorm_lt(b : int, pw : wpolylvec) = wpolylvec_srng pw (b-1) (b-1).
op wpolylvec_ntt_rng(pw : wpolylvec) = all wpoly_ntt_rng pw.

lemma wpolylvec_infnorm_liftE (b : int) (pw : wpolylvec) :
    0 < b <= q %/ 2 =>
    wpolylvec_infnorm_lt b pw => PolyLVec.infnorm_lt (lifts_wpolylvec pw) b.
proof.
move => Hb.
rewrite /wpolylvec_infnorm_lt /wpolylvec_srng /polylvec_infnorm_lt /lifts_wpolylvec allP /= => H.
rewrite /infnorm_lt allP => i; rewrite mem_iota /= => Hi.
rewrite allP => k; rewrite mem_iota /= => Hk.
rewrite mapiE 1:/# /= mapiE 1:/# /=.
have := H i _; 1: smt().
rewrite /wpoly_srng allP => Hi'.
have /= := Hi' k _; 1: smt().
by  have /# := incoeffK_centered (to_sint pw.[i].[k]) _; 1: smt().
qed.

(* Reverse direction: spec infnorm implies word infnorm, given range ensuring incoeffK_centered applies *)
lemma wpolylvec_infnorm_unliftE (b bl bh : int) (pw : wpolylvec) :
    0 < b <= q %/ 2 =>
    bl + 1 <= q %/ 2 => bh <= q %/ 2 =>
    wpolylvec_srng pw bl bh =>
    PolyLVec.infnorm_lt (lifts_wpolylvec pw) b => wpolylvec_infnorm_lt b pw.
proof.
move => Hb Hbl Hbh Hrng Hinf.
rewrite /wpolylvec_infnorm_lt /wpolylvec_srng allP => i  Hi.
rewrite /wpoly_srng allP => k /= Hk.
move: Hinf; rewrite /PolyLVec.infnorm_lt /lifts_wpolylvec allP /= => Hinf.
have /= Hi' := Hinf i _; 1: smt(mem_iota).
move: Hi'; rewrite allP /= => Hi'.
have /= Hk' := Hi' k _; 1: smt(mem_iota).
rewrite mapiE 1:/# /= in Hk'.
move: Hrng; rewrite /wpolylvec_srng allP => Hrng.
have /= Hrng_i := Hrng i _; 1: smt().
move: Hrng_i; rewrite /wpoly_srng allP => /= Hrng_i.
have /= Hrng_k := Hrng_i k _; 1: smt().
have := Hk'; rewrite /lifts_wpoly mapiE 1:/# /=.
by  have/#  := incoeffK_centered (to_sint pw.[i].[k]) _; 1: smt().
qed.


type wpolykvec = wpoly KArray.t. 

op liftu_wpolykvec(wv : wpolykvec) : polykvec =
  map liftu_wpoly wv.

op lifts_wpolykvec (wv : wpolykvec) : polykvec =
  map lifts_wpoly wv.

op unlift_polykvec (v : polykvec) : wpolykvec = map unlift_poly v.

op polykvec_urng(p : polykvec, b : int) = all (poly_urng b) p.
op polykvec_srng(p : polykvec, bl bh : int) = all (poly_srng bl bh) p.

op wpolykvec_urng(pw : wpolykvec, b : int) = all (wpoly_urng b) pw.
op wpolykvec_srng(pw : wpolykvec, bl bh : int) = all (wpoly_srng bl bh) pw.
op wpolykvec_infnorm(b : int, pw : wpolykvec) = wpolykvec_srng pw (b-1) (b-1).
op wpolykvec_ntt_rng(pw : wpolykvec) = all wpoly_ntt_rng pw.

lemma wpolykvec_infnorm_liftE (b : int) (pw : wpolykvec) :
    0 < b <= q %/ 2 =>
    wpolykvec_infnorm b pw => PolyKVec.infnorm (lifts_wpolykvec pw) b.
proof.
move => Hb.
rewrite /wpolykvec_infnorm /wpolykvec_srng /polykvec_infnorm /lifts_wpolykvec allP /= => H.
rewrite /infnorm allP => i; rewrite mem_iota /= => Hi.
rewrite allP => k; rewrite mem_iota /= => Hk.
rewrite mapiE 1:/# /= mapiE 1:/# /=.
have := H i _; 1: smt().
rewrite /wpoly_srng allP => Hi'.
have /= := Hi' k _; 1: smt().
by  have /# := incoeffK_centered (to_sint pw.[i].[k]) _; 1: smt().
qed.

type wpolymat = wpoly KLMatrix.t.

op liftu_wpolymat(wv : wpolymat) : polymat =
  map liftu_wpoly wv.

op lifts_wpolymat (wv : wpolymat) : polymat =
  map lifts_wpoly wv.

op unlift_polymat (v : polymat) : wpolymat = map unlift_poly v.

op polymat_urng(p : polymat, b : int) = all (poly_urng b) p.
op polymat_srng(p : polymat, bl bh : int) = all (poly_srng bl bh) p.

op wpolymat_urng(pw : wpolymat, b : int) = all (wpoly_urng b) pw.
op wpolymat_srng(pw : wpolymat, bl bh : int) = all (wpoly_srng bl bh) pw.
