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

(* ------------------------------------------------------------------ *)
(* Abstract range predicates for the three word-level polynomial ops.  *)
(*                                                                      *)
(* Each operation has an input range and an output range that may      *)
(* differ from each other and from the other operations' ranges.       *)
(* All six are left abstract here and will be made concrete once the   *)
(* NTT bridge lemmas are fully worked out.                             *)
(*                                                                      *)
(* Expected instantiation path:                                        *)
(*   ntt_orng  => bmul_irng   (NTT output is valid basemul input)      *)
(*   bmul_orng => intt_irng   (basemul output is valid INTT input)     *)
(*   intt_orng => wpoly_srng B_lo B_hi  (INTT output has concrete rng) *)
(* ------------------------------------------------------------------ *)
op wpoly_ntt_irng  : wpoly -> bool.  (* valid input  to   NTT   *)
op wpoly_ntt_orng  : wpoly -> bool.  (* valid output from NTT   *)
op wpoly_intt_irng : wpoly -> bool.  (* valid input  to   INTT  *)
op wpoly_bmul_irng : wpoly -> bool.  (* valid input  to   basemul *)

(* ------------------------------------------------------------------ *)
(* Bridge lemmas: relations between abstract range predicates.         *)
(* Admitted pending concrete instantiation of the abstract ops.        *)
(* ------------------------------------------------------------------ *)
lemma wpoly_ntt_orng_bmul_irng (p : wpoly) : wpoly_ntt_orng p => wpoly_bmul_irng p.
admitted.
(* basemul outputs satisfy |to_sint coeff| < q (Barrett/Montgomery final step),
   which is sufficient input range for invNTT *)
lemma wpoly_bmul_orng_intt_irng (p : wpoly) : wpoly_srng (q-1) (q-1) p => wpoly_intt_irng p.
admitted.

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
op wpolylvec_ntt_irng (pw : wpolylvec) = all wpoly_ntt_irng  pw.
op wpolylvec_ntt_orng (pw : wpolylvec) = all wpoly_ntt_orng  pw.
op wpolylvec_intt_irng(pw : wpolylvec) = all wpoly_intt_irng pw.
op wpolylvec_bmul_irng(pw : wpolylvec) = all wpoly_bmul_irng pw.

lemma wpolylvec_ntt_orng_bmul_irng (pv : wpolylvec) :
  wpolylvec_ntt_orng pv => wpolylvec_bmul_irng pv.
proof.
rewrite /wpolylvec_ntt_orng /wpolylvec_bmul_irng !allP.
by move => H p Hp; exact (wpoly_ntt_orng_bmul_irng pv.[p] (H p Hp)).
qed.

lemma wpolylvec_bmul_orng_intt_irng (pv : wpolylvec) :
  wpolylvec_srng pv (q-1) (q-1) => wpolylvec_intt_irng pv.
proof.
rewrite /wpolylvec_srng /wpolylvec_intt_irng !allP.
by move => H p Hp; exact (wpoly_bmul_orng_intt_irng pv.[p] (H p Hp)).
qed.

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
op wpolykvec_infnorm_lt(b : int, pw : wpolykvec) = wpolykvec_srng pw (b-1) (b-1).
op wpolykvec_ntt_irng (pw : wpolykvec) = all wpoly_ntt_irng  pw.
op wpolykvec_ntt_orng (pw : wpolykvec) = all wpoly_ntt_orng  pw.
op wpolykvec_intt_irng(pw : wpolykvec) = all wpoly_intt_irng pw.
op wpolykvec_bmul_irng(pw : wpolykvec) = all wpoly_bmul_irng pw.

lemma wpolykvec_ntt_orng_bmul_irng (pv : wpolykvec) :
  wpolykvec_ntt_orng pv => wpolykvec_bmul_irng pv.
proof.
rewrite /wpolykvec_ntt_orng /wpolykvec_bmul_irng !allP.
by move => H p Hp; exact (wpoly_ntt_orng_bmul_irng pv.[p] (H p Hp)).
qed.

lemma wpolykvec_bmul_orng_intt_irng (pv : wpolykvec) :
  wpolykvec_srng pv (q-1) (q-1) => wpolykvec_intt_irng pv.
proof.
rewrite /wpolykvec_srng /wpolykvec_intt_irng !allP.
by move => H p Hp; exact (wpoly_bmul_orng_intt_irng pv.[p] (H p Hp)).
qed.

lemma wpolykvec_infnorm_liftE (b : int) (pw : wpolykvec) :
    0 < b <= q %/ 2 =>
    wpolykvec_infnorm_lt b pw => PolyKVec.infnorm_lt (lifts_wpolykvec pw) b.
proof.
move => Hb.
rewrite /wpolykvec_infnorm_lt /wpolykvec_srng /polykvec_infnorm_lt /lifts_wpolykvec allP /= => H.
rewrite /infnorm_lt allP => i; rewrite mem_iota /= => Hi.
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
