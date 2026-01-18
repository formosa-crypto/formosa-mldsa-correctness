require import AllCore.

from Jasmin require import JWord.

require import GFq Rq VecMat.
require import Array256.

import CDR Round Zq PolyLVec PolyKVec.

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
op poly_srng(bl bh : int, p : poly) = all (fun i => -bl <= as_sint i <= bh) p.

op wpoly_urng(b : int, pw : wpoly) = all (fun i => 0 <= W32.to_uint i < b) pw.
op wpoly_srng(bl bh : int, pw : wpoly) = all (fun i => -bl <= W32.to_sint i <= bh) pw.

 
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

