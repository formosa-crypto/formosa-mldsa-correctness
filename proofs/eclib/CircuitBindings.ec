(* -------------------------------------------------------------------- *)
require import AllCore List Ring IntDiv BitEncoding.
require import StdRing StdOrder QFABV.

from Jasmin require import JWord.

import BS2Int.

require import JWordExtra.

(* -------------------------------------------------------------------- *)
op bool2bits (b : bool) : bool list = [b].
op bits2bool (b: bool list) : bool = List.nth false b 0.

op i2b (i : int) = (i %% 2 <> 0).
op b2si (b : bool) = 0.

bind bitstring bool2bits bits2bool b2i b2si i2b bool 1.

realize gt0_size    by done.
realize size_tolist by done.
realize tolistP     by done.
realize tosintP     by done.
realize oflistP     by smt(size_eq1).

realize ofintP.
proof.
move=> i @/bits2bool @/int2bs.
by rewrite (nth_mkseq false). 
qed.

realize touintP.
proof.
move=> b @/bool2bits.
by rewrite bs2int_cons bs2int_nil.
qed.
    
bind op bool (/\) "and".
realize bvandP by move=> * @/bool2bits /#.

bind op bool (\/) "or".
realize bvorP by move=> * @/bool2bits /#.

bind op bool Bool.(^^) "xor".
realize bvxorP by move=> * @/bool2bits /#.


(* -------------------------------------------------------------------- *)
theory BSW8.
  bind bitstring W8.w2bits W8.bits2w W8.to_uint W8.to_sint W8.of_int W8.t 8.

  realize gt0_size    by done.
  realize size_tolist by done.
  realize tolistP     by exact: W8.w2bitsK.
  realize oflistP     by exact: W8.bits2wK.
  realize touintP     by move=> @/W8.to_uint.

  realize tosintP.
  proof.
  have [# ??]: 2^7 = 128 /\ 2^8 = 256 by done.
  move=> w; apply/implyNb=> sz_ne1 /= @/msb.
  by rewrite -W8.get_bits2w 1:/# W8.w2bitsK -BWE8.msbE /#.
  qed.

  realize ofintP.
  proof. by move=> i @/of_int; rewrite int2bs_mod. qed.

  bind op [bool & W8.t] W8.init "init".
  realize size_1 by done.

  realize bvinitP.
  proof.
  move=> f; apply/(eq_from_nth false) => /=.
  - rewrite (size_flatten_ctt 1) ?size_mkseq //.
    by move=> bs /mkseqP[i] [_ ->].
  move=> i rgi; rewrite (BitChunking.nth_flatten false 1) /=.
  - by apply/List.allP=> bs /mkseqP[j] [_ ->].
  by rewrite nth_mkseq //= initiE.
  qed.

  bind op W8.t W8.( + ) "add".
  realize bvaddP by exact W8.to_uintD.

  bind op W8.t W8.( * ) "mul".
  realize bvmulP by exact W8.to_uintM. 

  bind op W8.t W8.andw "and".
  realize bvandP.
  proof.
  by move=> w1 w2; rewrite /w2bits zip_map /= zipss -!map_comp.
  qed.

  bind op W8.t W8.orw "or".
  realize bvorP.
  proof.
  by move=> w1 w2; rewrite /w2bits zip_map /= zipss -!map_comp.
  qed.

  bind op W8.t W8.(+^) "xor".
  realize bvxorP.
  proof.
  by move=> w1 w2; rewrite /w2bits zip_map /= zipss -!map_comp.
  qed.

  bind op [W8.t & W8.t] W8.(`>>`) "shrs".

  realize bvshrsP.
  proof.
  move=> w1 w2 @/(`>>`).
  by rewrite W8.to_uint_shr // #smt:(W8.to_uint_cmp).
  qed.

  op srl_8 (w1 w2 : W8.t) : W8.t = w1 `>>>` W8.to_uint w2.

  bind op [W8.t] srl_8 "shr".
  realize bvshrP.
  proof.
  move=> w1 w2 @/shr_8.
  by rewrite W8.to_uint_shr // #smt:(W8.to_uint_cmp).
  qed.

  op sll_8 (w1 w2 : W8.t) : W8.t = w1 `<<<` to_uint w2.

  bind op [W8.t] sll_8 "shl".
  realize bvshlP.
  move=> w1 w2 @/shl_8.
  by rewrite W8.to_uint_shl // #smt:(W8.to_uint_cmp).
  qed.
end BSW8.

(* -------------------------------------------------------------------- *)
abstract theory BSW.
  op size : int.

  clone import BitWordSH as W with op size <- size.
  clone import WE as WE with op size <- size, theory W <- W.

  op rol (w1 w2 : W.t) = w1 `|<<<|` to_uint w2.
  op ror (w1 w2 : W.t) = w1 `|>>>|` to_uint w2.

  op sar (w1 w2 : W.t) : W.t = w1 `|>>>` W.to_uint w2.
  op shr (w1 w2 : W.t) : W.t = w1  `>>>` W.to_uint w2.

  bind bitstring W.w2bits W.bits2w W.to_uint W.to_sint W.of_int W.t size.

  realize gt0_size    by done.
  realize size_tolist by done.
  realize tolistP     by exact: W.w2bitsK.
  realize oflistP     by exact: W.bits2wK.
  realize touintP     by move=> @/to_uint.

  realize tosintP.
  proof.
  have ? := gt0_size; move=> w; apply/implyNb=> sz_ne1 /=.
  by rewrite /msb -get_bits2w 1:/# w2bitsK -msbE /#.
  qed.

  realize ofintP.
  proof. by move=> i @/of_int; rewrite int2bs_mod. qed.

  bind op W.t W.( + ) "add".
  realize bvaddP by exact W.to_uintD.

  bind op W.t W.( * ) "mul".
  realize bvmulP by exact W.to_uintM. 

  bind op W.t W.andw "and".
  realize bvandP.
  proof.
  by move=> w1 w2; rewrite /w2bits zip_map /= zipss -!map_comp.
  qed.

  bind op W.t W.orw "or".
  realize bvorP.
  proof.
  by move=> w1 w2; rewrite /w2bits zip_map /= zipss -!map_comp.
  qed.

  bind op W.t W.(+^) "xor".
  realize bvxorP.
  proof.
  by move=> w1 w2; rewrite /w2bits zip_map /= zipss -!map_comp.
  qed.

  bind op [W.t] rol "rol".
  realize bvrolP.
  proof.
  by move=> w1 w2 i ?; rewrite !get_w2bits /rol initE ifT.
  qed.

  bind op [W.t] ror "ror".
  realize bvrorP.
  proof.
  by move=> w1 w2 i ?; rewrite !get_w2bits /ror initE ifT.
  qed.

  bind op [W.t] sar "ashr".
  realize bvashrP.
  proof. by move=> w1 w2; rewrite to_sint_sar // #smt:(to_uint_cmp). qed.

  bind op [W.t] shr "shr".
  realize bvshrP.
  proof. by move=> w1 w2; rewrite to_uint_shr // #smt:(to_uint_cmp). qed.

  bind op [W.t & W8.t] W.(`<<`) "shls".
  realize bvshlsP.
  proof. by move=> w1 w2; rewrite to_uint_shl // #smt:(W8.to_uint_cmp). qed.

  bind op [W.t & W8.t] W.(`>>`) "shrs".
  realize bvshrsP.
  proof. by move=> w1 w2; rewrite to_uint_shr // #smt:(W8.to_uint_cmp). qed.

  bind op [W.t & W8.t] W.(`|>>`) "ashrs".
  realize bvashrsP.
  proof. by move=> w1 w2; rewrite to_sint_sar // #smt:(W8.to_uint_cmp). qed.
end BSW.

(* -------------------------------------------------------------------- *)
clone BSW as BSW16 with
  op     size <- 16,
  theory W    <- W16  { rename "_XX" as "_16" },
  theory WE   <- WE16 { rename "_XX" as "_16" }.

(* -------------------------------------------------------------------- *)
clone BSW as BSW32 with
  op     size <- 32,
  theory W    <- W32  { rename "_XX" as "_32" },
  theory WE   <- WE32 { rename "_XX" as "_32" }.

(* -------------------------------------------------------------------- *)
clone BSW as BSW64 with
  op     size <- 64,
  theory W    <- W64  { rename "_XX" as "_64" },
  theory WE   <- WE64 { rename "_XX" as "_64" }.

(* -------------------------------------------------------------------- *)
clone BSW as BSW128 with
  op     size <- 128,
  theory W    <- W128  { rename "_XX" as "_128" },
  theory WE   <- WE128 { rename "_XX" as "_128" }.

(* -------------------------------------------------------------------- *)
clone BSW as BSW256 with
  op     size <- 256,
  theory W    <- W256  { rename "_XX" as "_256" },
  theory WE   <- WE256 { rename "_XX" as "_256" }.
