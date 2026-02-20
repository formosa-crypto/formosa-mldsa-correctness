(* ==================================================================== *)
require import AllCore List Ring IntDiv BitEncoding.
require import StdRing StdOrder QFABV.
require import ListExtra.

from Jasmin require import JWord JArray.

import BS2Int.

require import JWordExtra.

import BitChunking.

(* ==================================================================== *)
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

(* ==================================================================== *)
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

(* ==================================================================== *)
abstract theory BSW.
  op size : int.

  clone import BitWordSH as W with op size <- size.
  clone import WE as WE with op size <- size, theory W <- W.

  op rol (w1 w2 : W.t) = w1 `|<<<|` to_uint w2.
  op ror (w1 w2 : W.t) = w1 `|>>>|` to_uint w2.

  op sar (w1 w2 : W.t) : W.t = w1 `|>>>` W.to_uint w2.
  op shr (w1 w2 : W.t) : W.t = w1  `>>>` W.to_uint w2.
  op shl (w1 w2 : W.t) : W.t = w1  `<<<` W.to_uint w2.

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

  bind op W.t W.(\udiv) "udiv".
  realize bvudivP by exact WE.to_uintUD.

  bind op W.t W.(\umod) "urem".
  realize bvuremP by exact WE.to_uintUM.

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

  bind op W.t W.invw "not".
  realize bvnotP.
  proof.
  by move=> w; rewrite /invw /= eq_sym map_w2bits_w2bits.
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

  bind op [W.t] shl "shl".
  realize bvshlP.
  proof. by move=> w1 w2; rewrite to_uint_shl // #smt:(to_uint_cmp). qed.

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

  bind op [bool & W.t] W.(\ult) "ult".
  realize bvultP by smt().

  bind op [bool & W.t] W.(\ule) "ule".
  realize bvuleP by smt().

  bind op [bool & W.t] W.(\slt) "slt".
  realize bvsltP by smt().

  bind op [bool & W.t] W.(\sle) "sle".
  realize bvsleP by smt().

  (* FIXME: uniformize type parameter order for bindings *)
  (* FIXME: uniformize binding treatment of booleans     *)
  (* FIXME: here BSW.size is required to be >= 1         *)
  bind op [W.t & bool] W."_.[_]" "get".
  realize bvgetP   by done.
  realize eq1_size by done.
  realize le_size  by smt(gt0_size).

  bind op [bool & W.t] W.init "init".

  realize size_1 by done.

  realize bvinitP.
  proof.
  move=> f; rewrite init_bits2w bits2wK.
  - by rewrite size_map size_iota.
  - by rewrite flatten_mkseq_seq1.
  qed.
end BSW.

(* ==================================================================== *)
abstract theory BS_WB_WS.
  op sizeS : int.
  op sizeB : int.
  op r     : int.

  clone import BitWordSH as WS with
    op size <- sizeS.

  clone WE as WSE with
        op size <- sizeS,
    theory W    <- WS.

  clone import BitWordSH as WB with
    op size <- sizeB.

  clone WE as WBE with
        op size <- sizeB,
    theory W    <- WB.
  
  clone import W_WS with
        op sizeS <- sizeS, 
        op sizeB <- sizeB,
        op r     <- r,
    theory WS    <- WS,
    theory WB    <- WB.

  clone import BSW as BSWS with 
        op size <- sizeS,
    theory W    <- WS,
    theory WE   <- WSE.

  clone import BSW as BSWB with 
        op size <- sizeB,
    theory W    <- WB,
    theory WE   <- WBE.

  bind op [WB.t & WS.t] truncateu'S "truncate".

  realize le_size by smt(WS.gt0_size W_WS.gt0_r W_WS.sizeBrS).

  realize bvtruncateP.
  proof.
  move=> w @/truncateu'S @/w2bits; rewrite take_mkseq.
  - by rewrite ge0_size le_size.
  apply: eq_in_mkseq => i rgi /=; rewrite of_intwE rgi /=.
  rewrite get_to_uint /int_bit /= modz_pow2_div 1:/#.
  by rewrite modz_dvd -1:#smt:(le_size) (dvdz_exp2l _ 1) /#.
  qed.

  bind op [WS.t & WB.t] zeroextu'B "zextend".

  realize le_size by smt(WS.gt0_size W_WS.gt0_r W_WS.sizeBrS).

  realize bvzextendP.
  proof.
  have ? := WS.to_uint_cmp; move=> w @/zeroextu'B; rewrite of_uintK.
  rewrite pmod_small //; split=> [/#|_].
  apply: (IntOrder.ltr_le_trans WS.modulus) => [/#|].
  by apply: IntOrder.ler_weexpn2l => //; smt(WS.gt0_size le_size).
  qed.
end BS_WB_WS.

(* ==================================================================== *)
abstract theory BS_WB_WS_U.
  op sizeS : int.
  op sizeB : int.

  axiom le_size : sizeS <= sizeB.

  clone import BitWordSH as WS with
    op size <- sizeS.

  clone WE as WSE with
        op size <- sizeS,
    theory W    <- WS.

  clone import BitWordSH as WB with
    op size <- sizeB.

  clone WE as WBE with
        op size <- sizeB,
    theory W    <- WB.

  clone import BSW as BSWS with 
        op size <- sizeS,
    theory W    <- WS,
    theory WE   <- WSE.

  clone import BSW as BSWB with 
        op size <- sizeB,
    theory W    <- WB,
    theory WE   <- WBE.

  op truncateu'S (w : WB.t) : WS.t =
    WS.of_int (WB.to_uint w).

  op zeroextu'B (w : WS.t) : WB.t =
    WB.of_int (WS.to_uint w).

  bind op [WB.t & WS.t] truncateu'S "truncate".

  realize le_size by apply: le_size.

  realize bvtruncateP.
  proof.
  move=> w @/truncateu'S @/w2bits; rewrite take_mkseq.
  - by rewrite ge0_size le_size.
  apply: eq_in_mkseq => i rgi /=; rewrite of_intwE rgi /=.
  rewrite get_to_uint /int_bit /= modz_pow2_div 1:/#.
  by rewrite modz_dvd -1:#smt:(le_size) (dvdz_exp2l _ 1) /#.
  qed.

  bind op [WS.t & WB.t] zeroextu'B "zextend".

  realize le_size by apply: le_size.

  realize bvzextendP.
  proof.
  have ? := WS.to_uint_cmp; move=> w @/zeroextu'B; rewrite of_uintK.
  rewrite pmod_small //; split=> [/#|_].
  apply: (IntOrder.ltr_le_trans WS.modulus) => [/#|].
  by apply: IntOrder.ler_weexpn2l => //; smt(WS.gt0_size le_size).
  qed.
end BS_WB_WS_U.

(* ==================================================================== *)
abstract theory BSA.
  op size : int.

  axiom gt0_size : 0 < size.
 
  clone import PolyArray as A with
    op size <- size proof ge0_size by smt(gt0_size).

  bind array A."_.[_]" A."_.[_<-_]" A.to_list A.of_list A.t size.

  realize gt0_size by exact: gt0_size.
  realize tolistP  by done.
  realize get_setP by smt(A.get_setE).
  realize eqP      by smt(A.tP).
  realize get_out  by smt(A.get_out).
end BSA.

(* ==================================================================== *)
abstract theory BSWA.
  op asize : int.
  op bsize : int.

  clone import PolyArray as A with op size <- asize.
  clone import BitWordSH as W with op size <- bsize.

  clone WE with
        op size <- bsize,
    theory W    <- W.

  clone import BSW with 
        op size <- bsize,
    theory W    <- W,
    theory WE   <- WE.

  clone import BSA with
        op size <- asize,
    theory  A   <- A.

  op init (f: int -> W.t) : W.t A.t = A.init f.

  bind op [W.t & A.t] init "ainit".

  realize bvainitP.
  proof.
  move=> f @/init; rewrite BVA_Top_BSA_A_t.tolistP.
  by apply: eq_in_mkseq => i ? /=; rewrite initE ifT.
  qed.
end BSWA.

(* ==================================================================== *)
abstract theory BSWAS.
  op asize : int.
  op bsize : int.
  op ssize : int.

  axiom le_size : ssize <= bsize * asize.

  clone import PolyArray as A  with op size <- asize.
  clone import BitWordSH as WB with op size <- bsize.
  clone import BitWordSH as WS with op size <- ssize.

  clone WE as WEB with
        op size <- bsize,
    theory W    <- WB.

  clone import BSW as BSWB with 
        op size <- bsize,
    theory W    <- WB,
    theory WE   <- WEB.

  clone WE as WES with
        op size <- ssize,
    theory W    <- WS.

  clone import BSW as BSWS with 
        op size <- ssize,
    theory W    <- WS,
    theory WE   <- WES.

  clone BSA with
        op size <- asize,
    theory A    <- A.

  clone BSWA with
        op asize <- asize,
        op bsize <- bsize,
    theory W     <- WB,
    theory WE    <- WEB,
    theory BSW   <- BSWB,
    theory A     <- A,
    theory BSA   <- BSA.

  op tobits (a : WB.t A.t) : bool list =
    flatten (List.map WB.w2bits (A.to_list a)).

  op ofbits (a : bool list) : WB.t A.t =
    A.of_list witness (List.map WB.bits2w (chunk bsize a)).

  lemma size_tobits a : size (tobits a) = bsize * asize.
  proof.
  rewrite /tobits (size_flatten_ctt bsize).
  - by move=> bs /mapP[w] [_ ->].
  - by rewrite size_map size_to_list.
  qed.

  hint simplify size_tobits.

  lemma ofbitsK (bs : bool list) :
    size bs = bsize * asize => tobits (ofbits bs) = bs.
  proof.
  move=> eq @/tobits @/ofbits; rewrite of_listK.
  - by rewrite size_map size_chunk // eq; smt(WB.gt0_size).
  rewrite -map_comp -(iffLR _ _ (eq_in_map idfun _ _)).
  - move=> w /(in_chunk_size bsize _ _ WB.gt0_size) ?.
    by rewrite /idfun /(\o) WB.bits2wK.
  by rewrite map_id chunkK // eq dvdz_mulr dvdzz.
  qed.

  op sliceget (a : WB.t A.t) (offset : int) : WS.t =
    WS.bits2w (take ssize (drop offset (tobits a))).

  op sliceset (a : WB.t A.t) (offset : int) (w : WS.t) : WB.t A.t =
    let pr = take offset (tobits a) in
    let po = drop (offset + ssize) (tobits a) in
    ofbits (pr ++ WS.w2bits w ++ po).

  bind op [WB.t & WS.t & A.t] sliceget "asliceget".

  realize le_size by exact: le_size.

  realize bvaslicegetP.
  proof. by move=> /= a off ? i ? @/sliceget; rewrite get_bits2w. qed.

  bind op [WB.t & WS.t & A.t] sliceset "asliceset".

  realize le_size by exact: le_size.

  realize bvaslicesetP.
  proof.
  have ? := WS.ge0_size; have ? := WB.ge0_size.
  move=> /= a off w ? i ?; rewrite -!/(tobits _) /sliceset /= ofbitsK.
  - by rewrite !size_cat /= size_take_condle 1:/# /= ifT 1:/# size_drop /#.
  case: (i < off) => ?.
  - rewrite ifF 1:/# -catA nth_cat ifT.
    - by rewrite size_take_condle /#.
    - by rewrite nth_take ~-1:/#.
  rewrite -catA nth_cat ifF 1:size_take_condle ~-1:/#.
  rewrite size_take_condle 1:/# /= ifT 1:/# /=.
  case: (off + ssize <= i) => ?.
  - by rewrite ifF 1:/# nth_cat /= ifF 1:/# nth_drop /#.
  by rewrite ifT 1:/# nth_cat ifT 1:/# get_w2bits.
  qed.
end BSWAS.

(* ==================================================================== *)
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

(* ==================================================================== *)
clone BS_WB_WS as BS_W2u16 with
      op sizeS <-  16,
      op sizeB <-  32,
      op r     <-   2,
  theory WS    <- W16   { rename "_XX" as "_16" },
  theory WSE   <- WE16  { rename "_XX" as "_16" },
  theory WB    <- W32   { rename "_XX" as "_32" },
  theory WBE   <- WE32  { rename "_XX" as "_32" },
  theory BSWS  <- BSW16,
  theory BSWB  <- BSW32,
  theory W_WS  <- W2u16
                    { rename "'Ru'S" as "2u16"
                             "'R"    as "2"
                             "'S"    as "16"
                             "'B"    as "32" }.

(* -------------------------------------------------------------------- *)
clone BS_WB_WS as BS_W2u32 with
      op sizeS <-  32,
      op sizeB <-  64,
      op r     <-   2,
  theory WS    <- W32   { rename "_XX" as "_32" },
  theory WSE   <- WE32  { rename "_XX" as "_32" },
  theory WB    <- W64   { rename "_XX" as "_64" },
  theory WBE   <- WE64  { rename "_XX" as "_64" },
  theory BSWS  <- BSW32,
  theory BSWB  <- BSW64,
  theory W_WS  <- W2u32
                    { rename "'Ru'S" as "2u32"
                             "'R"    as "2"
                             "'S"    as "32"
                             "'B"    as "64" }.

(* -------------------------------------------------------------------- *)
clone BS_WB_WS as BS_W2u64 with
      op sizeS <-  64,
      op sizeB <- 128,
      op r     <-   2,
  theory WS    <- W64   { rename "_XX" as "_64" },
  theory WSE   <- WE64  { rename "_XX" as "_64" },
  theory WB    <- W128  { rename "_XX" as "_128" },
  theory WBE   <- WE128 { rename "_XX" as "_128" },
  theory BSWS  <- BSW64,
  theory BSWB  <- BSW128,
  theory W_WS  <- W2u64
                    { rename "'Ru'S" as "2u64"
                             "'R"    as "2"
                             "'S"    as "64"
                             "'B"    as "128" }.

(* -------------------------------------------------------------------- *)
clone BS_WB_WS as BS_W2u128 with
      op sizeS <- 128,
      op sizeB <- 256,
      op r     <-   2,
  theory WS    <- W128  { rename "_XX" as "_128" },
  theory WSE   <- WE128 { rename "_XX" as "_128" },
  theory WB    <- W256  { rename "_XX" as "_256" },
  theory WBE   <- WE256 { rename "_XX" as "_256" },
  theory BSWS  <- BSW128,
  theory BSWB  <- BSW256,
  theory W_WS  <- W2u128
                    { rename "'Ru'S" as "2u128"
                             "'R"    as "2"
                             "'S"    as "128"
                             "'B"    as "256" }.

(* -------------------------------------------------------------------- *)
clone BS_WB_WS as BS_W4u16 with
      op sizeS <-  16,
      op sizeB <-  64,
      op r     <-   4,
  theory WS    <- W16   { rename "_XX" as "_16" },
  theory WSE   <- WE16  { rename "_XX" as "_16" },
  theory WB    <- W64   { rename "_XX" as "_64" },
  theory WBE   <- WE64  { rename "_XX" as "_64" },
  theory BSWS  <- BSW16,
  theory BSWB  <- BSW64,
  theory W_WS  <- W4u16
                    { rename "'Ru'S" as "4u16"
                             "'R"    as "4"
                             "'S"    as "16"
                             "'B"    as "64" }.

(* -------------------------------------------------------------------- *)
clone BS_WB_WS as BS_W4u32 with
      op sizeS <-  32,
      op sizeB <- 128,
      op r     <-   4,
  theory WS    <- W32   { rename "_XX" as "_32" },
  theory WSE   <- WE32  { rename "_XX" as "_32" },
  theory WB    <- W128  { rename "_XX" as "_128" },
  theory WBE   <- WE128 { rename "_XX" as "_128" },
  theory BSWS  <- BSW32,
  theory BSWB  <- BSW128,
  theory W_WS  <- W4u32
                    { rename "'Ru'S" as "4u32"
                             "'R"    as "4"
                             "'S"    as "32"
                             "'B"    as "128" }.

(* -------------------------------------------------------------------- *)
clone BS_WB_WS as BS_W4u64 with
      op sizeS <-  64,
      op sizeB <- 256,
      op r     <-   4,
  theory WS    <- W64   { rename "_XX" as "_64" },
  theory WSE   <- WE64  { rename "_XX" as "_64" },
  theory WB    <- W256  { rename "_XX" as "_256" },
  theory WBE   <- WE256 { rename "_XX" as "_256" },
  theory BSWS  <- BSW64,
  theory BSWB  <- BSW256,
  theory W_WS  <- W4u64
                    { rename "'Ru'S" as "4u64"
                             "'R"    as "4"
                             "'S"    as "64"
                             "'B"    as "256" }.

(* -------------------------------------------------------------------- *)
clone BS_WB_WS as BS_W8u16 with
      op sizeS <-  16,
      op sizeB <- 128,
      op r     <-   8,
  theory WS    <- W16   { rename "_XX" as "_16" },
  theory WSE   <- WE16  { rename "_XX" as "_16" },
  theory WB    <- W128  { rename "_XX" as "_128" },
  theory WBE   <- WE128 { rename "_XX" as "_128" },
  theory BSWS  <- BSW16,
  theory BSWB  <- BSW128,
  theory W_WS  <- W8u16
                    { rename "'Ru'S" as "8u16"
                             "'R"    as "8"
                             "'S"    as "16"
                             "'B"    as "128" }.

(* -------------------------------------------------------------------- *)
clone BS_WB_WS as BS_W8u32 with
      op sizeS <-  32,
      op sizeB <- 256,
      op r     <-   8,
  theory WS    <- W32   { rename "_XX" as "_32" },
  theory WSE   <- WE32  { rename "_XX" as "_32" },
  theory WB    <- W256  { rename "_XX" as "_256" },
  theory WBE   <- WE256 { rename "_XX" as "_256" },
  theory BSWS  <- BSW32,
  theory BSWB  <- BSW256,
  theory W_WS  <- W8u32
                    { rename "'Ru'S" as "8u32"
                             "'R"    as "8"
                             "'S"    as "32"
                             "'B"    as "256" }.

(* -------------------------------------------------------------------- *)
clone BS_WB_WS as BS_W16u16 with
      op sizeS <-  16,
      op sizeB <- 256,
      op r     <-  16,
  theory WS    <- W16   { rename "_XX" as "_16" },
  theory WSE   <- WE16  { rename "_XX" as "_16" },
  theory WB    <- W256  { rename "_XX" as "_256" },
  theory WBE   <- WE256 { rename "_XX" as "_256" },
  theory BSWS  <- BSW16,
  theory BSWB  <- BSW256,
  theory W_WS  <- W16u16
                    { rename "'Ru'S" as "16u16"
                             "'R"    as "16"
                             "'S"    as "16"
                             "'B"    as "256" }.
