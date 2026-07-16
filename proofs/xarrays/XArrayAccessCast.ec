(* -------------------------------------------------------------------- *)
(* Generic bridge between the (warray-model) extraction cast operators    *)
(* ArrayAccessCast.{get,set}_cast_direct and the circuit-binding slice     *)
(* operators BSWAS.{sliceget,sliceset}.  Proven once here over a shared     *)
(* word/array; cloned per (element-word, slice-word, length) combo in the   *)
(* XArray* files to obtain the element lemmas with no per-width proof.       *)
(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv BitEncoding JWordExtra JArrayExtra CircuitBindings.
from Jasmin require import JWord JArray JWord_array.
import BitChunking.

abstract theory XArrayAccessCast.
  op sizeWB : int.   (* bytes per array element word *)
  op sizeWS : int.   (* bytes per slice word        *)
  op sizeB  : int.   (* array length (in elements)  *)

  axiom rg_sizeWB : 1 <= sizeWB <= 32.
  axiom rg_sizeWS : 1 <= sizeWS <= 32.
  axiom gt0_sizeB : 0 < sizeB.
  axiom le_slice  : sizeWS <= sizeWB * sizeB.

  (* the shared word / array: a single BitWordSH-based word serves as both  *)
  (* the circuit-side BitWord and the extraction-side WT interface.         *)
  clone import BitWordSH as WB with op size <- 8 * sizeWB
    proof gt0_size by smt(rg_sizeWB), size_le_256 by smt(rg_sizeWB).
  clone import BitWordSH as WS with op size <- 8 * sizeWS
    proof gt0_size by smt(rg_sizeWS), size_le_256 by smt(rg_sizeWS).
  clone import PolyArray as A with op size <- sizeB
    proof ge0_size by smt(gt0_sizeB).

  (* extraction side (AW builds its own byte-array WArrayN internally) *)
  clone import ArrayWords as AW with
        op sizeW <- sizeWB,
        op sizeA <- sizeB,
    theory Word    <= WB,
    theory ArrayN  <= A
    proof gt0_sizeW by smt(rg_sizeWB), gt0_sizeA by smt(gt0_sizeB).

  clone import ArrayAccessCast as AC with
        op sizeWS      <- sizeWS,
        op sizeWB      <- sizeWB,
        op sizeB       <- sizeB,
    theory WordS       <- WS,
    theory WordB       <- WB,
    theory ArrayWordsB <= AW
    proof gt0_sizeWS by smt(rg_sizeWS), gt0_sizeWB by smt(rg_sizeWB), gt0_sizeB by smt(gt0_sizeB).

  (* circuit side, over the SAME word/array *)
  clone import BSWAS as BS with
        op asize <- sizeB,
        op bsize <- 8 * sizeWB,
        op ssize <- 8 * sizeWS,
    theory A     <- A,
    theory WB    <- WB,
    theory WS    <- WS
    proof le_size by smt(le_slice rg_sizeWB rg_sizeWS gt0_sizeB).

  (* bit b of word w of the array = flat bit w*(8*sizeWB)+b of its
     w2bits-flattened byte-list image *)
  lemma flat_bitE (a : WB.t A.t) (w b : int) :
    0 <= w < sizeB => 0 <= b < 8 * sizeWB =>
    a.[w].[b] = nth false (flatten (map WB.w2bits (A.to_list a))) (w * (8 * sizeWB) + b).
  proof.
  move => hw hb.
  rewrite (nth_flatten false (8 * sizeWB)).
  + rewrite allP /= => x; rewrite mapP => He; elim He; smt(WB.size_w2bits).
  have -> : (w*(8*sizeWB)+b) %/ (8*sizeWB) = w by smt(divzMDl divz_small rg_sizeWB).
  have -> : (w*(8*sizeWB)+b) %% (8*sizeWB) = b by smt(modzMDl modz_small rg_sizeWB).
  by rewrite (nth_map witness) 1:size_to_list 1:/# get_w2bits get_to_list.
  qed.

  lemma get_castE (p : WB.t A.t) o :
    0 <= o*8 <= 8*sizeWB*sizeB - 8*sizeWS =>
     AC.get_cast_direct p o = BS.sliceget p (o * 8).
  proof.
  move => Ho; rewrite /get_cast_direct.
  apply WS.wordP => k kb.
  rewrite WSu8.pack'RwE 1:/# WSu8.Pack.initiE 1:/#.
  rewrite /of_word_array /=.
  rewrite AW.WArrayN.initiE 1:/# /=.
  rewrite AW.Wu8.bits'SiE 1:/#.
  have HH := BS.BVA_asliceget_Top_CircuitBindings_BSWAS_WB_t_Top_CircuitBindings_BSWAS_WS_t_Top_CircuitBindings_BSWAS_A_t.bvaslicegetP p (o * 8) _; first by smt().
  rewrite -(get_w2bits (BS.sliceget p (o*8)) k) HH 1:/#.
  rewrite nth_take 1,2:/# nth_drop 1,2:/# (nth_flatten false (8*sizeWB)).
  + rewrite allP /= => x; rewrite mapP => He; elim He; smt(WB.size_w2bits).
  rewrite (nth_map witness); 1: by rewrite size_to_list; smt(ltz_divLR divz_ge0 rg_sizeWB).
  rewrite get_w2bits get_to_list.
  (* match the byte-decomposed (extraction) index with the bit index (o*8+k) *)
  have decomp : o*8+k = ((o+k%/8)%/sizeWB)*(8*sizeWB) + (((o+k%/8)%%sizeWB)*8+k%%8) by smt(divz_eq).
  have rbound : 0 <= ((o+k%/8)%%sizeWB)*8+k%%8 < 8*sizeWB by smt(modz_ge0 ltz_pmod rg_sizeWB).
  have hd : (((o+k%/8)%%sizeWB)*8+k%%8) %/ (8*sizeWB) = 0 by apply pdiv_small; exact rbound.
  have hm : (((o+k%/8)%%sizeWB)*8+k%%8) %% (8*sizeWB) = ((o+k%/8)%%sizeWB)*8+k%%8 by apply pmod_small; exact rbound.
  have e1 : (o*8+k)%/(8*sizeWB) = (o+k%/8)%/sizeWB by rewrite {1}decomp divzMDl 1:/# hd.
  have e2 : (o*8+k)%%(8*sizeWB) = ((o+k%/8)%%sizeWB)*8+k%%8 by rewrite {1}decomp modzMDl hm.
  by rewrite e1 e2.
  qed.

  lemma set_castE (t : WB.t A.t) o (s : WS.t) :
    0 <= o*8 <= 8*sizeWB*sizeB - 8*sizeWS =>
     AC.set_cast_direct t o s = BS.sliceset t (o * 8) s.
  proof.
  move => Ho; rewrite /set_cast_direct; apply A.tP => k kb.
  rewrite /to_word_array A.initiE 1:/# /=.
  apply WB.wordP => i ib.
  rewrite /wa_get /wa_get_direct.
  rewrite AW.Wu8.pack'RwE 1:/#.
  rewrite AW.Wu8.Pack.initiE 1:/#.
  rewrite /= AW.WArrayN.initiE 1:/# /=.
  have HH := BS.BVA_asliceset_Top_CircuitBindings_BSWAS_WB_t_Top_CircuitBindings_BSWAS_WS_t_Top_CircuitBindings_BSWAS_A_t.bvaslicesetP t (o * 8) s _ (k*(8*sizeWB)+i) _; 1,2: by smt().
  rewrite (flat_bitE (BS.sliceset t (o*8) s) k i) 1,2:/#.
  rewrite HH.
  have -> : (o * 8 <= k * (8*sizeWB) + i < o * 8 + 8*sizeWS) = (o <= sizeWB * k + i %/ 8 < o + sizeWS) by smt(divz_eq).
  rewrite fun_if (fun_if (fun (g : int -> bool) => g (i %% 8))) /=.
  rewrite WSu8.bits'SiE 1:/#.
  rewrite /of_word_array AW.WArrayN.initiE 1:/# /= AW.Wu8.bits'SiE 1:/# -(flat_bitE t k i) 1,2:/#.
  smt(divz_eq).
  qed.
end XArrayAccessCast.
