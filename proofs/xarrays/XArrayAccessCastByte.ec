(* -------------------------------------------------------------------- *)
(* Byte-array variant of XArrayAccessCast: the element word is the         *)
(* bootstrap byte word W8, which satisfies WT and BitWord but NOT           *)
(* BitWordSH (its shift_mask would self-reference W8), so it cannot be       *)
(* substituted into a BitWordSH slot.  We therefore pin WB = concrete W8     *)
(* (sizeWB = 1) and keep only the slice word WS (BitWordSH) and length        *)
(* parametric.  Same one-time proof as XArrayAccessCast.                      *)
(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv BitEncoding JWordExtra JArrayExtra CircuitBindings.
from Jasmin require import JWord JArray JWord_array.
import BitChunking.

abstract theory XArrayAccessCastByte.
  op sizeWS : int.   (* bytes per slice word        *)
  op sizeB  : int.   (* array length (in bytes)     *)

  axiom rg_sizeWS : 1 <= sizeWS <= 32.
  axiom gt0_sizeB : 0 < sizeB.
  axiom le_slice  : sizeWS <= sizeB.

  clone import BitWordSH as WS with op size <- 8 * sizeWS
    proof gt0_size by smt(rg_sizeWS), size_le_256 by smt(rg_sizeWS).
  clone import PolyArray as A with op size <- sizeB
    proof ge0_size by smt(gt0_sizeB).

  (* extraction side (AW builds its own byte-array WArrayN internally) *)
  clone import ArrayWords as AW with
        op sizeW <- 1,
        op sizeA <- sizeB,
    theory Word    <= W8,
    theory ArrayN  <= A
    proof gt0_sizeW by done, gt0_sizeA by smt(gt0_sizeB).

  clone import ArrayAccessCast as AC with
        op sizeWS      <- sizeWS,
        op sizeWB      <- 1,
        op sizeB       <- sizeB,
    theory WordS       <- WS,
    theory WordB       <- W8,
    theory ArrayWordsB <= AW
    proof gt0_sizeWS by smt(rg_sizeWS), gt0_sizeWB by done, gt0_sizeB by smt(gt0_sizeB).

  (* circuit side, over the SAME word/array (BSWAS.WB is a BitWord -> rename) *)
  clone import BSWAS as BS with
        op asize <- sizeB,
        op bsize <- 8,
        op ssize <- 8 * sizeWS,
    theory A     <- A,
    theory WB    <- W8 { rename "_XX" as "_8" },
    theory WS    <- WS
    proof le_size by smt(le_slice rg_sizeWS gt0_sizeB).

  lemma flat_bitE (a : W8.t A.t) (w b : int) :
    0 <= w < sizeB => 0 <= b < 8 =>
    a.[w].[b] = nth false (flatten (map W8.w2bits (A.to_list a))) (w * 8 + b).
  proof.
  move => hw hb.
  rewrite (nth_flatten false 8).
  + rewrite allP /= => x; rewrite mapP => He; elim He; smt(W8.size_w2bits).
  have -> : (w*8+b) %/ 8 = w by smt(divzMDl divz_small).
  have -> : (w*8+b) %% 8 = b by smt(modzMDl modz_small).
  by rewrite (nth_map witness) 1:size_to_list 1:/# get_w2bits get_to_list.
  qed.

  lemma get_castE (p : W8.t A.t) o :
    0 <= o*8 <= 8*sizeB - 8*sizeWS =>
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
  rewrite nth_take 1,2:/# nth_drop 1,2:/# (nth_flatten false 8).
  + rewrite allP /= => x; rewrite mapP => He; elim He; smt(W8.size_w2bits).
  rewrite (nth_map witness); 1: by rewrite size_to_list; smt(ltz_divLR divz_ge0).
  rewrite get_w2bits get_to_list.
  have decomp : o*8+k = ((o+k%/8)%/1)*8 + (((o+k%/8)%%1)*8+k%%8) by smt(divz_eq).
  have rbound : 0 <= ((o+k%/8)%%1)*8+k%%8 < 8 by smt(modz_ge0 ltz_pmod).
  have hd : (((o+k%/8)%%1)*8+k%%8) %/ 8 = 0 by apply pdiv_small; exact rbound.
  have hm : (((o+k%/8)%%1)*8+k%%8) %% 8 = ((o+k%/8)%%1)*8+k%%8 by apply pmod_small; exact rbound.
  have e1 : (o*8+k)%/8 = (o+k%/8)%/1 by rewrite {1}decomp divzMDl 1:/# hd.
  have e2 : (o*8+k)%%8 = ((o+k%/8)%%1)*8+k%%8 by rewrite {1}decomp modzMDl hm.
  by rewrite e1 e2.
  qed.

  lemma set_castE (t : W8.t A.t) o (s : WS.t) :
    0 <= o*8 <= 8*sizeB - 8*sizeWS =>
     AC.set_cast_direct t o s = BS.sliceset t (o * 8) s.
  proof.
  move => Ho; rewrite /set_cast_direct; apply A.tP => k kb.
  rewrite /to_word_array A.initiE 1:/# /=.
  apply W8.wordP => i ib.
  rewrite /wa_get /wa_get_direct.
  rewrite AW.Wu8.pack'RwE 1:/#.
  rewrite AW.Wu8.Pack.initiE 1:/#.
  rewrite /= AW.WArrayN.initiE 1:/# /=.
  have HH := BS.BVA_asliceset_Top_CircuitBindings_BSWAS_WB_t_Top_CircuitBindings_BSWAS_WS_t_Top_CircuitBindings_BSWAS_A_t.bvaslicesetP t (o * 8) s _ (k*8+i) _; 1,2: by smt().
  rewrite (flat_bitE (BS.sliceset t (o*8) s) k i) 1,2:/#.
  rewrite HH.
  have -> : (o * 8 <= k * 8 + i < o * 8 + 8*sizeWS) = (o <= 1 * k + i %/ 8 < o + sizeWS) by smt(divz_eq).
  rewrite fun_if (fun_if (fun (g : int -> bool) => g (i %% 8))) /=.
  rewrite WSu8.bits'SiE 1:/#.
  rewrite /of_word_array AW.WArrayN.initiE 1:/# /= AW.Wu8.bits'SiE 1:/# -(flat_bitE t k i) 1,2:/#.
  smt(divz_eq).
  qed.

  (* Element of a WS-word store into the byte array: the warray analogue of
     get8_set16_directE.  Stated in the bridge's own byte op WSu8.\bits'S. *)
  lemma set_cast_directE (t : W8.t A.t) (o k : int) (s : WS.t) :
    0 <= o => o + sizeWS <= sizeB => 0 <= k < sizeB =>
     (AC.set_cast_direct t o s).[k]
     = if o <= k < o + sizeWS then WSu8.(\bits'S) s (k - o) else t.[k].
  proof.
  move => ho hos hk; rewrite /set_cast_direct.
  rewrite /to_word_array A.initiE 1:/# /=.
  apply W8.wordP => i ib.
  rewrite /wa_get /wa_get_direct.
  rewrite AW.Wu8.pack'RwE 1:/# AW.Wu8.Pack.initiE 1:/# /=.
  rewrite AW.WArrayN.initiE 1:/# /=.
  have hi0 : i %/ 8 = 0 by smt().
  have him : i %% 8 = i by smt().
  rewrite hi0 him /=.
  case (o <= k < o + sizeWS) => hc.
  + done.
  + rewrite /of_word_array AW.WArrayN.initiE 1:/# /= AW.Wu8.bits'SiE 1:/# /#.
  qed.

  (* Byte of a WS-word read from the byte array: (get_cast_direct t o) byte j
     is the source byte at o+j.  Companion for array-to-array copies. *)
  lemma get_cast_bits'SE (t : W8.t A.t) (o j : int) :
    0 <= o => o + sizeWS <= sizeB => 0 <= j < sizeWS =>
     WSu8.(\bits'S) (AC.get_cast_direct t o) j = t.[o + j].
  proof.
  move => ho hos hj; rewrite /get_cast_direct.
  rewrite WSu8.pack'RbE 1:/# WSu8.Pack.initiE 1:/# /=.
  rewrite /of_word_array AW.WArrayN.initiE 1:/# /=.
  apply W8.wordP => b bb.
  rewrite AW.Wu8.bits'SiE 1:/# /#.
  qed.
end XArrayAccessCastByte.
