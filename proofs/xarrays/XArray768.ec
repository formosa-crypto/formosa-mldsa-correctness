(* -------------------------------------------------------------------- *)
(* Byte-element bridge for the 768-byte array (ArrayAccessCastW256_768W8):  *)
(* \bits8 element/byte lemmas for W256 <-> W8 Array768 casts.                *)
(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array768.

from Jasmin require import JWord.

export Array768.Array768.

require import WArray768 BitEncoding.
require import ArrayAccessCastW256_768W8 ArrayWords768W8.
require import XArrayAccessCastByte.
import Array768 BitChunking.

clone import XArrayAccessCastByte as X768u256 with
      op sizeWS <- 32,
      op sizeB  <- 768,
  theory WS     <- W256 { rename "_XX" as "_256" },
  theory A      <- Array768,
  theory AW     <- ArrayWords768W8,
  theory AC     <- ArrayAccessCastW256_768W8
  proof rg_sizeWS by done, gt0_sizeB by done, le_slice by done.

lemma get_cast256_768W8E (t : W8.t Array768.t) (o j : int) :
  0 <= o => o + 32 <= 768 => 0 <= j < 32 =>
   (ArrayAccessCastW256_768W8.get_cast_direct t o) \bits8 j = t.[o + j].
proof.
move => ho hos hj; rewrite -X768u256.get_cast_bits'SE 1,2,3:/#.
apply W8.wordP => b hb.
rewrite bits8iE 1:/# ArrayAccessCastW256_768W8.WSu8.bits'SiE 1:/# /#.
qed.

lemma set_cast256_768W8E (t : W8.t Array768.t) (o k : int) (s : W256.t) :
  0 <= o => o + 32 <= 768 => 0 <= k < 768 =>
   (ArrayAccessCastW256_768W8.set_cast_direct t o s).[k]
   = if o <= k < o + 32 then s \bits8 (k - o) else t.[k].
proof.
move => ho hos hk; rewrite X768u256.set_cast_directE 1,2,3:/#.
case (o <= k < o + 32) => hc; 2:done.
apply W8.wordP => b hb.
rewrite ArrayAccessCastW256_768W8.WSu8.bits'SiE 1:/# bits8iE 1:/# /#.
qed.
