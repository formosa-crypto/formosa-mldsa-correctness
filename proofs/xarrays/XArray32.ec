(* -------------------------------------------------------------------- *)
(* Byte-element bridge for the 32-byte array (ArrayAccessCastW256_32W8):    *)
(* \bits8 element/byte lemmas for W256 <-> W8 Array32 casts.                 *)
(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array32.

from Jasmin require import JWord.

export Array32.Array32.

require import WArray32 BitEncoding.
require import ArrayAccessCastW256_32W8 ArrayWords32W8.
require import XArrayAccessCastByte.
import Array32 BitChunking.

clone import XArrayAccessCastByte as X32u256 with
      op sizeWS <- 32,
      op sizeB  <- 32,
  theory WS     <- W256 { rename "_XX" as "_256" },
  theory A      <- Array32,
  theory AW     <- ArrayWords32W8,
  theory AC     <- ArrayAccessCastW256_32W8
  proof rg_sizeWS by done, gt0_sizeB by done, le_slice by done.

(* byte j of a W256 read from the array = source byte at o+j *)
lemma get_cast256_32W8E (t : W8.t Array32.t) (o j : int) :
  0 <= o => o + 32 <= 32 => 0 <= j < 32 =>
   (ArrayAccessCastW256_32W8.get_cast_direct t o) \bits8 j = t.[o + j].
proof.
move => ho hos hj; rewrite -X32u256.get_cast_bits'SE 1,2,3:/#.
apply W8.wordP => b hb.
rewrite bits8iE 1:/# ArrayAccessCastW256_32W8.WSu8.bits'SiE 1:/# /#.
qed.

(* element of a W256 store into the array, in standard \bits8 *)
lemma set_cast256_32W8E (t : W8.t Array32.t) (o k : int) (s : W256.t) :
  0 <= o => o + 32 <= 32 => 0 <= k < 32 =>
   (ArrayAccessCastW256_32W8.set_cast_direct t o s).[k]
   = if o <= k < o + 32 then s \bits8 (k - o) else t.[k].
proof.
move => ho hos hk; rewrite X32u256.set_cast_directE 1,2,3:/#.
case (o <= k < o + 32) => hc; 2:done.
apply W8.wordP => b hb.
rewrite ArrayAccessCastW256_32W8.WSu8.bits'SiE 1:/# bits8iE 1:/# /#.
qed.
