(* -------------------------------------------------------------------- *)
(* Byte-element bridge for the 64-byte array (ArrayAccessCastW256_64W8):    *)
(* \bits8 element/byte lemmas for W256 <-> W8 Array64 casts.                 *)
(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array64.

from Jasmin require import JWord.

export Array64.Array64.

require import WArray64 BitEncoding.
require import ArrayAccessCastW256_64W8 ArrayWords64W8.
require import XArrayAccessCastByte.
import Array64 BitChunking.

clone import XArrayAccessCastByte as X64u256 with
      op sizeWS <- 32,
      op sizeB  <- 64,
  theory WS     <- W256 { rename "_XX" as "_256" },
  theory A      <- Array64,
  theory AW     <- ArrayWords64W8,
  theory AC     <- ArrayAccessCastW256_64W8
  proof rg_sizeWS by done, gt0_sizeB by done, le_slice by done.

(* byte j of a W256 read from the array = source byte at o+j *)
lemma get_cast256_64W8E (t : W8.t Array64.t) (o j : int) :
  0 <= o => o + 32 <= 64 => 0 <= j < 32 =>
   (ArrayAccessCastW256_64W8.get_cast_direct t o) \bits8 j = t.[o + j].
proof.
move => ho hos hj; rewrite -X64u256.get_cast_bits'SE 1,2,3:/#.
apply W8.wordP => b hb.
rewrite bits8iE 1:/# ArrayAccessCastW256_64W8.WSu8.bits'SiE 1:/# /#.
qed.

(* element of a W256 store into the array, in standard \bits8 *)
lemma set_cast256_64W8E (t : W8.t Array64.t) (o k : int) (s : W256.t) :
  0 <= o => o + 32 <= 64 => 0 <= k < 64 =>
   (ArrayAccessCastW256_64W8.set_cast_direct t o s).[k]
   = if o <= k < o + 32 then s \bits8 (k - o) else t.[k].
proof.
move => ho hos hk; rewrite X64u256.set_cast_directE 1,2,3:/#.
case (o <= k < o + 32) => hc; 2:done.
apply W8.wordP => b hb.
rewrite ArrayAccessCastW256_64W8.WSu8.bits'SiE 1:/# bits8iE 1:/# /#.
qed.
