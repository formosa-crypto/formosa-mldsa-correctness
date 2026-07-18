(* -------------------------------------------------------------------- *)
(* Byte-element bridge for the 4032-byte array (secret key sk):            *)
(* \bits8 element/byte lemmas for W256 <-> W8 Array4032 casts.              *)
(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array4032.

from Jasmin require import JWord.

export Array4032.Array4032.

require import WArray4032 BitEncoding.
require import ArrayAccessCastW256_4032W8 ArrayWords4032W8.
require import XArrayAccessCastByte.
import Array4032 BitChunking.

clone import XArrayAccessCastByte as X4032u256 with
      op sizeWS <- 32,
      op sizeB  <- 4032,
  theory WS     <- W256 { rename "_XX" as "_256" },
  theory A      <- Array4032,
  theory AW     <- ArrayWords4032W8,
  theory AC     <- ArrayAccessCastW256_4032W8
  proof rg_sizeWS by done, gt0_sizeB by done, le_slice by done.

lemma get_cast256_4032W8E (t : W8.t Array4032.t) (o j : int) :
  0 <= o => o + 32 <= 4032 => 0 <= j < 32 =>
   (ArrayAccessCastW256_4032W8.get_cast_direct t o) \bits8 j = t.[o + j].
proof.
move => ho hos hj; rewrite -X4032u256.get_cast_bits'SE 1,2,3:/#.
apply W8.wordP => b hb.
rewrite bits8iE 1:/# ArrayAccessCastW256_4032W8.WSu8.bits'SiE 1:/# /#.
qed.

lemma set_cast256_4032W8E (t : W8.t Array4032.t) (o k : int) (s : W256.t) :
  0 <= o => o + 32 <= 4032 => 0 <= k < 4032 =>
   (ArrayAccessCastW256_4032W8.set_cast_direct t o s).[k]
   = if o <= k < o + 32 then s \bits8 (k - o) else t.[k].
proof.
move => ho hos hk; rewrite X4032u256.set_cast_directE 1,2,3:/#.
case (o <= k < o + 32) => hc; 2:done.
apply W8.wordP => b hb.
rewrite ArrayAccessCastW256_4032W8.WSu8.bits'SiE 1:/# bits8iE 1:/# /#.
qed.

(* Byte read of a stored word after the outer to_word_array/init has been
   peeled (read-for-hash sites); drop-in for the old get8_set256_directE. *)
lemma get8_set_cast256_4032W8E (t : W8.t Array4032.t) (o k : int) (s : W256.t) :
  0 <= o => o + 32 <= 4032 => 0 <= k < 4032 =>
   ArrayWords4032W8.wa_get_direct
     (ArrayWords4032W8.WArrayN.init (fun (j : int) =>
        if o <= j < o + 32 then ArrayAccessCastW256_4032W8.WSu8.(\bits'S) s (j - o)
        else (ArrayWords4032W8.of_word_array t).[j])) k
   = if o <= k < o + 32 then s \bits8 (k - o) else t.[k].
proof.
move => ho hos hk; rewrite -set_cast256_4032W8E 1,2,3:/#.
by rewrite /set_cast_direct /to_word_array Array4032.initiE 1:/#.
qed.
