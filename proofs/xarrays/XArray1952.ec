(* -------------------------------------------------------------------- *)
(* Byte-element bridge for the 1952-byte array (verification_key):         *)
(* \bits8 element/byte lemmas for W256 <-> W8 Array1952 casts.              *)
(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array1952.

from Jasmin require import JWord.

export Array1952.Array1952.

require import WArray1952 BitEncoding.
require import ArrayAccessCastW256_1952W8 ArrayWords1952W8.
require import XArrayAccessCastByte.
import Array1952 BitChunking.

clone import XArrayAccessCastByte as X1952u256 with
      op sizeWS <- 32,
      op sizeB  <- 1952,
  theory WS     <- W256 { rename "_XX" as "_256" },
  theory A      <- Array1952,
  theory AW     <- ArrayWords1952W8,
  theory AC     <- ArrayAccessCastW256_1952W8
  proof rg_sizeWS by done, gt0_sizeB by done, le_slice by done.

lemma get_cast256_1952W8E (t : W8.t Array1952.t) (o j : int) :
  0 <= o => o + 32 <= 1952 => 0 <= j < 32 =>
   (ArrayAccessCastW256_1952W8.get_cast_direct t o) \bits8 j = t.[o + j].
proof.
move => ho hos hj; rewrite -X1952u256.get_cast_bits'SE 1,2,3:/#.
apply W8.wordP => b hb.
rewrite bits8iE 1:/# ArrayAccessCastW256_1952W8.WSu8.bits'SiE 1:/# /#.
qed.

lemma set_cast256_1952W8E (t : W8.t Array1952.t) (o k : int) (s : W256.t) :
  0 <= o => o + 32 <= 1952 => 0 <= k < 1952 =>
   (ArrayAccessCastW256_1952W8.set_cast_direct t o s).[k]
   = if o <= k < o + 32 then s \bits8 (k - o) else t.[k].
proof.
move => ho hos hk; rewrite X1952u256.set_cast_directE 1,2,3:/#.
case (o <= k < o + 32) => hc; 2:done.
apply W8.wordP => b hb.
rewrite ArrayAccessCastW256_1952W8.WSu8.bits'SiE 1:/# bits8iE 1:/# /#.
qed.

(* Byte read of a stored word after the outer to_word_array/init has been
   peeled (as it is when the array is re-read via get8 to feed a hash): the
   unfolded set_cast_direct guts reduce to the same if-shape. Drop-in for the
   old get8_set256_directE at read-for-hash sites. *)
lemma get8_set_cast256_1952W8E (t : W8.t Array1952.t) (o k : int) (s : W256.t) :
  0 <= o => o + 32 <= 1952 => 0 <= k < 1952 =>
   ArrayWords1952W8.wa_get_direct
     (ArrayWords1952W8.WArrayN.init (fun (j : int) =>
        if o <= j < o + 32 then ArrayAccessCastW256_1952W8.WSu8.(\bits'S) s (j - o)
        else (ArrayWords1952W8.of_word_array t).[j])) k
   = if o <= k < o + 32 then s \bits8 (k - o) else t.[k].
proof.
move => ho hos hk; rewrite -set_cast256_1952W8E 1,2,3:/#.
by rewrite /set_cast_direct /to_word_array Array1952.initiE 1:/#.
qed.
