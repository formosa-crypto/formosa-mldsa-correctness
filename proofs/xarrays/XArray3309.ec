(* -------------------------------------------------------------------- *)
(* Byte-element bridge for the 3309-byte array (signature):                *)
(* \bits8 element/byte lemmas for W128 <-> W8 Array3309 casts.              *)
(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array3309.

from Jasmin require import JWord.

export Array3309.Array3309.

require import WArray3309 BitEncoding.
require import ArrayAccessCastW128_3309W8 ArrayWords3309W8.
require import XArrayAccessCastByte.
import Array3309 BitChunking.

clone import XArrayAccessCastByte as X3309u128 with
      op sizeWS <- 16,
      op sizeB  <- 3309,
  theory WS     <- W128 { rename "_XX" as "_128" },
  theory A      <- Array3309,
  theory AW     <- ArrayWords3309W8,
  theory AC     <- ArrayAccessCastW128_3309W8
  proof rg_sizeWS by done, gt0_sizeB by done, le_slice by done.

lemma get_cast128_3309W8E (t : W8.t Array3309.t) (o j : int) :
  0 <= o => o + 16 <= 3309 => 0 <= j < 16 =>
   (ArrayAccessCastW128_3309W8.get_cast_direct t o) \bits8 j = t.[o + j].
proof.
move => ho hos hj; rewrite -X3309u128.get_cast_bits'SE 1,2,3:/#.
apply W8.wordP => b hb.
rewrite bits8iE 1:/# ArrayAccessCastW128_3309W8.WSu8.bits'SiE 1:/# /#.
qed.

lemma set_cast128_3309W8E (t : W8.t Array3309.t) (o k : int) (s : W128.t) :
  0 <= o => o + 16 <= 3309 => 0 <= k < 3309 =>
   (ArrayAccessCastW128_3309W8.set_cast_direct t o s).[k]
   = if o <= k < o + 16 then s \bits8 (k - o) else t.[k].
proof.
move => ho hos hk; rewrite X3309u128.set_cast_directE 1,2,3:/#.
case (o <= k < o + 16) => hc; 2:done.
apply W8.wordP => b hb.
rewrite ArrayAccessCastW128_3309W8.WSu8.bits'SiE 1:/# bits8iE 1:/# /#.
qed.

(* Byte read of a stored word after the outer to_word_array/init has been
   peeled (read-for-hash / read-back sites); drop-in for old get8_set128_directE. *)
lemma get8_set_cast128_3309W8E (t : W8.t Array3309.t) (o k : int) (s : W128.t) :
  0 <= o => o + 16 <= 3309 => 0 <= k < 3309 =>
   ArrayWords3309W8.wa_get_direct
     (ArrayWords3309W8.WArrayN.init (fun (j : int) =>
        if o <= j < o + 16 then ArrayAccessCastW128_3309W8.WSu8.(\bits'S) s (j - o)
        else (ArrayWords3309W8.of_word_array t).[j])) k
   = if o <= k < o + 16 then s \bits8 (k - o) else t.[k].
proof.
move => ho hos hk; rewrite -set_cast128_3309W8E 1,2,3:/#.
by rewrite /set_cast_direct /to_word_array Array3309.initiE 1:/#.
qed.
