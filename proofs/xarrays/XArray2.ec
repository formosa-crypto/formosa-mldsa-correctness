(* -------------------------------------------------------------------- *)
(* Byte-element bridge for the 2-byte array (ArrayAccessCastW16_2W8): the  *)
(* warray analogue of get8_set16_directE for the W16 domain-separator      *)
(* store.  Wires XArrayAccessCastByte.set_cast_directE to the extraction    *)
(* clone and reconciles its internal byte op WSu8.\bits'S with \bits8.      *)
(* -------------------------------------------------------------------- *)
require import AllCore List IntDiv JWordExtra JArrayExtra CircuitBindings.
require (*--*) Array2.

from Jasmin require import JWord.

export Array2.Array2.

require import WArray2 BitEncoding.
require import ArrayAccessCastW16_2W8 ArrayWords2W8.
require import XArrayAccessCastByte.
import Array2 BitChunking.

(* -------------------------------------------------------------------- *)
clone import XArrayAccessCastByte as X2u16 with
      op sizeWS <- 2,
      op sizeB  <- 2,
  theory WS     <- W16 { rename "_XX" as "_16" },
  theory A      <- Array2,
  theory AW     <- ArrayWords2W8,
  theory AC     <- ArrayAccessCastW16_2W8
  proof rg_sizeWS by done, gt0_sizeB by done, le_slice by done.

(* Element of the W16 register store into the 2-byte array, in standard
   \bits8 (drop-in replacement for get8_set16_directE at offset 0). *)
lemma set_cast16_2W8E (a : W8.t Array2.t) (w : W16.t) (k : int) :
  0 <= k < 2 =>
  (ArrayAccessCastW16_2W8.set_cast a 0 w).[k] = w \bits8 k.
proof.
move => hk.
rewrite /ArrayAccessCastW16_2W8.set_cast /=.
rewrite X2u16.set_cast_directE 1,2,3:/#.
rewrite ifT 1:/#.
apply W8.wordP => b hb.
rewrite ArrayAccessCastW16_2W8.WSu8.bits'SiE 1:/# bits8iE 1:/# /#.
qed.

(* to_list of the W16 register store = the word's own byte list (neutral form
   used by the 4x absorb contracts). *)
lemma to_list_set_cast16 (w : W16.t) :
  to_list (ArrayAccessCastW16_2W8.set_cast witness<:W8.t Array2.t> 0 w) = to_list w.
proof.
apply (eq_from_nth witness).
+ by rewrite Array2.size_to_list size_to_list.
move => i; rewrite Array2.size_to_list => hi.
rewrite get_to_list set_cast16_2W8E 1:/#.
rewrite (nth_change_dfl (W8.of_int 0) witness) 1:size_to_list 1:/#.
by rewrite nth_to_list bits8E.
qed.
