(* -------------------------------------------------------------------- *)
(* W32-lane element bridge for the mask-copy loop (Array1280 of W32).      *)
(* Reduces the warray ArrayAccessCastW256_1280W32 cast ops to the proven   *)
(* old-model WArray5120 helpers via of_word_array = init32.                *)
(* -------------------------------------------------------------------- *)
require import AllCore IntDiv.

from Jasmin require import JModel_x86.

require import Array1280 WArray5120.
require import ArrayAccessCastW256_1280W32 ArrayWords1280W32.
require import XArray5120.

(* The bridge's per-slice byte extractor is just W256's \bits8. *)
lemma bits'S_bits8E (w : W256.t) (b : int) :
  0 <= b < 32 => ArrayAccessCastW256_1280W32.WSu8.(\bits'S) w b = w \bits8 b.
proof.
move => hb; apply W8.wordP => k kb.
by rewrite ArrayAccessCastW256_1280W32.WSu8.bits'SiE 1:/# bits8iE 1:/# /#.
qed.

(* ArrayWords1280W32.wa_get is WArray5120.get32 (both pack 4 bytes -> W32). *)
lemma wa_get_get32E (wa : WArray5120.t) (i : int) :
  0 <= i < 1280 => ArrayWords1280W32.wa_get wa i = WArray5120.get32 wa i.
proof.
move => hi; rewrite /wa_get_direct /get32_direct /=.
apply W32.wordP => k kb.
rewrite ArrayWords1280W32.Wu8.pack'RwE 1:/# ArrayWords1280W32.Wu8.Pack.initiE 1:/# /=.
by rewrite pack4wE 1:/# W4u8.Pack.initiE 1:/# /#.
qed.

(* get32 reading back the byte-view of a W32 array yields the source word. *)
lemma get32_of_word_arrayE (t : W32.t Array1280.t) (i : int) :
  0 <= i < 1280 => WArray5120.get32 (ArrayWords1280W32.of_word_array t) i = t.[i].
proof.
move => hi; rewrite /get32_direct /of_word_array /=.
apply W32.wordP => k kb.
rewrite pack4wE 1:/# W4u8.Pack.initiE 1:/# /=.
rewrite WArray5120.initiE 1:/# /=.
by rewrite ArrayWords1280W32.Wu8.bits'SiE 1:/# /#.
qed.

(* of_word_array is init32 of the word accessor. *)
lemma of_word_array_init32E (t : W32.t Array1280.t) :
  ArrayWords1280W32.of_word_array t = WArray5120.init32 (fun i => t.[i]).
proof.
rewrite /of_word_array /init32; apply WArray5120.ext_eq => k hk.
rewrite !WArray5120.initiE 1,2:/# /=.
apply W8.wordP => i ib.
by rewrite ArrayWords1280W32.Wu8.bits'SiE 1:/# bits8iE 1:/# /#.
qed.

(* --- The two lemmas the mask-copy invariant proof consumes. --- *)

(* Element of a W256 store into the W32 array, after the outer
   to_word_array/init has been peeled by Array1280.initiE. *)
lemma get32_set_cast256_1280W32E (t : W32.t Array1280.t) (j i : int) (w : W256.t) :
  0 <= j => j + 32 <= 5120 => j %% 4 = 0 => 0 <= i < 1280 =>
  ArrayWords1280W32.wa_get
    (WArray5120.init (fun (j0 : int) =>
        if j <= j0 < j + 32
        then ArrayAccessCastW256_1280W32.WSu8.(\bits'S) w (j0 - j)
        else (ArrayWords1280W32.of_word_array t).[j0])) i
  = if j %/ 4 <= i < j %/ 4 + 8 then w \bits32 (i - j %/ 4) else t.[i].
proof.
move => hj hj2 hjm hi.
have -> : (WArray5120.init (fun (j0 : int) =>
        if j <= j0 < j + 32
        then ArrayAccessCastW256_1280W32.WSu8.(\bits'S) w (j0 - j)
        else (ArrayWords1280W32.of_word_array t).[j0]))
      = WArray5120.set256_direct (ArrayWords1280W32.of_word_array t) j w.
+ rewrite /set256_direct; apply WArray5120.ext_eq => k hk.
  rewrite !WArray5120.initiE 1,2:/# /=.
  case (j <= k < j + 32) => hc; 2: done.
  by rewrite bits'S_bits8E 1:/#.
rewrite wa_get_get32E 1:/# get32_set256_direct_eq 1,2,3,4:/#.
case (j %/ 4 <= i < j %/ 4 + 8) => hc; 1: done.
by rewrite get32_of_word_arrayE 1:/#.
qed.

(* Lane of a W256 read from the W32 array: the k-th W32 lane is the
   source word at j/4 + k. *)
lemma get_cast256_1280W32E (t : W32.t Array1280.t) (j k : int) :
  0 <= j => j + 32 <= 5120 => j %% 4 = 0 => 0 <= k < 8 =>
  (ArrayAccessCastW256_1280W32.get_cast_direct t j) \bits32 k = t.[j %/ 4 + k].
proof.
move => hj hj2 hjm hk.
have -> : ArrayAccessCastW256_1280W32.get_cast_direct t j
        = WArray5120.get256_direct (ArrayWords1280W32.of_word_array t) j.
+ rewrite /get_cast_direct /get256_direct.
  apply W256.wordP => b hb.
  rewrite pack32wE 1:/# W32u8.Pack.initiE 1:/# /=.
  rewrite ArrayAccessCastW256_1280W32.WSu8.pack'RwE 1:/#.
  by rewrite ArrayAccessCastW256_1280W32.WSu8.Pack.initiE 1:/# /=.
by rewrite of_word_array_init32E get256_direct_init32_bits32 1,2,3,4:/#.
qed.
