require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array4 Array5 Array8 Array24 Array25 Array32 Array48 Array61 Array64 Array128
Array256 Array320 Array416 Array640 Array680 Array768 Array1280 Array1536
Array1920 Array1952 Array2496 Array3200 Array3309 Array4032 Array7680
WArray32 WArray40 WArray48 WArray61 WArray64 WArray128 WArray192 WArray200
WArray320 WArray416 WArray640 WArray680 WArray768 WArray1024 WArray1920
WArray1952 WArray2496 WArray3200 WArray3309 WArray4032 WArray5120 WArray6144
WArray30720.

abbrev zETAS_TIMES_MONTGOMERY_R =
((Array256.of_list witness)
[(W32.of_int 25847); (W32.of_int (-2608894)); (W32.of_int (-518909));
(W32.of_int 237124); (W32.of_int (-777960)); (W32.of_int (-876248));
(W32.of_int 466468); (W32.of_int 1826347); (W32.of_int 2353451);
(W32.of_int (-359251)); (W32.of_int (-2091905)); (W32.of_int 3119733);
(W32.of_int (-2884855)); (W32.of_int 3111497); (W32.of_int 2680103);
(W32.of_int 2725464); (W32.of_int 1024112); (W32.of_int (-1079900));
(W32.of_int 3585928); (W32.of_int (-549488)); (W32.of_int (-1119584));
(W32.of_int 2619752); (W32.of_int (-2108549)); (W32.of_int (-2118186));
(W32.of_int (-3859737)); (W32.of_int (-1399561)); (W32.of_int (-3277672));
(W32.of_int 1757237); (W32.of_int (-19422)); (W32.of_int 4010497);
(W32.of_int 280005); (W32.of_int 2706023); (W32.of_int 95776);
(W32.of_int 3077325); (W32.of_int 3530437); (W32.of_int (-1661693));
(W32.of_int (-3592148)); (W32.of_int (-2537516)); (W32.of_int 3915439);
(W32.of_int (-3861115)); (W32.of_int (-3043716)); (W32.of_int 3574422);
(W32.of_int (-2867647)); (W32.of_int 3539968); (W32.of_int (-300467));
(W32.of_int 2348700); (W32.of_int (-539299)); (W32.of_int (-1699267));
(W32.of_int (-1643818)); (W32.of_int 3505694); (W32.of_int (-3821735));
(W32.of_int 3507263); (W32.of_int (-2140649)); (W32.of_int (-1600420));
(W32.of_int 3699596); (W32.of_int 811944); (W32.of_int 531354);
(W32.of_int 954230); (W32.of_int 3881043); (W32.of_int 3900724);
(W32.of_int (-2556880)); (W32.of_int 2071892); (W32.of_int (-2797779));
(W32.of_int (-3930395)); (W32.of_int (-1528703)); (W32.of_int (-3677745));
(W32.of_int (-3041255)); (W32.of_int (-1452451)); (W32.of_int 3475950);
(W32.of_int 2176455); (W32.of_int (-1585221)); (W32.of_int (-1257611));
(W32.of_int 1939314); (W32.of_int (-4083598)); (W32.of_int (-1000202));
(W32.of_int (-3190144)); (W32.of_int (-3157330)); (W32.of_int (-3632928));
(W32.of_int 126922); (W32.of_int 3412210); (W32.of_int (-983419));
(W32.of_int 2147896); (W32.of_int 2715295); (W32.of_int (-2967645));
(W32.of_int (-3693493)); (W32.of_int (-411027)); (W32.of_int (-2477047));
(W32.of_int (-671102)); (W32.of_int (-1228525)); (W32.of_int (-22981));
(W32.of_int (-1308169)); (W32.of_int (-381987)); (W32.of_int 1349076);
(W32.of_int 1852771); (W32.of_int (-1430430)); (W32.of_int (-3343383));
(W32.of_int 264944); (W32.of_int 508951); (W32.of_int 3097992);
(W32.of_int 44288); (W32.of_int (-1100098)); (W32.of_int 904516);
(W32.of_int 3958618); (W32.of_int (-3724342)); (W32.of_int (-8578));
(W32.of_int 1653064); (W32.of_int (-3249728)); (W32.of_int 2389356);
(W32.of_int (-210977)); (W32.of_int 759969); (W32.of_int (-1316856));
(W32.of_int 189548); (W32.of_int (-3553272)); (W32.of_int 3159746);
(W32.of_int (-1851402)); (W32.of_int (-2409325)); (W32.of_int (-177440));
(W32.of_int 1315589); (W32.of_int 1341330); (W32.of_int 1285669);
(W32.of_int (-1584928)); (W32.of_int (-812732)); (W32.of_int (-1439742));
(W32.of_int (-3019102)); (W32.of_int (-3881060)); (W32.of_int (-3628969));
(W32.of_int 3839961); (W32.of_int 2091667); (W32.of_int 3407706);
(W32.of_int 2316500); (W32.of_int 3817976); (W32.of_int (-3342478));
(W32.of_int 2244091); (W32.of_int (-2446433)); (W32.of_int (-3562462));
(W32.of_int 266997); (W32.of_int 2434439); (W32.of_int (-1235728));
(W32.of_int 3513181); (W32.of_int (-3520352)); (W32.of_int (-3759364));
(W32.of_int (-1197226)); (W32.of_int (-3193378)); (W32.of_int 900702);
(W32.of_int 1859098); (W32.of_int 909542); (W32.of_int 819034);
(W32.of_int 495491); (W32.of_int (-1613174)); (W32.of_int (-43260));
(W32.of_int (-522500)); (W32.of_int (-655327)); (W32.of_int (-3122442));
(W32.of_int 2031748); (W32.of_int 3207046); (W32.of_int (-3556995));
(W32.of_int (-525098)); (W32.of_int (-768622)); (W32.of_int (-3595838));
(W32.of_int 342297); (W32.of_int 286988); (W32.of_int (-2437823));
(W32.of_int 4108315); (W32.of_int 3437287); (W32.of_int (-3342277));
(W32.of_int 1735879); (W32.of_int 203044); (W32.of_int 2842341);
(W32.of_int 2691481); (W32.of_int (-2590150)); (W32.of_int 1265009);
(W32.of_int 4055324); (W32.of_int 1247620); (W32.of_int 2486353);
(W32.of_int 1595974); (W32.of_int (-3767016)); (W32.of_int 1250494);
(W32.of_int 2635921); (W32.of_int (-3548272)); (W32.of_int (-2994039));
(W32.of_int 1869119); (W32.of_int 1903435); (W32.of_int (-1050970));
(W32.of_int (-1333058)); (W32.of_int 1237275); (W32.of_int (-3318210));
(W32.of_int (-1430225)); (W32.of_int (-451100)); (W32.of_int 1312455);
(W32.of_int 3306115); (W32.of_int (-1962642)); (W32.of_int (-1279661));
(W32.of_int 1917081); (W32.of_int (-2546312)); (W32.of_int (-1374803));
(W32.of_int 1500165); (W32.of_int 777191); (W32.of_int 2235880);
(W32.of_int 3406031); (W32.of_int (-542412)); (W32.of_int (-2831860));
(W32.of_int (-1671176)); (W32.of_int (-1846953)); (W32.of_int (-2584293));
(W32.of_int (-3724270)); (W32.of_int 594136); (W32.of_int (-3776993));
(W32.of_int (-2013608)); (W32.of_int 2432395); (W32.of_int 2454455);
(W32.of_int (-164721)); (W32.of_int 1957272); (W32.of_int 3369112);
(W32.of_int 185531); (W32.of_int (-1207385)); (W32.of_int (-3183426));
(W32.of_int 162844); (W32.of_int 1616392); (W32.of_int 3014001);
(W32.of_int 810149); (W32.of_int 1652634); (W32.of_int (-3694233));
(W32.of_int (-1799107)); (W32.of_int (-3038916)); (W32.of_int 3523897);
(W32.of_int 3866901); (W32.of_int 269760); (W32.of_int 2213111);
(W32.of_int (-975884)); (W32.of_int 1717735); (W32.of_int 472078);
(W32.of_int (-426683)); (W32.of_int 1723600); (W32.of_int (-1803090));
(W32.of_int 1910376); (W32.of_int (-1667432)); (W32.of_int (-1104333));
(W32.of_int (-260646)); (W32.of_int (-3833893)); (W32.of_int (-2939036));
(W32.of_int (-2235985)); (W32.of_int (-420899)); (W32.of_int (-2286327));
(W32.of_int 183443); (W32.of_int (-976891)); (W32.of_int 1612842);
(W32.of_int (-3545687)); (W32.of_int (-554416)); (W32.of_int 3919660);
(W32.of_int (-48306)); (W32.of_int (-1362209)); (W32.of_int 3937738);
(W32.of_int 1400424); (W32.of_int (-846154)); (W32.of_int 1976782);
(W32.of_int 0)]).

abbrev kECCAK1600_RC =
((Array24.of_list witness)
[(W64.of_int 1); (W64.of_int 32898); (W64.of_int (-9223372036854742902));
(W64.of_int (-9223372034707259392)); (W64.of_int 32907);
(W64.of_int 2147483649); (W64.of_int (-9223372034707259263));
(W64.of_int (-9223372036854743031)); (W64.of_int 138); (W64.of_int 136);
(W64.of_int 2147516425); (W64.of_int 2147483658); (W64.of_int 2147516555);
(W64.of_int (-9223372036854775669)); (W64.of_int (-9223372036854742903));
(W64.of_int (-9223372036854743037)); (W64.of_int (-9223372036854743038));
(W64.of_int (-9223372036854775680)); (W64.of_int 32778);
(W64.of_int (-9223372034707292150)); (W64.of_int (-9223372034707259263));
(W64.of_int (-9223372036854742912)); (W64.of_int 2147483649);
(W64.of_int (-9223372034707259384))]).

module M = {
  proc coefficient____power2round (r:W32.t) : W32.t * W32.t = {
    var highbits:W32.t;
    var lowbits:W32.t;
    var v32:W32.t;
    highbits <- r;
    highbits <- (highbits + (W32.of_int ((1 `<<` (13 - 1)) - 1)));
    highbits <- (highbits `>>` (W8.of_int 13));
    v32 <- highbits;
    v32 <- (v32 `<<` (W8.of_int 13));
    lowbits <- r;
    lowbits <- (lowbits - v32);
    return (highbits, lowbits);
  }
  proc coefficient____make_hint (a0:W32.t, a1:W32.t, msf:W64.t) : W32.t *
                                                                  W64.t = {
    var result:W32.t;
    var condition:bool;
    result <- (W32.of_int 0);
    condition <- ((W32.of_int ((8380417 - 1) %/ 32)) \slt a0);
    if (condition) {
      msf <- (update_msf condition msf);
      result <- (W32.of_int 1);
    } else {
      msf <- (update_msf (! condition) msf);
      condition <- (a0 \slt (W32.of_int (- ((8380417 - 1) %/ 32))));
      if (condition) {
        msf <- (update_msf condition msf);
        result <- (W32.of_int 1);
      } else {
        msf <- (update_msf (! condition) msf);
        condition <- (a0 = (W32.of_int (- ((8380417 - 1) %/ 32))));
        if (condition) {
          msf <- (update_msf condition msf);
          condition <- (a1 <> (W32.of_int 0));
          if (condition) {
            msf <- (update_msf condition msf);
            result <- (W32.of_int 1);
          } else {
            msf <- (update_msf (! condition) msf);
          }
        } else {
          msf <- (update_msf (! condition) msf);
        }
      }
    }
    return (result, msf);
  }
  proc coefficient____check_norm (coefficient:W32.t, threshold:int) : W8.t = {
    var result:W8.t;
    var sign_mask:W32.t;
    var c:W32.t;
    var sf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    result <- (W8.of_int 0);
    sign_mask <- coefficient;
    sign_mask <- (sign_mask `|>>` (W8.of_int 31));
    c <- coefficient;
    c <- (c `<<` (W8.of_int 1));
    c <- (c `&` sign_mask);
    coefficient <- (coefficient - c);
    ( _0,  _1, sf,  _2,  _3) <- (CMP_32 coefficient (W32.of_int threshold));
    result <- (SETcc (! sf));
    result <- (- result);
    return result;
  }
  proc coefficient____decompose (r:W32.t) : W32.t * W32.t = {
    var low_bits:W32.t;
    var high_bits:W32.t;
    var temp:W32.t;
    high_bits <- r;
    high_bits <- (high_bits + (W32.of_int 127));
    high_bits <- (high_bits `>>` (W8.of_int 7));
    temp <- high_bits;
    high_bits <- (high_bits `<<` (W8.of_int 10));
    high_bits <- (high_bits + temp);
    high_bits <- (high_bits + (W32.of_int (1 `<<` 21)));
    high_bits <- (high_bits `>>` (W8.of_int 22));
    high_bits <- (high_bits `&` (W32.of_int 15));
    temp <- high_bits;
    temp <- (temp * (W32.of_int (2 * ((8380417 - 1) %/ 32))));
    low_bits <- r;
    low_bits <- (low_bits - temp);
    temp <- (W32.of_int ((8380417 - 1) %/ 2));
    temp <- (temp - low_bits);
    temp <- (temp `|>>` (W8.of_int 31));
    temp <- (temp `&` (W32.of_int 8380417));
    low_bits <- (low_bits - temp);
    return (low_bits, high_bits);
  }
  proc coefficient____use_hint (a:W32.t, hint_0:W32.t, msf:W64.t) : W32.t *
                                                                    W64.t = {
    var a1:W32.t;
    var a0:W32.t;
    var b:bool;
    (a0, a1) <@ coefficient____decompose (a);
    b <- (hint_0 <> (W32.of_int 0));
    if (b) {
      msf <- (update_msf b msf);
      b <- ((W32.of_int 0) \slt a0);
      if (b) {
        msf <- (update_msf b msf);
        a1 <- (a1 + (W32.of_int 1));
        a1 <- (a1 `&` (W32.of_int 15));
      } else {
        msf <- (update_msf (! b) msf);
        a1 <- (a1 - (W32.of_int 1));
        a1 <- (a1 `&` (W32.of_int 15));
      }
    } else {
      msf <- (update_msf (! b) msf);
    }
    return (a1, msf);
  }
  proc error_polynomial__encode (encoded:W8.t Array128.t,
                                 polynomial:W32.t Array256.t) : W8.t Array128.t = {
    var i:W64.t;
    var coefficient:W32.t;
    var low_nibble:W32.t;
    var high_nibble:W32.t;
    var out_offset:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      coefficient <- polynomial.[(W64.to_uint i)];
      low_nibble <- (W32.of_int 4);
      low_nibble <- (low_nibble - coefficient);
      coefficient <- polynomial.[(W64.to_uint (i + (W64.of_int 1)))];
      high_nibble <- (W32.of_int 4);
      high_nibble <- (high_nibble - coefficient);
      high_nibble <- (high_nibble `<<` (W8.of_int 4));
      high_nibble <- (high_nibble `|` low_nibble);
      out_offset <- i;
      out_offset <- (out_offset `>>` (W8.of_int 1));
      encoded.[(W64.to_uint out_offset)] <- (truncateu8 high_nibble);
      i <- (i + (W64.of_int 2));
    }
    return encoded;
  }
  proc error_polynomial__decode (decoded:W32.t Array256.t,
                                 encoded:W8.t Array128.t) : W32.t Array256.t = {
    var i:W64.t;
    var nibble:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (256 %/ 2)))) {
      nibble <- (zeroextu32 encoded.[(W64.to_uint i)]);
      nibble <- (nibble `&` (W32.of_int 15));
      nibble <- (- nibble);
      nibble <- (nibble + (W32.of_int 4));
      decoded.[(W64.to_uint ((W64.of_int 2) * i))] <- nibble;
      nibble <- (zeroextu32 encoded.[(W64.to_uint i)]);
      nibble <- (nibble `>>` (W8.of_int 4));
      nibble <- (- nibble);
      nibble <- (nibble + (W32.of_int 4));
      decoded.[(W64.to_uint (((W64.of_int 2) * i) + (W64.of_int 1)))] <-
      nibble;
      i <- (i + (W64.of_int 1));
    }
    return decoded;
  }
  proc gamma1____encode_polynomial (encoded:W8.t Array640.t,
                                    polynomial:W32.t Array256.t) : W8.t Array640.t = {
    var output_offset:W64.t;
    var i:W64.t;
    var t0:W32.t;
    var t1:W32.t;
    var encoded_bytes:W32.t;
    var byte:W8.t;
    output_offset <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (256 %/ 2)))) {
      t0 <- (W32.of_int (1 `<<` 19));
      t0 <-
      (t0 -
      polynomial.[(W64.to_uint (((W64.of_int 2) * i) + (W64.of_int 0)))]);
      t1 <- (W32.of_int (1 `<<` 19));
      t1 <-
      (t1 -
      polynomial.[(W64.to_uint (((W64.of_int 2) * i) + (W64.of_int 1)))]);
      encoded_bytes <- t0;
      encoded.[(W64.to_uint output_offset)] <- (truncateu8 encoded_bytes);
      encoded_bytes <- t0;
      encoded_bytes <- (encoded_bytes `>>` (W8.of_int 8));
      encoded.[(W64.to_uint (output_offset + (W64.of_int 1)))] <-
      (truncateu8 encoded_bytes);
      encoded_bytes <- t0;
      encoded_bytes <- (encoded_bytes `>>` (W8.of_int 16));
      byte <- (truncateu8 encoded_bytes);
      encoded_bytes <- t1;
      encoded_bytes <- (encoded_bytes `<<` (W8.of_int 4));
      byte <- (byte `|` (truncateu8 encoded_bytes));
      encoded.[(W64.to_uint (output_offset + (W64.of_int 2)))] <- byte;
      encoded_bytes <- t1;
      encoded_bytes <- (encoded_bytes `>>` (W8.of_int 4));
      encoded.[(W64.to_uint (output_offset + (W64.of_int 3)))] <-
      (truncateu8 encoded_bytes);
      encoded_bytes <- t1;
      encoded_bytes <- (encoded_bytes `>>` (W8.of_int 12));
      encoded.[(W64.to_uint (output_offset + (W64.of_int 4)))] <-
      (truncateu8 encoded_bytes);
      output_offset <- (output_offset + (W64.of_int 5));
      i <- (i + (W64.of_int 1));
    }
    return encoded;
  }
  proc gamma1____decode_to_polynomial (polynomial:W32.t Array256.t,
                                       bytes:W8.t Array640.t) : W32.t Array256.t = {
    var input_offset:W64.t;
    var output_offset:W64.t;
    var coefficient:W32.t;
    var temp:W32.t;
    input_offset <- (W64.of_int 0);
    output_offset <- (W64.of_int 0);
    while ((input_offset \ult (W64.of_int ((20 * 256) %/ 8)))) {
      coefficient <- (zeroextu32 bytes.[(W64.to_uint input_offset)]);
      temp <-
      (zeroextu32 bytes.[(W64.to_uint (input_offset + (W64.of_int 1)))]);
      temp <- (temp `<<` (W8.of_int 8));
      coefficient <- (coefficient `|` temp);
      temp <-
      (zeroextu32 bytes.[(W64.to_uint (input_offset + (W64.of_int 2)))]);
      temp <- (temp `<<` (W8.of_int 16));
      coefficient <- (coefficient `|` temp);
      coefficient <- (coefficient `&` (W32.of_int 1048575));
      coefficient <- (- coefficient);
      coefficient <- (coefficient + (W32.of_int (1 `<<` 19)));
      polynomial.[(W64.to_uint (output_offset + (W64.of_int 0)))] <-
      coefficient;
      coefficient <-
      (zeroextu32 bytes.[(W64.to_uint (input_offset + (W64.of_int 2)))]);
      coefficient <- (coefficient `>>` (W8.of_int 4));
      temp <-
      (zeroextu32 bytes.[(W64.to_uint (input_offset + (W64.of_int 3)))]);
      temp <- (temp `<<` (W8.of_int 4));
      coefficient <- (coefficient `|` temp);
      temp <-
      (zeroextu32 bytes.[(W64.to_uint (input_offset + (W64.of_int 4)))]);
      temp <- (temp `<<` (W8.of_int 12));
      coefficient <- (coefficient `|` temp);
      coefficient <- (- coefficient);
      coefficient <- (coefficient + (W32.of_int (1 `<<` 19)));
      polynomial.[(W64.to_uint (output_offset + (W64.of_int 1)))] <-
      coefficient;
      input_offset <- (input_offset + (W64.of_int 5));
      output_offset <- (output_offset + (W64.of_int 2));
    }
    return polynomial;
  }
  proc gamma1____decode (decoded:W32.t Array1280.t, encoded:W8.t Array3200.t) : 
  W32.t Array1280.t = {
    var aux:W32.t Array256.t;
    var i:int;
    i <- 0;
    while ((i < 5)) {
      aux <@ gamma1____decode_to_polynomial ((Array256.init
                                             (fun i_0 => decoded.[((i * 256) +
                                                                  i_0)])
                                             ),
      (Array640.init (fun i_0 => encoded.[((i * ((20 * 256) %/ 8)) + i_0)])));
      decoded <-
      (Array1280.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  decoded.[i_0]))
      );
      i <- (i + 1);
    }
    return decoded;
  }
  proc __index_spec (x:int, y:int) : int = {
    var r:int;
    r <- ((x %% 5) + (5 * (y %% 5)));
    return r;
  }
  proc __keccak_rho_offsets_spec (i:int) : int = {
    var r:int;
    var x:int;
    var y:int;
    var t:int;
    var z:int;
    r <- 0;
    x <- 1;
    y <- 0;
    t <- 0;
    while ((t < 24)) {
      if ((i = (x + (5 * y)))) {
        r <- ((((t + 1) * (t + 2)) %/ 2) %% 64);
      } else {
        
      }
      z <- (((2 * x) + (3 * y)) %% 5);
      x <- y;
      y <- z;
      t <- (t + 1);
    }
    return r;
  }
  proc __rhotates_spec (x:int, y:int) : int = {
    var r:int;
    var i:int;
    i <@ __index_spec (x, y);
    r <@ __keccak_rho_offsets_spec (i);
    return r;
  }
  proc __rotate_left_64 (v:W64.t, rOTATE_BY:int) : W64.t = {
    var lower:W64.t;
    lower <- v;
    lower <- (lower `>>` (W8.of_int (64 - rOTATE_BY)));
    v <- (v `<<` (W8.of_int rOTATE_BY));
    v <- (v `|` lower);
    return v;
  }
  proc __theta_sum_ref1 (a:W64.t Array25.t) : W64.t Array5.t = {
    var c:W64.t Array5.t;
    var x:int;
    var y:int;
    c <- witness;
    x <- 0;
    while ((x < 5)) {
      c.[x] <- a.[(x + 0)];
      x <- (x + 1);
    }
    y <- 1;
    while ((y < 5)) {
      x <- 0;
      while ((x < 5)) {
        c.[x] <- (c.[x] `^` a.[(x + (y * 5))]);
        x <- (x + 1);
      }
      y <- (y + 1);
    }
    return c;
  }
  proc __theta_rol_ref1 (c:W64.t Array5.t) : W64.t Array5.t = {
    var aux:W64.t;
    var d:W64.t Array5.t;
    var x:int;
    d <- witness;
    x <- 0;
    while ((x < 5)) {
      d.[x] <- c.[((x + 1) %% 5)];
      aux <@ __rotate_left_64 (d.[x], 1);
      d.[x] <- aux;
      d.[x] <- (d.[x] `^` c.[(((x - 1) + 5) %% 5)]);
      x <- (x + 1);
    }
    return d;
  }
  proc __rol_sum_ref1 (a:W64.t Array25.t, d:W64.t Array5.t, y:int) : 
  W64.t Array5.t = {
    var aux:W64.t;
    var b:W64.t Array5.t;
    var x:int;
    var x_:int;
    var y_:int;
    var r:int;
    b <- witness;
    x <- 0;
    while ((x < 5)) {
      x_ <- ((x + (3 * y)) %% 5);
      y_ <- x;
      r <@ __rhotates_spec (x_, y_);
      b.[x] <- a.[(x_ + (y_ * 5))];
      b.[x] <- (b.[x] `^` d.[x_]);
      if ((r <> 0)) {
        aux <@ __rotate_left_64 (b.[x], r);
        b.[x] <- aux;
      } else {
        
      }
      x <- (x + 1);
    }
    return b;
  }
  proc __set_row_ref1 (e:W64.t Array25.t, b:W64.t Array5.t, y:int, s_rc:W64.t) : 
  W64.t Array25.t = {
    var x:int;
    var x1:int;
    var x2:int;
    var t:W64.t;
    x <- 0;
    while ((x < 5)) {
      x1 <- ((x + 1) %% 5);
      x2 <- ((x + 2) %% 5);
      t <- b.[x1];
      t <- (invw t);
      t <- (t `&` b.[x2]);
      t <- (t `^` b.[x]);
      if (((x = 0) /\ (y = 0))) {
        t <- (t `^` s_rc);
      } else {
        
      }
      e.[(x + (y * 5))] <- t;
      x <- (x + 1);
    }
    return e;
  }
  proc __round_ref1 (e:W64.t Array25.t, a:W64.t Array25.t, rc:W64.t) : 
  W64.t Array25.t = {
    var s_rc:W64.t;
    var c:W64.t Array5.t;
    var d:W64.t Array5.t;
    var y:int;
    var b:W64.t Array5.t;
    b <- witness;
    c <- witness;
    d <- witness;
    s_rc <- rc;
    c <@ __theta_sum_ref1 (a);
    d <@ __theta_rol_ref1 (c);
    y <- 0;
    while ((y < 5)) {
      b <@ __rol_sum_ref1 (a, d, y);
      e <@ __set_row_ref1 (e, b, y, s_rc);
      y <- (y + 1);
    }
    return e;
  }
  proc __keccakf1600_ref1 (a:W64.t Array25.t) : W64.t Array25.t = {
    var rC:W64.t Array24.t;
    var s_e:W64.t Array25.t;
    var e:W64.t Array25.t;
    var c:W64.t;
    var rc:W64.t;
    rC <- witness;
    e <- witness;
    s_e <- witness;
    rC <- kECCAK1600_RC;
    e <- s_e;
    c <- (W64.of_int 0);
    while ((c \ult (W64.of_int (24 - 1)))) {
      rc <- rC.[(W64.to_uint c)];
      e <@ __round_ref1 (e, a, rc);
      rc <- rC.[((W64.to_uint c) + 1)];
      a <@ __round_ref1 (a, e, rc);
      c <- (c + (W64.of_int 2));
    }
    return a;
  }
  proc _keccakf1600_ref1 (a:W64.t Array25.t) : W64.t Array25.t = {
    
    a <@ __keccakf1600_ref1 (a);
    return a;
  }
  proc __keccak_init_ref1 (state:W64.t Array25.t) : W64.t Array25.t = {
    var t:W64.t;
    var i:int;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    ( _0,  _1,  _2,  _3,  _4, t) <- (set0_64);
    i <- 0;
    while ((i < 25)) {
      state.[i] <- t;
      i <- (i + 1);
    }
    return state;
  }
  proc __hash_verification_key (verification_key:W8.t Array1952.t,
                                hash:W8.t Array64.t) : W8.t Array64.t = {
    var state_offset:W64.t;
    var verification_key_offset:W64.t;
    var state:W64.t Array25.t;
    var byte:W8.t;
    state <- witness;
    state_offset <- (W64.of_int 0);
    verification_key_offset <- (W64.of_int 0);
    (* Erased call to spill *)
    state <@ __keccak_init_ref1 (state);
    while ((verification_key_offset \ult
           (W64.of_int (((32 + (6 * (((23 - 13) * 256) %/ 8))) %/ 136) * 136)
           ))) {
      while ((state_offset \ult (W64.of_int 136))) {
        byte <- verification_key.[(W64.to_uint verification_key_offset)];
        state <-
        (Array25.init
        (WArray200.get64
        (WArray200.set8 (WArray200.init64 (fun i => state.[i]))
        (W64.to_uint state_offset)
        ((get8 (WArray200.init64 (fun i => state.[i]))
         (W64.to_uint state_offset)) `^`
        byte))));
        verification_key_offset <-
        (verification_key_offset + (W64.of_int 1));
        state_offset <- (state_offset + (W64.of_int 1));
      }
      (* Erased call to spill *)
      state <@ _keccakf1600_ref1 (state);
      (* Erased call to unspill *)
      state_offset <- (W64.of_int 0);
    }
    while ((verification_key_offset \ult
           (W64.of_int (32 + (6 * (((23 - 13) * 256) %/ 8)))))) {
      byte <- verification_key.[(W64.to_uint verification_key_offset)];
      state <-
      (Array25.init
      (WArray200.get64
      (WArray200.set8 (WArray200.init64 (fun i => state.[i]))
      (W64.to_uint state_offset)
      ((get8 (WArray200.init64 (fun i => state.[i]))
       (W64.to_uint state_offset)) `^`
      byte))));
      verification_key_offset <- (verification_key_offset + (W64.of_int 1));
      state_offset <- (state_offset + (W64.of_int 1));
    }
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i => state.[i]))
    (W64.to_uint state_offset)
    ((get8 (WArray200.init64 (fun i => state.[i])) (W64.to_uint state_offset)
     ) `^`
    (W8.of_int 31)))));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i => state.[i])) (136 - 1)
    ((get8 (WArray200.init64 (fun i => state.[i])) (136 - 1)) `^`
    (W8.of_int 128)))));
    state <@ _keccakf1600_ref1 (state);
    (* Erased call to unspill *)
    state_offset <- (W64.of_int 0);
    while ((state_offset \ult (W64.of_int 64))) {
      byte <-
      (get8 (WArray200.init64 (fun i => state.[i]))
      (W64.to_uint state_offset));
      hash.[(W64.to_uint state_offset)] <- byte;
      state_offset <- (state_offset + (W64.of_int 1));
    }
    return hash;
  }
  proc __shake256_consider_permute (state:W64.t Array25.t, offset:W64.t) : 
  W64.t Array25.t * W64.t = {
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    if (((W64.of_int 136) \ule offset)) {
      state <@ _keccakf1600_ref1 (state);
      ( _0,  _1,  _2,  _3,  _4, offset) <- (set0_64);
    } else {
      
    }
    return (state, offset);
  }
  proc __derive_message_representative (hash_of_verification_key:W8.t Array64.t,
                                        message:W64.t, message_size:W64.t) : 
  W8.t Array64.t = {
    var message_representative:W8.t Array64.t;
    var state:W64.t Array25.t;
    var state_offset:W64.t;
    var byte:W8.t;
    var message_offset:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    message_representative <- witness;
    state <- witness;
    state <@ __keccak_init_ref1 (state);
    state_offset <- (W64.of_int 0);
    while ((state_offset \ult (W64.of_int 64))) {
      byte <- hash_of_verification_key.[(W64.to_uint state_offset)];
      state <-
      (Array25.init
      (WArray200.get64
      (WArray200.set8 (WArray200.init64 (fun i => state.[i]))
      (W64.to_uint state_offset) byte)));
      state_offset <- (state_offset + (W64.of_int 1));
    }
    message_offset <- (W64.of_int 0);
    while ((message_offset \ult message_size)) {
      if (((W64.of_int 136) \ule state_offset)) {
        (* Erased call to spill *)
        state <@ _keccakf1600_ref1 (state);
        (* Erased call to unspill *)
        ( _0,  _1,  _2,  _3,  _4, state_offset) <- (set0_64);
      } else {
        
      }
      byte <- (loadW8 Glob.mem (W64.to_uint (message + message_offset)));
      message_offset <- (message_offset + (W64.of_int 1));
      state <-
      (Array25.init
      (WArray200.get64
      (WArray200.set8 (WArray200.init64 (fun i => state.[i]))
      (W64.to_uint state_offset)
      ((get8 (WArray200.init64 (fun i => state.[i]))
       (W64.to_uint state_offset)) `^`
      byte))));
      state_offset <- (state_offset + (W64.of_int 1));
    }
    (state, state_offset) <@ __shake256_consider_permute (state,
    state_offset);
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i => state.[i]))
    (W64.to_uint state_offset)
    ((get8 (WArray200.init64 (fun i => state.[i])) (W64.to_uint state_offset)
     ) `^`
    (W8.of_int 31)))));
    (state, state_offset) <@ __shake256_consider_permute (state,
    state_offset);
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i => state.[i])) (136 - 1)
    ((get8 (WArray200.init64 (fun i => state.[i])) (136 - 1)) `^`
    (W8.of_int 128)))));
    state <@ _keccakf1600_ref1 (state);
    state_offset <- (W64.of_int 0);
    while ((state_offset \ult (W64.of_int 64))) {
      byte <-
      (get8 (WArray200.init64 (fun i => state.[i]))
      (W64.to_uint state_offset));
      message_representative.[(W64.to_uint state_offset)] <- byte;
      state_offset <- (state_offset + (W64.of_int 1));
    }
    return message_representative;
  }
  proc __derive_commitment_hash (message_representative:W8.t Array64.t,
                                 encoded_commitment:W8.t Array768.t) : 
  W8.t Array48.t = {
    var commitment_hash:W8.t Array48.t;
    var state:W64.t Array25.t;
    var state_offset:W64.t;
    var byte:W8.t;
    var encoded_commitment_offset:W64.t;
    commitment_hash <- witness;
    state <- witness;
    state <@ __keccak_init_ref1 (state);
    state_offset <- (W64.of_int 0);
    while ((state_offset \ult (W64.of_int 64))) {
      byte <- message_representative.[(W64.to_uint state_offset)];
      state <-
      (Array25.init
      (WArray200.get64
      (WArray200.set8 (WArray200.init64 (fun i => state.[i]))
      (W64.to_uint state_offset) byte)));
      state_offset <- (state_offset + (W64.of_int 1));
    }
    encoded_commitment_offset <- (W64.of_int 0);
    while ((encoded_commitment_offset \ult
           (W64.of_int (72 + ((((((4 * 256) %/ 8) * 6) - 72) %/ 136) * 136))))) {
      while ((state_offset \ult (W64.of_int 136))) {
        byte <- encoded_commitment.[(W64.to_uint encoded_commitment_offset)];
        encoded_commitment_offset <-
        (encoded_commitment_offset + (W64.of_int 1));
        state <-
        (Array25.init
        (WArray200.get64
        (WArray200.set8 (WArray200.init64 (fun i => state.[i]))
        (W64.to_uint state_offset)
        ((get8 (WArray200.init64 (fun i => state.[i]))
         (W64.to_uint state_offset)) `^`
        byte))));
        state_offset <- (state_offset + (W64.of_int 1));
      }
      (* Erased call to spill *)
      state <@ _keccakf1600_ref1 (state);
      (* Erased call to unspill *)
      state_offset <- (W64.of_int 0);
    }
    while ((encoded_commitment_offset \ult
           (W64.of_int (((4 * 256) %/ 8) * 6)))) {
      byte <- encoded_commitment.[(W64.to_uint encoded_commitment_offset)];
      encoded_commitment_offset <-
      (encoded_commitment_offset + (W64.of_int 1));
      state <-
      (Array25.init
      (WArray200.get64
      (WArray200.set8 (WArray200.init64 (fun i => state.[i]))
      (W64.to_uint state_offset)
      ((get8 (WArray200.init64 (fun i => state.[i]))
       (W64.to_uint state_offset)) `^`
      byte))));
      state_offset <- (state_offset + (W64.of_int 1));
    }
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i => state.[i]))
    (W64.to_uint state_offset)
    ((get8 (WArray200.init64 (fun i => state.[i])) (W64.to_uint state_offset)
     ) `^`
    (W8.of_int 31)))));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i => state.[i])) (136 - 1)
    ((get8 (WArray200.init64 (fun i => state.[i])) (136 - 1)) `^`
    (W8.of_int 128)))));
    state <@ _keccakf1600_ref1 (state);
    state_offset <- (W64.of_int 0);
    while ((state_offset \ult (W64.of_int 48))) {
      byte <-
      (get8 (WArray200.init64 (fun i => state.[i]))
      (W64.to_uint state_offset));
      commitment_hash.[(W64.to_uint state_offset)] <- byte;
      state_offset <- (state_offset + (W64.of_int 1));
    }
    return commitment_hash;
  }
  proc __absorb_for_shake128 (state:W64.t Array25.t, rho:W8.t Array32.t,
                              i:int, j:int) : W64.t Array25.t = {
    var k:W64.t;
    var byte:W8.t;
    state <@ __keccak_init_ref1 (state);
    k <- (W64.of_int 0);
    while ((k \ult (W64.of_int 32))) {
      byte <- rho.[(W64.to_uint k)];
      state <-
      (Array25.init
      (WArray200.get64
      (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0]))
      (W64.to_uint k) byte)));
      k <- (k + (W64.of_int 1));
    }
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) 32
    (W8.of_int j))));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) 33
    (W8.of_int i))));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) 34
    (W8.of_int 31))));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) (168 - 1)
    (W8.of_int 128))));
    return state;
  }
  proc rejection_sample_less_than_field_modulus (result:W32.t Array256.t,
                                                 sampled:W64.t,
                                                 state:W64.t Array25.t) : 
  W32.t Array256.t * W64.t = {
    var msf:W64.t;
    var xof_offset:W64.t;
    var b:bool;
    var try_coefficient:W32.t;
    var k:int;
    var byte:W32.t;
    msf <- (init_msf);
    xof_offset <- (W64.of_int 0);
    b <- (xof_offset \ult (W64.of_int 168));
    while (b) {
      msf <- (update_msf b msf);
      b <- (sampled \ult (W64.of_int 256));
      if (b) {
        msf <- (update_msf b msf);
        try_coefficient <- (W32.of_int 0);
        k <- 0;
        while ((k < 3)) {
          byte <-
          (zeroextu32
          (get8 (WArray200.init64 (fun i => state.[i]))
          (W64.to_uint (xof_offset + (W64.of_int k)))));
          byte <- (byte `<<` (W8.of_int (8 * k)));
          try_coefficient <- (try_coefficient `|` byte);
          k <- (k + 1);
        }
        try_coefficient <- (try_coefficient `&` (W32.of_int 8388607));
        try_coefficient <- (protect_32 try_coefficient msf);
        b <- (try_coefficient \ult (W32.of_int 8380417));
        if (b) {
          msf <- (update_msf b msf);
          result.[(W64.to_uint sampled)] <- try_coefficient;
          sampled <- (sampled + (W64.of_int 1));
        } else {
          msf <- (update_msf (! b) msf);
        }
      } else {
        msf <- (update_msf (! b) msf);
      }
      xof_offset <- (xof_offset + (W64.of_int 3));
      b <- (xof_offset \ult (W64.of_int 168));
    }
    return (result, sampled);
  }
  proc __sample_polynomial (result:W32.t Array256.t, rho:W8.t Array32.t,
                            i:int, j:int) : W32.t Array256.t = {
    var state:W64.t Array25.t;
    var coefficients_sampled:W64.t;
    state <- witness;
    (* Erased call to spill *)
    state <@ __absorb_for_shake128 (state, rho, i, j);
    state <@ _keccakf1600_ref1 (state);
    (* Erased call to unspill *)
    coefficients_sampled <- (W64.of_int 0);
    (result, coefficients_sampled) <@ rejection_sample_less_than_field_modulus (
    result, coefficients_sampled, state);
    while ((coefficients_sampled \ult (W64.of_int 256))) {
      (* Erased call to spill *)
      state <@ _keccakf1600_ref1 (state);
      (* Erased call to unspill *)
      (result, coefficients_sampled) <@ rejection_sample_less_than_field_modulus (
      result, coefficients_sampled, state);
    }
    return result;
  }
  proc sample____matrix_A (rho:W8.t Array32.t) : W32.t Array7680.t = {
    var aux:W32.t Array256.t;
    var matrix_A:W32.t Array7680.t;
    var j:int;
    var i:int;
    matrix_A <- witness;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 6)) {
      j <- 0;
      while ((j < 5)) {
        (* Erased call to unspill *)
        aux <@ __sample_polynomial ((Array256.init
                                    (fun i_0 => matrix_A.[((((i * 5) + j) *
                                                           256) +
                                                          i_0)])
                                    ),
        rho, i, j);
        matrix_A <-
        (Array7680.init
        (fun i_0 => (if ((((i * 5) + j) * 256) <= i_0 < ((((i * 5) + j) *
                                                         256) +
                                                        256)) then aux.[
                                                                   (i_0 -
                                                                   ((
                                                                    (i * 5) +
                                                                    j) *
                                                                   256))] else 
                    matrix_A.[i_0]))
        );
        j <- (j + 1);
      }
      i <- (i + 1);
    }
    return matrix_A;
  }
  proc __absorb_to_generate_challenges (commitment_hash:W8.t Array48.t) : 
  W64.t Array25.t = {
    var state:W64.t Array25.t;
    var i:int;
    var byte:W8.t;
    state <- witness;
    state <@ __keccak_init_ref1 (state);
    i <- 0;
    while ((i < 48)) {
      byte <- commitment_hash.[i];
      state <-
      (Array25.init
      (WArray200.get64
      (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) i byte)));
      i <- (i + 1);
    }
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) 48
    (W8.of_int 31))));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) (136 - 1)
    (W8.of_int 128))));
    return state;
  }
  proc sample____challenge (output_challenge:W32.t Array256.t,
                            seed:W8.t Array48.t) : W32.t Array256.t = {
    var state:W64.t Array25.t;
    var signs:W64.t;
    var j:int;
    var byte:W64.t;
    var xof_offset:W64.t;
    var i:W64.t;
    var sample_at:W64.t;
    var coefficient:W32.t;
    var shift:W32.t;
    var  _0:W64.t;
    state <- witness;
    state <@ __absorb_to_generate_challenges (seed);
    (* Erased call to spill *)
    state <@ _keccakf1600_ref1 (state);
    (* Erased call to unspill *)
    signs <- (W64.of_int 0);
    j <- 0;
    while ((j < 8)) {
      byte <-
      (zeroextu64 (get8 (WArray200.init64 (fun i_0 => state.[i_0])) j));
      byte <- (byte `<<` (W8.of_int (8 * j)));
      signs <- (signs `|` byte);
      j <- (j + 1);
    }
    xof_offset <- (W64.of_int 8);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      output_challenge.[(W64.to_uint i)] <- (W32.of_int 0);
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int (256 - 49));
    while ((i \ult (W64.of_int 256))) {
      if (((W64.of_int 136) \ule xof_offset)) {
        (* Erased call to spill *)
        state <@ _keccakf1600_ref1 (state);
        (* Erased call to unspill *)
        xof_offset <- (W64.of_int 0);
      } else {
        
      }
      sample_at <-
      (zeroextu64
      (get8 (WArray200.init64 (fun i_0 => state.[i_0]))
      (W64.to_uint xof_offset)));
       _0 <- (init_msf);
      xof_offset <- (xof_offset + (W64.of_int 1));
      while ((i \ult sample_at)) {
        if (((W64.of_int 136) \ule xof_offset)) {
          (* Erased call to spill *)
          state <@ _keccakf1600_ref1 (state);
          (* Erased call to unspill *)
          xof_offset <- (W64.of_int 0);
        } else {
          
        }
        sample_at <-
        (zeroextu64
        (get8 (WArray200.init64 (fun i_0 => state.[i_0]))
        (W64.to_uint xof_offset)));
         _0 <- (init_msf);
        xof_offset <- (xof_offset + (W64.of_int 1));
      }
      coefficient <- output_challenge.[(W64.to_uint sample_at)];
      output_challenge.[(W64.to_uint i)] <- coefficient;
      shift <- (truncateu32 signs);
      shift <- (shift `&` (W32.of_int 1));
      shift <- (shift `<<` (W8.of_int 1));
      coefficient <- (W32.of_int 1);
      coefficient <- (coefficient - shift);
      output_challenge.[(W64.to_uint sample_at)] <- coefficient;
      signs <- (signs `>>` (W8.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return output_challenge;
  }
  proc __absorb_for_shake256 (rho_prime:W8.t Array64.t,
                              domain_separator:W16.t) : W64.t Array25.t = {
    var state:W64.t Array25.t;
    var v:W16.t;
    state <- witness;
    state <@ __keccak_init_ref1 (state);
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.init8
    (fun i => (if ((1 * 0) <= i < ((1 * 0) + 64)) then (WArray64.get8
                                                       (WArray64.init8
                                                       (fun i => (
                                                                 Array64.init
                                                                 (fun i => 
                                                                 (get8
                                                                 (
                                                                 WArray64.init64
                                                                 (fun i => 
                                                                 (copy_64
                                                                 (Array8.init
                                                                 (fun i => 
                                                                 (get64
                                                                 (
                                                                 WArray64.init8
                                                                 (fun i => 
                                                                 rho_prime.[
                                                                 i])) 
                                                                 i)))).[
                                                                 i])) 
                                                                 i))).[
                                                                 i])
                                                       ) (i - (1 * 0))) else 
              (WArray200.get8 (WArray200.init64 (fun i => state.[i])) 
              i)))
    )));
    v <- domain_separator;
    v <- (v `&` (W16.of_int 255));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i => state.[i])) 64 (truncateu8 v)
    )));
    v <- domain_separator;
    v <- (v `>>` (W8.of_int 8));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i => state.[i])) 65 (truncateu8 v)
    )));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i => state.[i])) 66
    ((get8 (WArray200.init64 (fun i => state.[i])) 66) `^` (W8.of_int 31)))));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i => state.[i])) (136 - 1)
    ((get8 (WArray200.init64 (fun i => state.[i])) (136 - 1)) `^`
    (W8.of_int 128)))));
    return state;
  }
  proc __sample_mask_polynomial (mask:W32.t Array256.t,
                                 rho_prime:W8.t Array64.t,
                                 domain_separator:W16.t) : W32.t Array256.t = {
    var inc:int;
    var state:W64.t Array25.t;
    var mask_encoded_offset:W64.t;
    var i:W64.t;
    var byte:W8.t;
    var mask_encoded:W8.t Array680.t;
    var block_being_squeezed:int;
    var  _0:W64.t;
    var block_being_squeezed_0:int;
    mask_encoded <- witness;
    state <- witness;
    state <@ __absorb_for_shake256 (rho_prime, domain_separator);
    mask_encoded_offset <- (W64.of_int 0);
    inc <- (((((20 * 256) %/ 8) + 136) - 1) %/ 136);
    block_being_squeezed_0 <- 0;
    while ((block_being_squeezed_0 < inc)) {
      block_being_squeezed <- block_being_squeezed_0;
      (* Erased call to spill *)
      state <@ _keccakf1600_ref1 (state);
      (* Erased call to unspill *)
       _0 <- (init_msf);
      i <- (W64.of_int 0);
      while ((i \ult (W64.of_int 136))) {
        byte <-
        (get8 (WArray200.init64 (fun i_0 => state.[i_0])) (W64.to_uint i));
        i <- (i + (W64.of_int 1));
        mask_encoded.[(W64.to_uint mask_encoded_offset)] <- byte;
        mask_encoded_offset <- (mask_encoded_offset + (W64.of_int 1));
      }
      block_being_squeezed <- (block_being_squeezed + 1);
      block_being_squeezed_0 <- (block_being_squeezed_0 + 1);
    }
    mask <@ gamma1____decode_to_polynomial (mask,
    (Array640.init (fun i_0 => mask_encoded.[(0 + i_0)])));
    return mask;
  }
  proc sample____mask (rho_prime:W8.t Array64.t, domain_separator:W16.t) : 
  W32.t Array1280.t * W16.t = {
    var aux:W32.t Array256.t;
    var mask:W32.t Array1280.t;
    var i:int;
    mask <- witness;
    i <- 0;
    while ((i < 5)) {
      aux <@ __sample_mask_polynomial ((Array256.init
                                       (fun i_0 => mask.[((256 * i) + i_0)])),
      rho_prime, domain_separator);
      mask <-
      (Array1280.init
      (fun i_0 => (if ((256 * i) <= i_0 < ((256 * i) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (256 * i))] else 
                  mask.[i_0]))
      );
      domain_separator <- (domain_separator + (W16.of_int 1));
      i <- (i + 1);
    }
    return (mask, domain_separator);
  }
  proc __montgomery_reduce (a:W64.t) : W32.t = {
    var t:W32.t;
    var a32:W32.t;
    var v64:W64.t;
    a32 <- (truncateu32 a);
    v64 <- (sigextu64 a32);
    v64 <- (v64 * (W64.of_int 58728449));
    t <- (truncateu32 v64);
    v64 <- (sigextu64 t);
    v64 <- (v64 * (W64.of_int (- 8380417)));
    v64 <- (v64 + a);
    v64 <- (v64 `>>` (W8.of_int 32));
    t <- (truncateu32 v64);
    return t;
  }
  proc coefficient____reduce32 (coefficient:W32.t) : W32.t = {
    var t:W32.t;
    var quotient:W32.t;
    t <- coefficient;
    t <- (t + (W32.of_int (1 `<<` 22)));
    t <- (t `|>>` (W8.of_int 23));
    quotient <- t;
    quotient <- (quotient * (W32.of_int 8380417));
    t <- coefficient;
    t <- (t - quotient);
    return t;
  }
  proc coefficient____conditionally_add_modulus (coefficient:W32.t) : W32.t = {
    var result:W32.t;
    var add_by:W32.t;
    add_by <- coefficient;
    add_by <- (add_by `|>>` (W8.of_int 31));
    add_by <- (add_by `&` (W32.of_int 8380417));
    result <- coefficient;
    result <- (result + add_by);
    return result;
  }
  proc polynomial____ntt_at_layer (polynomial:W32.t Array256.t, zeta_i:W64.t,
                                   lAYER:int) : W32.t Array256.t * W64.t = {
    var sTEP:int;
    var rOUNDS:int;
    var zetas:W32.t Array256.t;
    var round:W64.t;
    var offset:W64.t;
    var bound:W64.t;
    var t64:W64.t;
    var zeta_0:W64.t;
    var t:W32.t;
    var left_0:W32.t;
    zetas <- witness;
    sTEP <- (1 `<<` lAYER);
    rOUNDS <- (128 `|>>` lAYER);
    zetas <- zETAS_TIMES_MONTGOMERY_R;
    round <- (W64.of_int 0);
    while ((round \ult (W64.of_int rOUNDS))) {
      zeta_i <- (zeta_i + (W64.of_int 1));
      offset <- round;
      offset <- (offset * (W64.of_int sTEP));
      offset <- (offset * (W64.of_int 2));
      bound <- offset;
      bound <- (bound + (W64.of_int sTEP));
      while ((offset \ult bound)) {
        t64 <-
        (sigextu64 polynomial.[(W64.to_uint (offset + (W64.of_int sTEP)))]);
        zeta_0 <- (sigextu64 zetas.[(W64.to_uint zeta_i)]);
        t64 <- (t64 * zeta_0);
        t <@ __montgomery_reduce (t64);
        left_0 <- polynomial.[(W64.to_uint offset)];
        left_0 <- (left_0 - t);
        polynomial.[(W64.to_uint (offset + (W64.of_int sTEP)))] <- left_0;
        left_0 <- polynomial.[(W64.to_uint offset)];
        left_0 <- (left_0 + t);
        polynomial.[(W64.to_uint offset)] <- left_0;
        offset <- (offset + (W64.of_int 1));
      }
      round <- (round + (W64.of_int 1));
    }
    return (polynomial, zeta_i);
  }
  proc polynomial__ntt (polynomial:W32.t Array256.t) : W32.t Array256.t = {
    var inc:int;
    var zeta_i:W64.t;
    var lAYER:int;
    zeta_i <- (W64.of_int (- 1));
    inc <- (- 1);
    lAYER <- 7;
    while ((inc < lAYER)) {
      (polynomial, zeta_i) <@ polynomial____ntt_at_layer (polynomial, 
      zeta_i, lAYER);
      lAYER <- (lAYER - 1);
    }
    return polynomial;
  }
  proc polynomial____invert_ntt_at_layer (polynomial:W32.t Array256.t,
                                          zeta_i:W64.t, lAYER:int) : 
  W32.t Array256.t * W64.t = {
    var sTEP:int;
    var rOUNDS:int;
    var zetas:W32.t Array256.t;
    var round:W64.t;
    var offset:W64.t;
    var bound:W64.t;
    var t:W32.t;
    var left_0:W32.t;
    var right_0:W32.t;
    var zeta_0:W64.t;
    var t64:W64.t;
    zetas <- witness;
    sTEP <- (1 `<<` lAYER);
    rOUNDS <- (128 `|>>` lAYER);
    zetas <- zETAS_TIMES_MONTGOMERY_R;
    round <- (W64.of_int 0);
    while ((round \ult (W64.of_int rOUNDS))) {
      zeta_i <- (zeta_i - (W64.of_int 1));
      offset <- round;
      offset <- (offset * (W64.of_int sTEP));
      offset <- (offset * (W64.of_int 2));
      bound <- offset;
      bound <- (bound + (W64.of_int sTEP));
      while ((offset \ult bound)) {
        t <- polynomial.[(W64.to_uint (offset + (W64.of_int sTEP)))];
        t <- (t - polynomial.[(W64.to_uint offset)]);
        left_0 <- polynomial.[(W64.to_uint offset)];
        right_0 <- polynomial.[(W64.to_uint (offset + (W64.of_int sTEP)))];
        left_0 <- (left_0 + right_0);
        polynomial.[(W64.to_uint offset)] <- left_0;
        zeta_0 <- (sigextu64 zetas.[(W64.to_uint zeta_i)]);
        t64 <- (sigextu64 t);
        t64 <- (t64 * zeta_0);
        t <@ __montgomery_reduce (t64);
        polynomial.[(W64.to_uint (offset + (W64.of_int sTEP)))] <- t;
        offset <- (offset + (W64.of_int 1));
      }
      round <- (round + (W64.of_int 1));
    }
    return (polynomial, zeta_i);
  }
  proc polynomial__invert_ntt_montgomery (polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var zeta_i:W64.t;
    var lAYER:int;
    var j:W64.t;
    var coefficient64:W64.t;
    var coefficient:W32.t;
    zeta_i <- (W64.of_int 255);
    lAYER <- 0;
    while ((lAYER < 8)) {
      (polynomial, zeta_i) <@ polynomial____invert_ntt_at_layer (polynomial,
      zeta_i, lAYER);
      lAYER <- (lAYER + 1);
    }
    j <- (W64.of_int 0);
    while ((j \ult (W64.of_int 256))) {
      coefficient64 <- (sigextu64 polynomial.[(W64.to_uint j)]);
      coefficient64 <- (coefficient64 * (W64.of_int 41978));
      coefficient <@ __montgomery_reduce (coefficient64);
      polynomial.[(W64.to_uint j)] <- coefficient;
      j <- (j + (W64.of_int 1));
    }
    return polynomial;
  }
  proc polynomial__add (sum:W32.t Array256.t, lhs:W32.t Array256.t,
                        rhs:W32.t Array256.t) : W32.t Array256.t = {
    var i:W64.t;
    var lhs_coefficient:W32.t;
    var rhs_coefficient:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      lhs_coefficient <- lhs.[(W64.to_uint i)];
      rhs_coefficient <- rhs.[(W64.to_uint i)];
      lhs_coefficient <- (lhs_coefficient + rhs_coefficient);
      sum.[(W64.to_uint i)] <- lhs_coefficient;
      i <- (i + (W64.of_int 1));
    }
    return sum;
  }
  proc polynomial__subtract (difference:W32.t Array256.t,
                             lhs:W32.t Array256.t, rhs:W32.t Array256.t) : 
  W32.t Array256.t = {
    var i:W64.t;
    var lhs_coefficient:W32.t;
    var rhs_coefficient:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      lhs_coefficient <- lhs.[(W64.to_uint i)];
      rhs_coefficient <- rhs.[(W64.to_uint i)];
      lhs_coefficient <- (lhs_coefficient - rhs_coefficient);
      difference.[(W64.to_uint i)] <- lhs_coefficient;
      i <- (i + (W64.of_int 1));
    }
    return difference;
  }
  proc polynomial____pointwise_add_to_total (total:W32.t Array256.t,
                                             polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var i:W64.t;
    var coefficient:W32.t;
    var running_total:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      coefficient <- polynomial.[(W64.to_uint i)];
      running_total <- total.[(W64.to_uint i)];
      running_total <- (running_total + coefficient);
      total.[(W64.to_uint i)] <- running_total;
      i <- (i + (W64.of_int 1));
    }
    return total;
  }
  proc polynomial__pointwise_montgomery_product (product:W32.t Array256.t,
                                                 lhs:W32.t Array256.t,
                                                 rhs:W32.t Array256.t) : 
  W32.t Array256.t = {
    var i:W64.t;
    var lhs_coefficient:W64.t;
    var rhs_coefficient:W64.t;
    var product_reduced:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      lhs_coefficient <- (sigextu64 lhs.[(W64.to_uint i)]);
      rhs_coefficient <- (sigextu64 rhs.[(W64.to_uint i)]);
      lhs_coefficient <- (lhs_coefficient * rhs_coefficient);
      product_reduced <@ __montgomery_reduce (lhs_coefficient);
      product.[(W64.to_uint i)] <- product_reduced;
      i <- (i + (W64.of_int 1));
    }
    return product;
  }
  proc polynomial____zero (polynomial:W32.t Array256.t) : W32.t Array256.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      polynomial.[(W64.to_uint i)] <- (W32.of_int 0);
      i <- (i + (W64.of_int 1));
    }
    return polynomial;
  }
  proc polynomial__conditionally_add_modulus (polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var i:W64.t;
    var coefficient:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      coefficient <- polynomial.[(W64.to_uint i)];
      coefficient <@ coefficient____conditionally_add_modulus (coefficient);
      polynomial.[(W64.to_uint i)] <- coefficient;
      i <- (i + (W64.of_int 1));
    }
    return polynomial;
  }
  proc polynomial____check_infinity_norm (polynomial:W32.t Array256.t,
                                          threshold:int) : W8.t = {
    var result:W8.t;
    var i:W64.t;
    var coefficient:W32.t;
    var ret:W8.t;
    result <- (W8.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      coefficient <- polynomial.[(W64.to_uint i)];
      ret <@ coefficient____check_norm (coefficient, threshold);
      result <- (result `|` ret);
      i <- (i + (W64.of_int 1));
    }
    return result;
  }
  proc polynomial____make_hint (hints:W32.t Array256.t, f0:W32.t Array256.t,
                                f1:W32.t Array256.t) : W32.t Array256.t *
                                                       W32.t = {
    var weight:W32.t;
    var msf:W64.t;
    var i:W64.t;
    var condition:bool;
    var a0:W32.t;
    var a1:W32.t;
    var hint_0:W32.t;
    msf <- (init_msf);
    weight <- (W32.of_int 0);
    i <- (W64.of_int 0);
    condition <- (i \ult (W64.of_int 256));
    while (condition) {
      msf <- (update_msf condition msf);
      a0 <- f0.[(W64.to_uint i)];
      a0 <- (protect_32 a0 msf);
      a1 <- f1.[(W64.to_uint i)];
      a1 <- (protect_32 a1 msf);
      (hint_0, msf) <@ coefficient____make_hint (a0, a1, msf);
      hints.[(W64.to_uint i)] <- hint_0;
      weight <- (weight + hint_0);
      i <- (i + (W64.of_int 1));
      condition <- (i \ult (W64.of_int 256));
    }
    return (hints, weight);
  }
  proc polynomial__reduce32 (polynomial:W32.t Array256.t) : W32.t Array256.t = {
    var i:W64.t;
    var coeff:W32.t;
    var reduced:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      coeff <- polynomial.[(W64.to_uint i)];
      reduced <@ coefficient____reduce32 (coeff);
      polynomial.[(W64.to_uint i)] <- reduced;
      i <- (i + (W64.of_int 1));
    }
    return polynomial;
  }
  proc polynomial____shift_coefficients_left (polynomial:W32.t Array256.t) : 
  W32.t Array256.t = {
    var i:W64.t;
    var coefficient:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      coefficient <- polynomial.[(W64.to_uint i)];
      coefficient <- (coefficient `<<` (W8.of_int 13));
      polynomial.[(W64.to_uint i)] <- coefficient;
      i <- (i + (W64.of_int 1));
    }
    return polynomial;
  }
  proc polynomial__use_hints (commitment:W32.t Array256.t,
                              hints:W32.t Array256.t) : W32.t Array256.t = {
    var msf:W64.t;
    var i:W64.t;
    var b:bool;
    var h:W32.t;
    var a:W32.t;
    msf <- (init_msf);
    i <- (W64.of_int 0);
    b <- (i \ult (W64.of_int 256));
    while (b) {
      msf <- (update_msf b msf);
      h <- hints.[(W64.to_uint i)];
      h <- (protect_32 h msf);
      a <- commitment.[(W64.to_uint i)];
      a <- (protect_32 a msf);
      (a, msf) <@ coefficient____use_hint (a, h, msf);
      commitment.[(W64.to_uint i)] <- a;
      i <- (i + (W64.of_int 1));
      b <- (i \ult (W64.of_int 256));
    }
    return commitment;
  }
  proc row_vector__ntt (vector:W32.t Array1280.t) : W32.t Array1280.t = {
    var aux:W32.t Array256.t;
    var i:int;
    i <- 0;
    while ((i < 5)) {
      aux <@ polynomial__ntt ((Array256.init
                              (fun i_0 => vector.[((i * 256) + i_0)])));
      vector <-
      (Array1280.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  vector.[i_0]))
      );
      i <- (i + 1);
    }
    return vector;
  }
  proc row_vector__invert_ntt_montgomery (vector:W32.t Array1280.t) : 
  W32.t Array1280.t = {
    var aux:W32.t Array256.t;
    var i:int;
    i <- 0;
    while ((i < 5)) {
      aux <@ polynomial__invert_ntt_montgomery ((Array256.init
                                                (fun i_0 => vector.[(
                                                                    (
                                                                    i * 256) +
                                                                    i_0)])
                                                ));
      vector <-
      (Array1280.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  vector.[i_0]))
      );
      i <- (i + 1);
    }
    return vector;
  }
  proc row_vector____add (lhs:W32.t Array1280.t, rhs:W32.t Array1280.t) : 
  W32.t Array1280.t = {
    var aux:W32.t Array256.t;
    var sum:W32.t Array1280.t;
    var i:int;
    sum <- witness;
    i <- 0;
    while ((i < 5)) {
      aux <@ polynomial__add ((Array256.init
                              (fun i_0 => sum.[((256 * i) + i_0)])),
      (Array256.init (fun i_0 => lhs.[((256 * i) + i_0)])),
      (Array256.init (fun i_0 => rhs.[((256 * i) + i_0)])));
      sum <-
      (Array1280.init
      (fun i_0 => (if ((256 * i) <= i_0 < ((256 * i) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (256 * i))] else 
                  sum.[i_0]))
      );
      i <- (i + 1);
    }
    return sum;
  }
  proc row_vector____dot_product (output:W32.t Array256.t,
                                  lhs:W32.t Array1280.t,
                                  rhs:W32.t Array1280.t) : W32.t Array256.t = {
    var product:W32.t Array256.t;
    var i:int;
    product <- witness;
    output <@ polynomial____zero (output);
    (* Erased call to spill *)
    i <- 0;
    while ((i < 5)) {
      (* Erased call to unspill *)
      product <@ polynomial__pointwise_montgomery_product (product,
      (Array256.init (fun i_0 => lhs.[((256 * i) + i_0)])),
      (Array256.init (fun i_0 => rhs.[((256 * i) + i_0)])));
      (* Erased call to unspill *)
      output <@ polynomial____pointwise_add_to_total (output, product);
      (* Erased call to spill *)
      i <- (i + 1);
    }
    return output;
  }
  proc row_vector____multiply_by_polynomial (vector:W32.t Array1280.t,
                                             poly:W32.t Array256.t) : 
  W32.t Array1280.t = {
    var aux:W32.t Array256.t;
    var product:W32.t Array1280.t;
    var i:int;
    product <- witness;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 5)) {
      aux <@ polynomial__pointwise_montgomery_product ((Array256.init
                                                       (fun i_0 => product.[
                                                                   ((i * 256) +
                                                                   i_0)])
                                                       ),
      (Array256.init (fun i_0 => vector.[((i * 256) + i_0)])), poly);
      product <-
      (Array1280.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  product.[i_0]))
      );
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return product;
  }
  proc row_vector____multiply_with_matrix_A (matrix_A:W32.t Array7680.t,
                                             vector:W32.t Array1280.t) : 
  W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var out:W32.t Array1536.t;
    var i:int;
    out <- witness;
    i <- 0;
    while ((i < 6)) {
      aux <@ row_vector____dot_product ((Array256.init
                                        (fun i_0 => out.[((256 * i) + i_0)])),
      (Array1280.init (fun i_0 => matrix_A.[(((5 * 256) * i) + i_0)])),
      vector);
      out <-
      (Array1536.init
      (fun i_0 => (if ((256 * i) <= i_0 < ((256 * i) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (256 * i))] else 
                  out.[i_0]))
      );
      i <- (i + 1);
    }
    return out;
  }
  proc row_vector__reduce32 (vector:W32.t Array1280.t) : W32.t Array1280.t = {
    var aux:W32.t Array256.t;
    var i:int;
    i <- 0;
    while ((i < 5)) {
      aux <@ polynomial__reduce32 ((Array256.init
                                   (fun i_0 => vector.[((i * 256) + i_0)])));
      vector <-
      (Array1280.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  vector.[i_0]))
      );
      i <- (i + 1);
    }
    return vector;
  }
  proc row_vector____check_infinity_norm (vector:W32.t Array1280.t,
                                          threshold:int) : W8.t = {
    var result:W8.t;
    var i:int;
    var vector_element:W32.t Array256.t;
    var ret:W8.t;
    vector_element <- witness;
    result <- (W8.of_int 0);
    i <- 0;
    while ((i < 5)) {
      vector_element <-
      (Array256.init (fun i_0 => vector.[((i * 256) + i_0)]));
      ret <@ polynomial____check_infinity_norm (vector_element, threshold);
      result <- (result `|` ret);
      i <- (i + 1);
    }
    return result;
  }
  proc column_vector__reduce32 (vector:W32.t Array1536.t) : W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var i:int;
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__reduce32 ((Array256.init
                                   (fun i_0 => vector.[((i * 256) + i_0)])));
      vector <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  vector.[i_0]))
      );
      i <- (i + 1);
    }
    return vector;
  }
  proc column_vector__ntt (vector:W32.t Array1536.t) : W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var i:int;
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__ntt ((Array256.init
                              (fun i_0 => vector.[((i * 256) + i_0)])));
      vector <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  vector.[i_0]))
      );
      i <- (i + 1);
    }
    return vector;
  }
  proc column_vector__invert_ntt_montgomery (vector:W32.t Array1536.t) : 
  W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var i:int;
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__invert_ntt_montgomery ((Array256.init
                                                (fun i_0 => vector.[(
                                                                    (
                                                                    i * 256) +
                                                                    i_0)])
                                                ));
      vector <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  vector.[i_0]))
      );
      i <- (i + 1);
    }
    return vector;
  }
  proc column_vector____power2round (v:W32.t Array1536.t) : W32.t Array1536.t *
                                                            W32.t Array1536.t = {
    var t1:W32.t Array1536.t;
    var t0:W32.t Array1536.t;
    var i:W64.t;
    var x:W32.t;
    var y1:W32.t;
    var y2:W32.t;
    t0 <- witness;
    t1 <- witness;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (6 * 256)))) {
      x <- v.[(W64.to_uint i)];
      (* Erased call to spill *)
      (y1, y2) <@ coefficient____power2round (x);
      (* Erased call to unspill *)
      t1.[(W64.to_uint i)] <- y1;
      t0.[(W64.to_uint i)] <- y2;
      i <- (i + (W64.of_int 1));
    }
    return (t1, t0);
  }
  proc column_vector____add (lhs:W32.t Array1536.t, rhs:W32.t Array1536.t) : 
  W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var sum:W32.t Array1536.t;
    var i:int;
    sum <- witness;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__add ((Array256.init
                              (fun i_0 => sum.[((256 * i) + i_0)])),
      (Array256.init (fun i_0 => lhs.[((256 * i) + i_0)])),
      (Array256.init (fun i_0 => rhs.[((256 * i) + i_0)])));
      sum <-
      (Array1536.init
      (fun i_0 => (if ((256 * i) <= i_0 < ((256 * i) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (256 * i))] else 
                  sum.[i_0]))
      );
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return sum;
  }
  proc column_vector____conditionally_add_modulus (vector:W32.t Array1536.t) : 
  W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var i:int;
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__conditionally_add_modulus ((Array256.init
                                                    (fun i_0 => vector.[
                                                                ((i * 256) +
                                                                i_0)])
                                                    ));
      vector <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  vector.[i_0]))
      );
      i <- (i + 1);
    }
    return vector;
  }
  proc column_vector____decompose (vector:W32.t Array1536.t) : W32.t Array1536.t *
                                                               W32.t Array1536.t = {
    var low:W32.t Array1536.t;
    var high:W32.t Array1536.t;
    var i:W64.t;
    var coefficient:W32.t;
    var low_bits:W32.t;
    var high_bits:W32.t;
    high <- witness;
    low <- witness;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (6 * 256)))) {
      coefficient <- vector.[(W64.to_uint i)];
      (low_bits, high_bits) <@ coefficient____decompose (coefficient);
      low.[(W64.to_uint i)] <- low_bits;
      high.[(W64.to_uint i)] <- high_bits;
      i <- (i + (W64.of_int 1));
    }
    return (low, high);
  }
  proc column_vector____multiply_by_polynomial (vector:W32.t Array1536.t,
                                                poly:W32.t Array256.t) : 
  W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var product:W32.t Array1536.t;
    var i:int;
    product <- witness;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__pointwise_montgomery_product ((Array256.init
                                                       (fun i_0 => product.[
                                                                   ((i * 256) +
                                                                   i_0)])
                                                       ),
      (Array256.init (fun i_0 => vector.[((i * 256) + i_0)])), poly);
      product <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  product.[i_0]))
      );
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return product;
  }
  proc column_vector____subtract (lhs:W32.t Array1536.t,
                                  rhs:W32.t Array1536.t) : W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var difference:W32.t Array1536.t;
    var i:int;
    difference <- witness;
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__subtract ((Array256.init
                                   (fun i_0 => difference.[((256 * i) + i_0)])
                                   ),
      (Array256.init (fun i_0 => lhs.[((256 * i) + i_0)])),
      (Array256.init (fun i_0 => rhs.[((256 * i) + i_0)])));
      difference <-
      (Array1536.init
      (fun i_0 => (if ((256 * i) <= i_0 < ((256 * i) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (256 * i))] else 
                  difference.[i_0]))
      );
      i <- (i + 1);
    }
    return difference;
  }
  proc column_vector____check_infinity_norm (vector:W32.t Array1536.t,
                                             threshold:int) : W8.t = {
    var result:W8.t;
    var i:int;
    var ret:W8.t;
    result <- (W8.of_int 0);
    i <- 0;
    while ((i < 6)) {
      ret <@ polynomial____check_infinity_norm ((Array256.init
                                                (fun i_0 => vector.[(
                                                                    (
                                                                    i * 256) +
                                                                    i_0)])
                                                ),
      threshold);
      result <- (result `|` ret);
      i <- (i + 1);
    }
    return result;
  }
  proc column_vector____make_hint (addend:W32.t Array1536.t,
                                   original:W32.t Array1536.t) : W32.t Array1536.t *
                                                                 W32.t = {
    var aux_0:W32.t;
    var aux:W32.t Array256.t;
    var hint_vector:W32.t Array1536.t;
    var ones_in_hint_vector:W32.t;
    var i:int;
    var ones_in_hint:W32.t;
    hint_vector <- witness;
    ones_in_hint_vector <- (W32.of_int 0);
    i <- 0;
    while ((i < 6)) {
      (aux, aux_0) <@ polynomial____make_hint ((Array256.init
                                               (fun i_0 => hint_vector.[
                                                           ((i * 256) + 
                                                           i_0)])
                                               ),
      (Array256.init (fun i_0 => addend.[((i * 256) + i_0)])),
      (Array256.init (fun i_0 => original.[((i * 256) + i_0)])));
      hint_vector <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  hint_vector.[i_0]))
      );
      ones_in_hint <- aux_0;
      ones_in_hint_vector <- (ones_in_hint_vector + ones_in_hint);
      i <- (i + 1);
    }
    return (hint_vector, ones_in_hint_vector);
  }
  proc t0__change_t0_interval (coefficient:W32.t) : W32.t = {
    
    coefficient <- (- coefficient);
    coefficient <- (coefficient + (W32.of_int ((1 `<<` 13) %/ 2)));
    return coefficient;
  }
  proc t0__encode_polynomial (encoded:W8.t Array416.t, t0:W32.t Array256.t) : 
  W8.t Array416.t = {
    var encoded_offset:W64.t;
    var t0_offset:W64.t;
    var i:W64.t;
    var coefficient:W32.t;
    var t:W32.t Array8.t;
    var c:W8.t;
    var c1:W8.t;
    t <- witness;
    encoded_offset <- (W64.of_int 0);
    t0_offset <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (256 %/ 8)))) {
      coefficient <- t0.[(W64.to_uint t0_offset)];
      t0_offset <- (t0_offset + (W64.of_int 1));
      coefficient <@ t0__change_t0_interval (coefficient);
      t.[0] <- coefficient;
      c <- (truncateu8 coefficient);
      encoded.[(W64.to_uint encoded_offset)] <- c;
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- t.[0];
      coefficient <- (coefficient `>>` (W8.of_int 8));
      c <- (truncateu8 coefficient);
      coefficient <- t0.[(W64.to_uint t0_offset)];
      t0_offset <- (t0_offset + (W64.of_int 1));
      coefficient <@ t0__change_t0_interval (coefficient);
      t.[1] <- coefficient;
      coefficient <- (coefficient `<<` (W8.of_int 5));
      c1 <- (truncateu8 coefficient);
      c <- (c `|` c1);
      encoded.[(W64.to_uint encoded_offset)] <- c;
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- t.[1];
      coefficient <- (coefficient `>>` (W8.of_int 3));
      c <- (truncateu8 coefficient);
      encoded.[(W64.to_uint encoded_offset)] <- c;
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- t.[1];
      coefficient <- (coefficient `>>` (W8.of_int 11));
      c <- (truncateu8 coefficient);
      coefficient <- t0.[(W64.to_uint t0_offset)];
      t0_offset <- (t0_offset + (W64.of_int 1));
      coefficient <@ t0__change_t0_interval (coefficient);
      t.[2] <- coefficient;
      coefficient <- (coefficient `<<` (W8.of_int 2));
      c1 <- (truncateu8 coefficient);
      c <- (c `|` c1);
      encoded.[(W64.to_uint encoded_offset)] <- c;
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- t.[2];
      coefficient <- (coefficient `>>` (W8.of_int 6));
      c <- (truncateu8 coefficient);
      coefficient <- t0.[(W64.to_uint t0_offset)];
      t0_offset <- (t0_offset + (W64.of_int 1));
      coefficient <@ t0__change_t0_interval (coefficient);
      t.[3] <- coefficient;
      coefficient <- (coefficient `<<` (W8.of_int 7));
      c1 <- (truncateu8 coefficient);
      c <- (c `|` c1);
      encoded.[(W64.to_uint encoded_offset)] <- c;
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- t.[3];
      coefficient <- (coefficient `>>` (W8.of_int 1));
      c <- (truncateu8 coefficient);
      encoded.[(W64.to_uint encoded_offset)] <- c;
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- t.[3];
      coefficient <- (coefficient `>>` (W8.of_int 9));
      c <- (truncateu8 coefficient);
      coefficient <- t0.[(W64.to_uint t0_offset)];
      t0_offset <- (t0_offset + (W64.of_int 1));
      coefficient <@ t0__change_t0_interval (coefficient);
      t.[4] <- coefficient;
      coefficient <- (coefficient `<<` (W8.of_int 4));
      c1 <- (truncateu8 coefficient);
      c <- (c `|` c1);
      encoded.[(W64.to_uint encoded_offset)] <- c;
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- t.[4];
      coefficient <- (coefficient `>>` (W8.of_int 4));
      c <- (truncateu8 coefficient);
      encoded.[(W64.to_uint encoded_offset)] <- c;
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- t.[4];
      coefficient <- (coefficient `>>` (W8.of_int 12));
      c <- (truncateu8 coefficient);
      coefficient <- t0.[(W64.to_uint t0_offset)];
      t0_offset <- (t0_offset + (W64.of_int 1));
      coefficient <@ t0__change_t0_interval (coefficient);
      t.[5] <- coefficient;
      coefficient <- (coefficient `<<` (W8.of_int 1));
      c1 <- (truncateu8 coefficient);
      c <- (c `|` c1);
      encoded.[(W64.to_uint encoded_offset)] <- c;
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- t.[5];
      coefficient <- (coefficient `>>` (W8.of_int 7));
      c <- (truncateu8 coefficient);
      coefficient <- t0.[(W64.to_uint t0_offset)];
      t0_offset <- (t0_offset + (W64.of_int 1));
      coefficient <@ t0__change_t0_interval (coefficient);
      t.[6] <- coefficient;
      coefficient <- (coefficient `<<` (W8.of_int 6));
      c1 <- (truncateu8 coefficient);
      c <- (c `|` c1);
      encoded.[(W64.to_uint encoded_offset)] <- c;
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- t.[6];
      coefficient <- (coefficient `>>` (W8.of_int 2));
      c <- (truncateu8 coefficient);
      encoded.[(W64.to_uint encoded_offset)] <- c;
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- t.[6];
      coefficient <- (coefficient `>>` (W8.of_int 10));
      c <- (truncateu8 coefficient);
      coefficient <- t0.[(W64.to_uint t0_offset)];
      t0_offset <- (t0_offset + (W64.of_int 1));
      coefficient <@ t0__change_t0_interval (coefficient);
      t.[7] <- coefficient;
      coefficient <- (coefficient `<<` (W8.of_int 3));
      c1 <- (truncateu8 coefficient);
      c <- (c `|` c1);
      encoded.[(W64.to_uint encoded_offset)] <- c;
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- t.[7];
      coefficient <- (coefficient `>>` (W8.of_int 5));
      c <- (truncateu8 coefficient);
      encoded.[(W64.to_uint encoded_offset)] <- c;
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return encoded;
  }
  proc t0____encode (encoded:W8.t Array2496.t, t0:W32.t Array1536.t) : 
  W8.t Array2496.t = {
    var aux:W8.t Array416.t;
    var j:int;
    (* Erased call to spill *)
    j <- 0;
    while ((j < 6)) {
      aux <@ t0__encode_polynomial ((Array416.init
                                    (fun i => encoded.[((j *
                                                        ((13 * 256) %/ 8)) +
                                                       i)])
                                    ),
      (Array256.init (fun i => t0.[((256 * j) + i)])));
      encoded <-
      (Array2496.init
      (fun i => (if ((j * ((13 * 256) %/ 8)) <= i < ((j * ((13 * 256) %/ 8)) +
                                                    416)) then aux.[(
                                                                    i -
                                                                    (
                                                                    j *
                                                                    (
                                                                    (13 *
                                                                    256) %/
                                                                    8)))] else 
                encoded.[i]))
      );
      (* Erased call to unspill *)
      j <- (j + 1);
    }
    return encoded;
  }
  proc t0____decode_polynomial (t0:W32.t Array256.t, src:W8.t Array416.t) : 
  W32.t Array256.t = {
    var output_offset:W64.t;
    var i:W64.t;
    var input_offset:W64.t;
    var coefficient:W32.t;
    var encoded_byte:W32.t;
    output_offset <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (256 %/ 8)))) {
      input_offset <- i;
      input_offset <- (input_offset * (W64.of_int 13));
      coefficient <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      encoded_byte <- (encoded_byte `<<` (W8.of_int 8));
      coefficient <- (coefficient `|` encoded_byte);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 13) - 1)));
      coefficient <@ t0__change_t0_interval (coefficient);
      t0.[(W64.to_uint output_offset)] <- coefficient;
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      coefficient <- (coefficient `>>` (W8.of_int 5));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      encoded_byte <- (encoded_byte `<<` (W8.of_int 3));
      coefficient <- (coefficient `|` encoded_byte);
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      encoded_byte <- (encoded_byte `<<` (W8.of_int 11));
      coefficient <- (coefficient `|` encoded_byte);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 13) - 1)));
      coefficient <@ t0__change_t0_interval (coefficient);
      t0.[(W64.to_uint output_offset)] <- coefficient;
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      coefficient <- (coefficient `>>` (W8.of_int 2));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      encoded_byte <- (encoded_byte `<<` (W8.of_int 6));
      coefficient <- (coefficient `|` encoded_byte);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 13) - 1)));
      coefficient <@ t0__change_t0_interval (coefficient);
      t0.[(W64.to_uint output_offset)] <- coefficient;
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      coefficient <- (coefficient `>>` (W8.of_int 7));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      encoded_byte <- (encoded_byte `<<` (W8.of_int 1));
      coefficient <- (coefficient `|` encoded_byte);
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      encoded_byte <- (encoded_byte `<<` (W8.of_int 9));
      coefficient <- (coefficient `|` encoded_byte);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 13) - 1)));
      coefficient <@ t0__change_t0_interval (coefficient);
      t0.[(W64.to_uint output_offset)] <- coefficient;
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      coefficient <- (coefficient `>>` (W8.of_int 4));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      encoded_byte <- (encoded_byte `<<` (W8.of_int 4));
      coefficient <- (coefficient `|` encoded_byte);
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      encoded_byte <- (encoded_byte `<<` (W8.of_int 12));
      coefficient <- (coefficient `|` encoded_byte);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 13) - 1)));
      coefficient <@ t0__change_t0_interval (coefficient);
      t0.[(W64.to_uint output_offset)] <- coefficient;
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      coefficient <- (coefficient `>>` (W8.of_int 1));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      encoded_byte <- (encoded_byte `<<` (W8.of_int 7));
      coefficient <- (coefficient `|` encoded_byte);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 13) - 1)));
      coefficient <@ t0__change_t0_interval (coefficient);
      t0.[(W64.to_uint output_offset)] <- coefficient;
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      coefficient <- (coefficient `>>` (W8.of_int 6));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      encoded_byte <- (encoded_byte `<<` (W8.of_int 2));
      coefficient <- (coefficient `|` encoded_byte);
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      encoded_byte <- (encoded_byte `<<` (W8.of_int 10));
      coefficient <- (coefficient `|` encoded_byte);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 13) - 1)));
      coefficient <@ t0__change_t0_interval (coefficient);
      t0.[(W64.to_uint output_offset)] <- coefficient;
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      coefficient <- (coefficient `>>` (W8.of_int 3));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- (zeroextu32 src.[(W64.to_uint input_offset)]);
      encoded_byte <- (encoded_byte `<<` (W8.of_int 5));
      coefficient <- (coefficient `|` encoded_byte);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 13) - 1)));
      coefficient <@ t0__change_t0_interval (coefficient);
      t0.[(W64.to_uint output_offset)] <- coefficient;
      output_offset <- (output_offset + (W64.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return t0;
  }
  proc t0____decode (t0:W32.t Array1536.t, encoded:W8.t Array2496.t) : 
  W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var i:int;
    i <- 0;
    while ((i < 6)) {
      aux <@ t0____decode_polynomial ((Array256.init
                                      (fun i_0 => t0.[((i * 256) + i_0)])),
      (Array416.init (fun i_0 => encoded.[((((13 * 256) %/ 8) * i) + i_0)])));
      t0 <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  t0.[i_0]))
      );
      i <- (i + 1);
    }
    return t0;
  }
  proc t1__encode_polynomial (encoded:W8.t Array320.t, t1:W32.t Array256.t) : 
  W8.t Array320.t = {
    var input_offset:W64.t;
    var output_offset:W64.t;
    var i:W64.t;
    var encoded_bytes:W32.t;
    var encoded_byte:W32.t;
    input_offset <- (W64.of_int 0);
    output_offset <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (256 %/ 4)))) {
      encoded_bytes <- t1.[(W64.to_uint input_offset)];
      encoded.[(W64.to_uint output_offset)] <- (truncateu8 encoded_bytes);
      output_offset <- (output_offset + (W64.of_int 1));
      encoded_bytes <- t1.[(W64.to_uint input_offset)];
      encoded_bytes <- (encoded_bytes `>>` (W8.of_int 8));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- t1.[(W64.to_uint input_offset)];
      encoded_byte <- (encoded_byte `<<` (W8.of_int 2));
      encoded_bytes <- (encoded_bytes `|` encoded_byte);
      encoded.[(W64.to_uint output_offset)] <- (truncateu8 encoded_bytes);
      output_offset <- (output_offset + (W64.of_int 1));
      encoded_bytes <- t1.[(W64.to_uint input_offset)];
      encoded_bytes <- (encoded_bytes `>>` (W8.of_int 6));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- t1.[(W64.to_uint input_offset)];
      encoded_byte <- (encoded_byte `<<` (W8.of_int 4));
      encoded_bytes <- (encoded_bytes `|` encoded_byte);
      encoded.[(W64.to_uint output_offset)] <- (truncateu8 encoded_bytes);
      output_offset <- (output_offset + (W64.of_int 1));
      encoded_bytes <- t1.[(W64.to_uint input_offset)];
      encoded_bytes <- (encoded_bytes `>>` (W8.of_int 4));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- t1.[(W64.to_uint input_offset)];
      encoded_byte <- (encoded_byte `<<` (W8.of_int 6));
      encoded_bytes <- (encoded_bytes `|` encoded_byte);
      encoded.[(W64.to_uint output_offset)] <- (truncateu8 encoded_bytes);
      output_offset <- (output_offset + (W64.of_int 1));
      encoded_bytes <- t1.[(W64.to_uint input_offset)];
      encoded_bytes <- (encoded_bytes `>>` (W8.of_int 2));
      encoded.[(W64.to_uint output_offset)] <- (truncateu8 encoded_bytes);
      output_offset <- (output_offset + (W64.of_int 1));
      input_offset <- (input_offset + (W64.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return encoded;
  }
  proc t1____encode (encoded:W8.t Array1920.t, t1:W32.t Array1536.t) : 
  W8.t Array1920.t = {
    var aux:W8.t Array320.t;
    var j:int;
    (* Erased call to spill *)
    j <- 0;
    while ((j < 6)) {
      aux <@ t1__encode_polynomial ((Array320.init
                                    (fun i => encoded.[((j *
                                                        (((23 - 13) * 256) %/
                                                        8)) +
                                                       i)])
                                    ),
      (Array256.init (fun i => t1.[((256 * j) + i)])));
      encoded <-
      (Array1920.init
      (fun i => (if ((j * (((23 - 13) * 256) %/ 8)) <= i < ((j *
                                                            (((23 - 13) *
                                                             256) %/
                                                            8)) +
                                                           320)) then 
                aux.[(i - (j * (((23 - 13) * 256) %/ 8)))] else encoded.[i]))
      );
      (* Erased call to unspill *)
      j <- (j + 1);
    }
    return encoded;
  }
  proc t1__decode_polynomial (t1:W32.t Array256.t, encoded:W8.t Array320.t) : 
  W32.t Array256.t = {
    var input_offset:W64.t;
    var output_offset:W64.t;
    var i:W64.t;
    var coefficient:W32.t;
    var temp1:W32.t;
    var temp2:W32.t;
    input_offset <- (W64.of_int 0);
    output_offset <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (256 %/ 4)))) {
      coefficient <- (zeroextu32 encoded.[(W64.to_uint input_offset)]);
      input_offset <- (input_offset + (W64.of_int 1));
      temp1 <- (zeroextu32 encoded.[(W64.to_uint input_offset)]);
      input_offset <- (input_offset + (W64.of_int 1));
      temp2 <- temp1;
      temp1 <- (temp1 `<<` (W8.of_int 8));
      coefficient <- (coefficient `|` temp1);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 10) - 1)));
      t1.[(W64.to_uint output_offset)] <- coefficient;
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <- (temp2 `>>` (W8.of_int 2));
      temp1 <- (zeroextu32 encoded.[(W64.to_uint input_offset)]);
      input_offset <- (input_offset + (W64.of_int 1));
      temp2 <- temp1;
      temp1 <- (temp1 `<<` (W8.of_int 6));
      coefficient <- (coefficient `|` temp1);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 10) - 1)));
      t1.[(W64.to_uint output_offset)] <- coefficient;
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <- (temp2 `>>` (W8.of_int 4));
      temp1 <- (zeroextu32 encoded.[(W64.to_uint input_offset)]);
      input_offset <- (input_offset + (W64.of_int 1));
      temp2 <- temp1;
      temp1 <- (temp1 `<<` (W8.of_int 4));
      coefficient <- (coefficient `|` temp1);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 10) - 1)));
      t1.[(W64.to_uint output_offset)] <- coefficient;
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <- (temp2 `>>` (W8.of_int 6));
      temp1 <- (zeroextu32 encoded.[(W64.to_uint input_offset)]);
      input_offset <- (input_offset + (W64.of_int 1));
      temp1 <- (temp1 `<<` (W8.of_int 2));
      coefficient <- (coefficient `|` temp1);
      t1.[(W64.to_uint output_offset)] <- coefficient;
      output_offset <- (output_offset + (W64.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return t1;
  }
  proc signature____encode (signature:W8.t Array3309.t,
                            commitment_hash:W8.t Array48.t,
                            signer_response:W32.t Array1280.t,
                            hint_0:W32.t Array1536.t) : W8.t Array3309.t = {
    var i:W64.t;
    var k:int;
    var polynomial_encoded:W8.t Array640.t;
    var polynomial:W32.t Array256.t;
    var msf:W64.t;
    var hints_written:W64.t;
    var condition:bool;
    var j:W64.t;
    var hint_offset:W64.t;
    var hint_coefficient:W32.t;
    polynomial <- witness;
    polynomial_encoded <- witness;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 48))) {
      signature.[(W64.to_uint i)] <- commitment_hash.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
    }
    k <- 0;
    while ((k < 5)) {
      polynomial_encoded <-
      (Array640.init
      (fun i_0 => signature.[((48 + (k * ((20 * 256) %/ 8))) + i_0)]));
      polynomial <-
      (Array256.init (fun i_0 => signer_response.[((k * 256) + i_0)]));
      polynomial_encoded <@ gamma1____encode_polynomial (polynomial_encoded,
      polynomial);
      signature <-
      (Array3309.init
      (fun i_0 => (if ((48 + (k * ((20 * 256) %/ 8))) <= i_0 < ((48 +
                                                                (k *
                                                                ((20 * 256) %/
                                                                8))) +
                                                               640)) then 
                  polynomial_encoded.[(i_0 - (48 + (k * ((20 * 256) %/ 8))))] else 
                  signature.[i_0]))
      );
      k <- (k + 1);
    }
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (55 + 6)))) {
      signature.[(W64.to_uint
                 ((W64.of_int (48 + (5 * ((20 * 256) %/ 8)))) + i))] <-
      (W8.of_int 0);
      i <- (i + (W64.of_int 1));
    }
    msf <- (init_msf);
    hints_written <- (W64.of_int 0);
    i <- (W64.of_int 0);
    condition <- (i \ult (W64.of_int 6));
    while (condition) {
      msf <- (update_msf condition msf);
      j <- (W64.of_int 0);
      condition <- (j \ult (W64.of_int 256));
      while (condition) {
        msf <- (update_msf condition msf);
        hint_offset <- i;
        hint_offset <- (hint_offset `<<` (W8.of_int 8));
        hint_offset <- (hint_offset + j);
        hint_coefficient <- hint_0.[(W64.to_uint hint_offset)];
        hint_coefficient <- (protect_32 hint_coefficient msf);
        condition <- (hint_coefficient <> (W32.of_int 0));
        if (condition) {
          msf <- (update_msf condition msf);
          signature.[(W64.to_uint
                     ((W64.of_int (48 + (5 * ((20 * 256) %/ 8)))) +
                     hints_written))] <-
          (truncateu8 j);
          hints_written <- (hints_written + (W64.of_int 1));
        } else {
          msf <- (update_msf (! condition) msf);
        }
        j <- (j + (W64.of_int 1));
        condition <- (j \ult (W64.of_int 256));
      }
      msf <- (update_msf (! condition) msf);
      signature.[(W64.to_uint
                 ((W64.of_int ((48 + (5 * ((20 * 256) %/ 8))) + 55)) + i))] <-
      (truncateu8 hints_written);
      i <- (i + (W64.of_int 1));
      condition <- (i \ult (W64.of_int 6));
    }
    return signature;
  }
  proc signature____decode_hint (hints:W32.t Array1536.t,
                                 hint_encoded:W8.t Array61.t) : W32.t Array1536.t *
                                                                W64.t = {
    var ill_formed_hint:W64.t;
    var previous_true_hints_seen:W64.t;
    var encoded_offset:W64.t;
    var decoded_offset:W64.t;
    var j:W64.t;
    var index:W64.t;
    var current_true_hints_seen:W64.t;
    var hint_at_j:W64.t;
    var hint_at_j_minus_one:W64.t;
    var done_0:W8.t;
    var within_bounds:bool;
    var hint_0:W64.t;
    var  _0:W64.t;
    var  _1:W64.t;
    var  _2:W64.t;
    var  _3:W64.t;
    ill_formed_hint <- (W64.of_int 0);
    previous_true_hints_seen <- (W64.of_int 0);
    encoded_offset <- (W64.of_int 0);
    within_bounds <- ((W64.of_int 6) \ule encoded_offset);
    done_0 <- (SETcc within_bounds);
    done_0 <- (done_0 `|` (truncateu8 ill_formed_hint));
    while ((done_0 = (W8.of_int 0))) {
      decoded_offset <- encoded_offset;
      decoded_offset <- (decoded_offset `<<` (W8.of_int 8));
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int 256))) {
        index <- (LEA_64 (decoded_offset + j));
        hints.[(W64.to_uint index)] <- (W32.of_int 0);
        j <- (j + (W64.of_int 1));
      }
      current_true_hints_seen <-
      (zeroextu64
      hint_encoded.[(W64.to_uint ((W64.of_int 55) + encoded_offset))]);
       _0 <- (init_msf);
      if ((current_true_hints_seen \ult previous_true_hints_seen)) {
        ill_formed_hint <- (W64.of_int 1);
      } else {
        if (((W64.of_int 55) \ult previous_true_hints_seen)) {
          ill_formed_hint <- (W64.of_int 1);
        } else {
          j <- previous_true_hints_seen;
          within_bounds <- (current_true_hints_seen \ule j);
          done_0 <- (SETcc within_bounds);
          done_0 <- (done_0 `|` (truncateu8 ill_formed_hint));
          while ((done_0 = (W8.of_int 0))) {
            hint_at_j <- (zeroextu64 hint_encoded.[(W64.to_uint j)]);
             _1 <- (init_msf);
            if ((previous_true_hints_seen \ult j)) {
              hint_at_j_minus_one <-
              (zeroextu64 hint_encoded.[(W64.to_uint (j - (W64.of_int 1)))]);
               _2 <- (init_msf);
              if ((hint_at_j \ule hint_at_j_minus_one)) {
                ill_formed_hint <- (W64.of_int 1);
              } else {
                
              }
            } else {
              
            }
            if ((ill_formed_hint = (W64.of_int 0))) {
              index <- (LEA_64 (decoded_offset + hint_at_j));
              hints.[(W64.to_uint index)] <- (W32.of_int 1);
              j <- (j + (W64.of_int 1));
            } else {
              
            }
            within_bounds <- (current_true_hints_seen \ule j);
            done_0 <- (SETcc within_bounds);
            done_0 <- (done_0 `|` (truncateu8 ill_formed_hint));
          }
        }
      }
      if ((ill_formed_hint = (W64.of_int 0))) {
        previous_true_hints_seen <- current_true_hints_seen;
        encoded_offset <- (encoded_offset + (W64.of_int 1));
      } else {
        
      }
      within_bounds <- ((W64.of_int 6) \ule encoded_offset);
      done_0 <- (SETcc within_bounds);
      done_0 <- (done_0 `|` (truncateu8 ill_formed_hint));
    }
    encoded_offset <- previous_true_hints_seen;
    within_bounds <- ((W64.of_int 55) \ule encoded_offset);
    done_0 <- (SETcc within_bounds);
    done_0 <- (done_0 `|` (truncateu8 ill_formed_hint));
    while ((done_0 = (W8.of_int 0))) {
      hint_0 <- (zeroextu64 hint_encoded.[(W64.to_uint encoded_offset)]);
       _3 <- (init_msf);
      if ((hint_0 <> (W64.of_int 0))) {
        ill_formed_hint <- (W64.of_int 1);
      } else {
        
      }
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      within_bounds <- ((W64.of_int 55) \ule encoded_offset);
      done_0 <- (SETcc within_bounds);
      done_0 <- (done_0 `|` (truncateu8 ill_formed_hint));
    }
    ill_formed_hint <- (- ill_formed_hint);
    return (hints, ill_formed_hint);
  }
  proc s1____encode (encoded:W8.t Array640.t, s1:W32.t Array1280.t) : 
  W8.t Array640.t = {
    var aux:W8.t Array128.t;
    var i:int;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 5)) {
      aux <@ error_polynomial__encode ((Array128.init
                                       (fun i_0 => encoded.[((128 * i) + i_0)])
                                       ),
      (Array256.init (fun i_0 => s1.[((256 * i) + i_0)])));
      encoded <-
      (Array640.init
      (fun i_0 => (if ((128 * i) <= i_0 < ((128 * i) + 128)) then aux.[
                                                                  (i_0 -
                                                                  (128 * i))] else 
                  encoded.[i_0]))
      );
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return encoded;
  }
  proc s1____decode (s1:W32.t Array1280.t, encoded:W8.t Array640.t) : 
  W32.t Array1280.t = {
    var aux:W32.t Array256.t;
    var i:int;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 5)) {
      aux <@ error_polynomial__decode ((Array256.init
                                       (fun i_0 => s1.[((i * 256) + i_0)])),
      (Array128.init (fun i_0 => encoded.[((128 * i) + i_0)])));
      s1 <-
      (Array1280.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  s1.[i_0]))
      );
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return s1;
  }
  proc s2____encode (encoded:W8.t Array768.t, s2:W32.t Array1536.t) : 
  W8.t Array768.t = {
    var aux:W8.t Array128.t;
    var i:int;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 6)) {
      aux <@ error_polynomial__encode ((Array128.init
                                       (fun i_0 => encoded.[((128 * i) + i_0)])
                                       ),
      (Array256.init (fun i_0 => s2.[((256 * i) + i_0)])));
      encoded <-
      (Array768.init
      (fun i_0 => (if ((128 * i) <= i_0 < ((128 * i) + 128)) then aux.[
                                                                  (i_0 -
                                                                  (128 * i))] else 
                  encoded.[i_0]))
      );
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return encoded;
  }
  proc s2____decode (s2:W32.t Array1536.t, encoded:W8.t Array768.t) : 
  W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var i:int;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 6)) {
      aux <@ error_polynomial__decode ((Array256.init
                                       (fun i_0 => s2.[((i * 256) + i_0)])),
      (Array128.init (fun i_0 => encoded.[((128 * i) + i_0)])));
      s2 <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  s2.[i_0]))
      );
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return s2;
  }
  proc __absorb_to_generate_errors (rho_prime:W8.t Array64.t, index:W16.t) : 
  W64.t Array25.t = {
    var state:W64.t Array25.t;
    var i:W64.t;
    var byte:W8.t;
    state <- witness;
    state <@ __keccak_init_ref1 (state);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 64))) {
      byte <- rho_prime.[(W64.to_uint i)];
      state <-
      (Array25.init
      (WArray200.get64
      (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0]))
      (W64.to_uint i) byte)));
      i <- (i + (W64.of_int 1));
    }
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) 64
    (truncateu8 index))));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) 65
    (W8.of_int 0))));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) 66
    (W8.of_int 31))));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) (136 - 1)
    (W8.of_int 128))));
    return state;
  }
  proc rejection_sample_less_than_eta (state:W64.t Array25.t,
                                       error:W32.t Array256.t, sampled:W64.t) : 
  W32.t Array256.t * W64.t = {
    var msf:W64.t;
    var xof_offset:W64.t;
    var b:bool;
    var byte:W8.t;
    var try_coefficient:W32.t;
    var temp:W32.t;
    msf <- (init_msf);
    xof_offset <- (W64.of_int 0);
    b <- (xof_offset \ult (W64.of_int 136));
    while (b) {
      msf <- (update_msf b msf);
      b <- (sampled \ult (W64.of_int 256));
      if (b) {
        msf <- (update_msf b msf);
        byte <-
        (get8 (WArray200.init64 (fun i => state.[i]))
        (W64.to_uint xof_offset));
        try_coefficient <- (zeroextu32 byte);
        try_coefficient <- (try_coefficient `&` (W32.of_int 15));
        try_coefficient <- (protect_32 try_coefficient msf);
        b <- (try_coefficient \ult (W32.of_int 9));
        if (b) {
          msf <- (update_msf b msf);
          temp <- (W32.of_int 4);
          temp <- (temp - try_coefficient);
          error.[(W64.to_uint sampled)] <- temp;
          sampled <- (sampled + (W64.of_int 1));
        } else {
          msf <- (update_msf (! b) msf);
        }
        b <- (sampled \ult (W64.of_int 256));
        if (b) {
          msf <- (update_msf b msf);
          try_coefficient <- (zeroextu32 byte);
          try_coefficient <- (try_coefficient `>>` (W8.of_int 4));
          try_coefficient <- (protect_32 try_coefficient msf);
          b <- (try_coefficient \ult (W32.of_int 9));
          if (b) {
            msf <- (update_msf b msf);
            temp <- (W32.of_int 4);
            temp <- (temp - try_coefficient);
            error.[(W64.to_uint sampled)] <- temp;
            sampled <- (sampled + (W64.of_int 1));
          } else {
            msf <- (update_msf (! b) msf);
          }
        } else {
          msf <- (update_msf (! b) msf);
        }
      } else {
        msf <- (update_msf (! b) msf);
      }
      xof_offset <- (xof_offset + (W64.of_int 1));
      b <- (xof_offset \ult (W64.of_int 136));
    }
    return (error, sampled);
  }
  proc __sample_error_polynomial (rho_prime:W8.t Array64.t, i:int,
                                  error:W32.t Array256.t) : W32.t Array256.t = {
    var state:W64.t Array25.t;
    var coefficients_sampled:W64.t;
    state <- witness;
    (* Erased call to spill *)
    state <@ __absorb_to_generate_errors (rho_prime, (W16.of_int i));
    state <@ _keccakf1600_ref1 (state);
    (* Erased call to unspill *)
    coefficients_sampled <- (W64.of_int 0);
    (error, coefficients_sampled) <@ rejection_sample_less_than_eta (
    state, error, coefficients_sampled);
    while ((coefficients_sampled \ult (W64.of_int 256))) {
      (* Erased call to spill *)
      state <@ _keccakf1600_ref1 (state);
      (* Erased call to unspill *)
      (error, coefficients_sampled) <@ rejection_sample_less_than_eta (
      state, error, coefficients_sampled);
    }
    return error;
  }
  proc sample____error_vectors (rho_prime:W8.t Array64.t) : W32.t Array1280.t *
                                                            W32.t Array1536.t = {
    var aux:W32.t Array256.t;
    var s1:W32.t Array1280.t;
    var s2:W32.t Array1536.t;
    var i:int;
    s1 <- witness;
    s2 <- witness;
    i <- 0;
    while ((i < 5)) {
      aux <@ __sample_error_polynomial (rho_prime, i,
      (Array256.init (fun i_0 => s1.[((256 * i) + i_0)])));
      s1 <-
      (Array1280.init
      (fun i_0 => (if ((256 * i) <= i_0 < ((256 * i) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (256 * i))] else 
                  s1.[i_0]))
      );
      i <- (i + 1);
    }
    i <- 0;
    while ((i < 6)) {
      aux <@ __sample_error_polynomial (rho_prime, (5 + i),
      (Array256.init (fun i_0 => s2.[((256 * i) + i_0)])));
      s2 <-
      (Array1536.init
      (fun i_0 => (if ((256 * i) <= i_0 < ((256 * i) + 256)) then aux.[
                                                                  (i_0 -
                                                                  (256 * i))] else 
                  s2.[i_0]))
      );
      i <- (i + 1);
    }
    return (s1, s2);
  }
  proc __prepare_state_for_shake256 (randomness:W8.t Array32.t,
                                     number_of_rows:W8.t,
                                     number_of_columns:W8.t) : W64.t Array25.t = {
    var state:W64.t Array25.t;
    var i:W64.t;
    var byte:W8.t;
    state <- witness;
    state <@ __keccak_init_ref1 (state);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      byte <- randomness.[(W64.to_uint i)];
      state <-
      (Array25.init
      (WArray200.get64
      (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0]))
      (W64.to_uint i) byte)));
      i <- (i + (W64.of_int 1));
    }
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) 32
    number_of_rows)));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) 33
    number_of_columns)));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) 34
    ((get8 (WArray200.init64 (fun i_0 => state.[i_0])) 34) `^`
    (W8.of_int 31)))));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i_0 => state.[i_0])) (136 - 1)
    ((get8 (WArray200.init64 (fun i_0 => state.[i_0])) (136 - 1)) `^`
    (W8.of_int 128)))));
    return state;
  }
  proc __keygen_internal (verification_key:W8.t Array1952.t,
                          signing_key:W8.t Array4032.t,
                          randomness:W8.t Array32.t) : W8.t Array1952.t *
                                                       W8.t Array4032.t = {
    var aux_1:W8.t Array1920.t;
    var aux_2:W8.t Array2496.t;
    var aux:W8.t Array640.t;
    var aux_0:W8.t Array768.t;
    var state:W64.t Array25.t;
    var seed_for_matrix_A:W8.t Array32.t;
    var seed_for_error_vectors:W8.t Array64.t;
    var seed_for_signing:W8.t Array32.t;
    var s1:W32.t Array1280.t;
    var s2:W32.t Array1536.t;
    var i:W64.t;
    var matrix_A:W32.t Array7680.t;
    var t:W32.t Array1536.t;
    var t1:W32.t Array1536.t;
    var t0:W32.t Array1536.t;
    var verification_key_pointer_copy:W8.t Array1952.t;
    var verification_key_hash:W8.t Array64.t;
    matrix_A <- witness;
    s1 <- witness;
    s2 <- witness;
    seed_for_error_vectors <- witness;
    seed_for_matrix_A <- witness;
    seed_for_signing <- witness;
    state <- witness;
    t <- witness;
    t0 <- witness;
    t1 <- witness;
    verification_key_hash <- witness;
    verification_key_pointer_copy <- witness;
    (* Erased call to spill *)
    state <@ __prepare_state_for_shake256 (randomness, (W8.of_int 6),
    (W8.of_int 5));
    state <@ _keccakf1600_ref1 (state);
    seed_for_matrix_A <-
    (Array32.init
    (fun i_0 => (get8 (WArray200.init64 (fun i_0 => state.[i_0])) (0 + i_0)))
    );
    seed_for_error_vectors <-
    (Array64.init
    (fun i_0 => (get8 (WArray200.init64 (fun i_0 => state.[i_0])) (32 + i_0)))
    );
    seed_for_signing <-
    (Array32.init
    (fun i_0 => (get8 (WArray200.init64 (fun i_0 => state.[i_0]))
                ((32 + 64) + i_0)))
    );
    (s1, s2) <@ sample____error_vectors (seed_for_error_vectors);
    (* Erased call to unspill *)
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      signing_key.[(W64.to_uint i)] <- seed_for_matrix_A.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      signing_key.[(W64.to_uint ((W64.of_int 32) + i))] <-
      seed_for_signing.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
    }
    aux <@ s1____encode ((Array640.init
                         (fun i_0 => signing_key.[(((32 + 32) + 64) + i_0)])),
    s1);
    signing_key <-
    (Array4032.init
    (fun i_0 => (if (((32 + 32) + 64) <= i_0 < (((32 + 32) + 64) + 640)) then 
                aux.[(i_0 - ((32 + 32) + 64))] else signing_key.[i_0]))
    );
    aux_0 <@ s2____encode ((Array768.init
                           (fun i_0 => signing_key.[((((32 + 32) + 64) +
                                                     (5 * 128)) +
                                                    i_0)])
                           ),
    s2);
    signing_key <-
    (Array4032.init
    (fun i_0 => (if ((((32 + 32) + 64) + (5 * 128)) <= i_0 < ((((32 + 32) +
                                                               64) +
                                                              (5 * 128)) +
                                                             768)) then 
                aux_0.[(i_0 - (((32 + 32) + 64) + (5 * 128)))] else signing_key.[
                                                                    i_0]))
    );
    (* Erased call to spill *)
    s1 <@ row_vector__ntt (s1);
    matrix_A <@ sample____matrix_A (seed_for_matrix_A);
    t <@ row_vector____multiply_with_matrix_A (matrix_A, s1);
    t <@ column_vector__reduce32 (t);
    t <@ column_vector__invert_ntt_montgomery (t);
    t <@ column_vector____add (t, s2);
    t <@ column_vector____conditionally_add_modulus (t);
    (t1, t0) <@ column_vector____power2round (t);
    (* Erased call to unspill *)
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      verification_key.[(W64.to_uint i)] <-
      seed_for_matrix_A.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
    }
    aux_1 <@ t1____encode ((Array1920.init
                           (fun i_0 => verification_key.[(32 + i_0)])),
    t1);
    verification_key <-
    (Array1952.init
    (fun i_0 => (if (32 <= i_0 < (32 + 1920)) then aux_1.[(i_0 - 32)] else 
                verification_key.[i_0]))
    );
    verification_key_pointer_copy <- verification_key;
    verification_key_hash <@ __hash_verification_key (verification_key_pointer_copy,
    verification_key_hash);
    (* Erased call to unspill *)
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 64))) {
      signing_key.[(W64.to_uint ((W64.of_int 64) + i))] <-
      verification_key_hash.[(W64.to_uint i)];
      i <- (i + (W64.of_int 1));
    }
    aux_2 <@ t0____encode ((Array2496.init
                           (fun i_0 => signing_key.[(((((32 + 32) + 64) +
                                                      (5 * 128)) +
                                                     (6 * 128)) +
                                                    i_0)])
                           ),
    t0);
    signing_key <-
    (Array4032.init
    (fun i_0 => (if (((((32 + 32) + 64) + (5 * 128)) + (6 * 128)) <= 
                    i_0 < (((((32 + 32) + 64) + (5 * 128)) + (6 * 128)) +
                          2496)) then aux_2.[(i_0 -
                                             ((((32 + 32) + 64) + (5 * 128)) +
                                             (6 * 128)))] else signing_key.[
                                                               i_0]))
    );
    return (verification_key, signing_key);
  }
  proc commitment____encode_polynomial (output:W8.t Array128.t,
                                        commitment_polynomial:W32.t Array256.t) : 
  W8.t Array128.t = {
    var i:W64.t;
    var encoded_byte:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (256 %/ 2)))) {
      encoded_byte <-
      commitment_polynomial.[(W64.to_uint
                             (((W64.of_int 2) * i) + (W64.of_int 1)))];
      encoded_byte <- (encoded_byte `<<` (W8.of_int 4));
      encoded_byte <-
      (encoded_byte `|`
      commitment_polynomial.[(W64.to_uint
                             (((W64.of_int 2) * i) + (W64.of_int 0)))]);
      output.[(W64.to_uint i)] <- (truncateu8 encoded_byte);
      i <- (i + (W64.of_int 1));
    }
    return output;
  }
  proc commitment____encode (commitment:W32.t Array1536.t) : W8.t Array768.t = {
    var aux:W8.t Array128.t;
    var encoded_commitment:W8.t Array768.t;
    var i:int;
    encoded_commitment <- witness;
    i <- 0;
    while ((i < 6)) {
      aux <@ commitment____encode_polynomial ((Array128.init
                                              (fun i_0 => encoded_commitment.[
                                                          ((i *
                                                           ((4 * 256) %/ 8)) +
                                                          i_0)])
                                              ),
      (Array256.init (fun i_0 => commitment.[((i * 256) + i_0)])));
      encoded_commitment <-
      (Array768.init
      (fun i_0 => (if ((i * ((4 * 256) %/ 8)) <= i_0 < ((i *
                                                        ((4 * 256) %/ 8)) +
                                                       128)) then aux.[
                                                                  (i_0 -
                                                                  (i *
                                                                  ((4 * 256) %/
                                                                  8)))] else 
                  encoded_commitment.[i_0]))
      );
      i <- (i + 1);
    }
    return encoded_commitment;
  }
  proc derive_seed_for_mask (k:W8.t Array32.t, randomness:W8.t Array32.t,
                             message_representative:W8.t Array64.t,
                             seed_for_mask:W8.t Array64.t) : W8.t Array64.t = {
    var state:W64.t Array25.t;
    state <- witness;
    state <@ __keccak_init_ref1 (state);
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.init8
    (fun i => (if ((1 * 0) <= i < ((1 * 0) + 32)) then (WArray32.get8
                                                       (WArray32.init8
                                                       (fun i => (
                                                                 Array32.init
                                                                 (fun i => 
                                                                 (get8
                                                                 (
                                                                 WArray32.init64
                                                                 (fun i => 
                                                                 (copy_64
                                                                 (Array4.init
                                                                 (fun i => 
                                                                 (get64
                                                                 (
                                                                 WArray32.init8
                                                                 (fun i => 
                                                                 k.[i])) 
                                                                 i)))).[
                                                                 i])) 
                                                                 i))).[
                                                                 i])
                                                       ) (i - (1 * 0))) else 
              (WArray200.get8 (WArray200.init64 (fun i => state.[i])) 
              i)))
    )));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.init8
    (fun i => (if ((1 * 32) <= i < ((1 * 32) + 32)) then (WArray32.get8
                                                         (WArray32.init8
                                                         (fun i => (
                                                                   Array32.init
                                                                   (fun i => 
                                                                   (get8
                                                                   (
                                                                   WArray32.init64
                                                                   (fun i => 
                                                                   (copy_64
                                                                   (
                                                                   Array4.init
                                                                   (fun i => 
                                                                   (get64
                                                                   (
                                                                   WArray32.init8
                                                                   (fun i => 
                                                                   randomness.[
                                                                   i])) 
                                                                   i)))).[
                                                                   i])) 
                                                                   i))).[
                                                                   i])
                                                         ) (i - (1 * 32))) else 
              (WArray200.get8 (WArray200.init64 (fun i => state.[i])) 
              i)))
    )));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.init8
    (fun i => (if ((1 * 64) <= i < ((1 * 64) + 64)) then (WArray64.get8
                                                         (WArray64.init8
                                                         (fun i => (
                                                                   Array64.init
                                                                   (fun i => 
                                                                   (get8
                                                                   (
                                                                   WArray64.init64
                                                                   (fun i => 
                                                                   (copy_64
                                                                   (
                                                                   Array8.init
                                                                   (fun i => 
                                                                   (get64
                                                                   (
                                                                   WArray64.init8
                                                                   (fun i => 
                                                                   message_representative.[
                                                                   i])) 
                                                                   i)))).[
                                                                   i])) 
                                                                   i))).[
                                                                   i])
                                                         ) (i - (1 * 64))) else 
              (WArray200.get8 (WArray200.init64 (fun i => state.[i])) 
              i)))
    )));
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i => state.[i])) 128
    ((get8 (WArray200.init64 (fun i => state.[i])) 128) `^` (W8.of_int 31))))
    );
    state <-
    (Array25.init
    (WArray200.get64
    (WArray200.set8 (WArray200.init64 (fun i => state.[i])) (136 - 1)
    ((get8 (WArray200.init64 (fun i => state.[i])) (136 - 1)) `^`
    (W8.of_int 128)))));
    (* Erased call to spill *)
    state <@ _keccakf1600_ref1 (state);
    (* Erased call to unspill *)
    seed_for_mask <-
    (Array64.init
    (fun i => (get8
              (WArray64.init64
              (fun i => (copy_64
                        (Array8.init
                        (fun i => (get64
                                  (WArray64.init8
                                  (fun i => (Array64.init
                                            (fun i => (get8
                                                      (WArray200.init64
                                                      (fun i => state.[i]))
                                                      (0 + i)))
                                            ).[i])
                                  ) i))
                        )).[i])
              ) i))
    );
    return seed_for_mask;
  }
  proc __sign_internal (signature:W8.t Array3309.t,
                        signing_key:W8.t Array4032.t,
                        pointer_to_message:W64.t, message_size:W64.t,
                        randomness:W8.t Array32.t) : W8.t Array3309.t = {
    var message_representative:W8.t Array64.t;
    var seed_for_matrix_A:W8.t Array32.t;
    var matrix_A:W32.t Array7680.t;
    var seed_for_mask:W8.t Array64.t;
    var s1:W32.t Array1280.t;
    var s2:W32.t Array1536.t;
    var t0:W32.t Array1536.t;
    var domain_separator_for_mask:W16.t;
    var exit_rejection_sampling_loop:W8.t;
    var mask:W32.t Array1280.t;
    var mask_as_ntt:W32.t Array1280.t;
    var w:W32.t Array1536.t;
    var w0:W32.t Array1536.t;
    var w1:W32.t Array1536.t;
    var commitment_encoded:W8.t Array768.t;
    var commitment_hash:W8.t Array48.t;
    var verifier_challenge:W32.t Array256.t;
    var cs1:W32.t Array1280.t;
    var signer_response:W32.t Array1280.t;
    var infinity_norm_check_result:W8.t;
    var cs2:W32.t Array1536.t;
    var w0_minus_cs2:W32.t Array1536.t;
    var ct0:W32.t Array1536.t;
    var w0_minus_cs2_plus_ct0:W32.t Array1536.t;
    var hint_0:W32.t Array1536.t;
    var ones_in_hint:W32.t;
    var  _0:W64.t;
    var  _1:W64.t;
    var  _2:W64.t;
    var  _3:W64.t;
    var  _4:W64.t;
    commitment_encoded <- witness;
    commitment_hash <- witness;
    cs1 <- witness;
    cs2 <- witness;
    ct0 <- witness;
    hint_0 <- witness;
    mask <- witness;
    mask_as_ntt <- witness;
    matrix_A <- witness;
    message_representative <- witness;
    s1 <- witness;
    s2 <- witness;
    seed_for_mask <- witness;
    seed_for_matrix_A <- witness;
    signer_response <- witness;
    t0 <- witness;
    verifier_challenge <- witness;
    w <- witness;
    w0 <- witness;
    w0_minus_cs2 <- witness;
    w0_minus_cs2_plus_ct0 <- witness;
    w1 <- witness;
    (* Erased call to spill *)
    message_representative <@ __derive_message_representative ((Array64.init
                                                               (fun i => 
                                                               signing_key.[
                                                               (64 + 
                                                               i)])),
    pointer_to_message, message_size);
    (* Erased call to unspill *)
    seed_for_matrix_A <- (Array32.init (fun i => signing_key.[(0 + i)]));
     _0 <- (init_msf);
    matrix_A <@ sample____matrix_A (seed_for_matrix_A);
    (* Erased call to unspill *)
    (* Erased call to unspill *)
    seed_for_mask <@ derive_seed_for_mask ((Array32.init
                                           (fun i => signing_key.[(32 + i)])),
    randomness, message_representative, seed_for_mask);
    (* Erased call to unspill *)
    s1 <@ s1____decode (s1,
    (Array640.init (fun i => signing_key.[(((32 + 32) + 64) + i)])));
    s2 <@ s2____decode (s2,
    (Array768.init
    (fun i => signing_key.[((((32 + 32) + 64) + (5 * 128)) + i)])));
    t0 <@ t0____decode (t0,
    (Array2496.init
    (fun i => signing_key.[(((((32 + 32) + 64) + (5 * 128)) + (6 * 128)) + i)])
    ));
    s1 <@ row_vector__ntt (s1);
    s2 <@ column_vector__ntt (s2);
    t0 <@ column_vector__ntt (t0);
    domain_separator_for_mask <- (W16.of_int 0);
    exit_rejection_sampling_loop <- (W8.of_int 0);
    while ((exit_rejection_sampling_loop <> (W8.of_int 1))) {
      (mask, domain_separator_for_mask) <@ sample____mask (seed_for_mask,
      domain_separator_for_mask);
      mask_as_ntt <-
      (Array1280.init
      (fun i => (get32
                (WArray5120.init64
                (fun i => (copy_64
                          (Array640.init
                          (fun i => (get64
                                    (WArray5120.init32 (fun i => mask.[i])) 
                                    i))
                          )).[i])
                ) i))
      );
      mask_as_ntt <@ row_vector__ntt (mask_as_ntt);
      w <@ row_vector____multiply_with_matrix_A (matrix_A, mask_as_ntt);
      w <@ column_vector__reduce32 (w);
      w <@ column_vector__invert_ntt_montgomery (w);
      w <@ column_vector____conditionally_add_modulus (w);
      (w0, w1) <@ column_vector____decompose (w);
      commitment_encoded <@ commitment____encode (w1);
      (* Erased call to spill *)
      commitment_hash <@ __derive_commitment_hash (message_representative,
      commitment_encoded);
      verifier_challenge <@ sample____challenge (verifier_challenge,
      commitment_hash);
      (* Erased call to unspill *)
      verifier_challenge <@ polynomial__ntt (verifier_challenge);
      cs1 <@ row_vector____multiply_by_polynomial (s1, verifier_challenge);
      cs1 <@ row_vector__invert_ntt_montgomery (cs1);
      signer_response <@ row_vector____add (cs1, mask);
      signer_response <@ row_vector__reduce32 (signer_response);
      infinity_norm_check_result <@ row_vector____check_infinity_norm (
      signer_response, ((1 `<<` 19) - (49 * 4)));
      infinity_norm_check_result <- infinity_norm_check_result;
       _1 <- (init_msf);
      if ((infinity_norm_check_result = (W8.of_int 0))) {
        cs2 <@ column_vector____multiply_by_polynomial (s2,
        verifier_challenge);
        cs2 <@ column_vector__invert_ntt_montgomery (cs2);
        w0_minus_cs2 <@ column_vector____subtract (w0, cs2);
        w0_minus_cs2 <@ column_vector__reduce32 (w0_minus_cs2);
        infinity_norm_check_result <@ column_vector____check_infinity_norm (
        w0_minus_cs2, (((8380417 - 1) %/ 32) - (49 * 4)));
        infinity_norm_check_result <- infinity_norm_check_result;
         _2 <- (init_msf);
        if ((infinity_norm_check_result = (W8.of_int 0))) {
          ct0 <@ column_vector____multiply_by_polynomial (t0,
          verifier_challenge);
          ct0 <@ column_vector__invert_ntt_montgomery (ct0);
          ct0 <@ column_vector__reduce32 (ct0);
          infinity_norm_check_result <@ column_vector____check_infinity_norm (
          ct0, ((8380417 - 1) %/ 32));
          infinity_norm_check_result <- infinity_norm_check_result;
           _3 <- (init_msf);
          if ((infinity_norm_check_result = (W8.of_int 0))) {
            w0_minus_cs2_plus_ct0 <@ column_vector____add (w0_minus_cs2,
            ct0);
            (hint_0, ones_in_hint) <@ column_vector____make_hint (w0_minus_cs2_plus_ct0,
            w1);
             _4 <- (init_msf);
            if ((ones_in_hint \ule (W32.of_int 55))) {
              exit_rejection_sampling_loop <- (W8.of_int 1);
            } else {
              
            }
          } else {
            
          }
        } else {
          
        }
      } else {
        
      }
    }
    (* Erased call to unspill *)
    signer_response <- signer_response;
    hint_0 <- hint_0;
    commitment_hash <- commitment_hash;
    signature <@ signature____encode (signature, commitment_hash,
    signer_response, hint_0);
    return signature;
  }
  proc __compare_commitment_hashes (lhs:W8.t Array48.t, rhs:W8.t Array48.t) : 
  W64.t = {
    var result:W64.t;
    var msf:W64.t;
    var i:W64.t;
    var condition:bool;
    var lhs_byte:W8.t;
    var rhs_byte:W8.t;
    msf <- (init_msf);
    result <- (W64.of_int 0);
    i <- (W64.of_int 0);
    condition <- (i \ult (W64.of_int 48));
    while (condition) {
      msf <- (update_msf condition msf);
      lhs_byte <- lhs.[(W64.to_uint i)];
      lhs_byte <- (protect_8 lhs_byte msf);
      rhs_byte <- rhs.[(W64.to_uint i)];
      rhs_byte <- (protect_8 rhs_byte msf);
      condition <- (lhs_byte <> rhs_byte);
      if (condition) {
        msf <- (update_msf condition msf);
        result <- (result `|` (W64.of_int (- 1)));
      } else {
        msf <- (update_msf (! condition) msf);
      }
      i <- (i + (W64.of_int 1));
      condition <- (i \ult (W64.of_int 48));
    }
    return result;
  }
  proc reconstruct_signer_commitment (t1_encoded:W8.t Array1920.t,
                                      challenge_as_ntt:W32.t Array256.t,
                                      a_times_signer_response:W32.t Array1536.t,
                                      hints:W32.t Array1536.t) : W8.t Array768.t = {
    var commitment_encoded:W8.t Array768.t;
    var i:int;
    var az_element:W32.t Array256.t;
    var t1_element:W32.t Array256.t;
    var c_times_t1:W32.t Array256.t;
    var commitment:W32.t Array1536.t;
    var commitment_element:W32.t Array256.t;
    az_element <- witness;
    c_times_t1 <- witness;
    commitment <- witness;
    commitment_element <- witness;
    commitment_encoded <- witness;
    t1_element <- witness;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 6)) {
      az_element <-
      (Array256.init (fun i_0 => a_times_signer_response.[((i * 256) + i_0)])
      );
      t1_element <@ t1__decode_polynomial (t1_element,
      (Array320.init
      (fun i_0 => t1_encoded.[(((((23 - 13) * 256) %/ 8) * i) + i_0)])));
      t1_element <@ polynomial____shift_coefficients_left (t1_element);
      t1_element <@ polynomial__ntt (t1_element);
      (* Erased call to unspill *)
      c_times_t1 <@ polynomial__pointwise_montgomery_product (c_times_t1,
      challenge_as_ntt, t1_element);
      commitment_element <-
      (Array256.init (fun i_0 => commitment.[((i * 256) + i_0)]));
      commitment_element <@ polynomial__subtract (commitment_element,
      az_element, c_times_t1);
      commitment_element <@ polynomial__reduce32 (commitment_element);
      commitment_element <@ polynomial__invert_ntt_montgomery (commitment_element);
      commitment_element <@ polynomial__conditionally_add_modulus (commitment_element);
      commitment_element <- commitment_element;
      commitment_element <@ polynomial__use_hints (commitment_element,
      (Array256.init (fun i_0 => hints.[((i * 256) + i_0)])));
      commitment <-
      (Array1536.init
      (fun i_0 => (if ((i * 256) <= i_0 < ((i * 256) + 256)) then commitment_element.[
                                                                  (i_0 -
                                                                  (i * 256))] else 
                  commitment.[i_0]))
      );
      i <- (i + 1);
    }
    commitment_encoded <@ commitment____encode (commitment);
    return commitment_encoded;
  }
  proc __verify_internal (verification_key:W8.t Array1952.t, message:W64.t,
                          message_size:W64.t,
                          signature_encoded:W8.t Array3309.t) : W64.t = {
    var result:W64.t;
    var signer_response:W32.t Array1280.t;
    var signer_response_outside_bounds:W8.t;
    var hints:W32.t Array1536.t;
    var matrix_A:W32.t Array7680.t;
    var a_times_signer_response:W32.t Array1536.t;
    var challenge:W32.t Array256.t;
    var reconstructed_signer_commitment:W8.t Array768.t;
    var verification_key_hash:W8.t Array64.t;
    var message_representative:W8.t Array64.t;
    var expected_commitment_hash:W8.t Array48.t;
    var  _0:W64.t;
    a_times_signer_response <- witness;
    challenge <- witness;
    expected_commitment_hash <- witness;
    hints <- witness;
    matrix_A <- witness;
    message_representative <- witness;
    reconstructed_signer_commitment <- witness;
    signer_response <- witness;
    verification_key_hash <- witness;
    result <- (W64.of_int (- 1));
    signer_response <@ gamma1____decode (signer_response,
    (Array3200.init (fun i => signature_encoded.[(48 + i)])));
    signer_response_outside_bounds <@ row_vector____check_infinity_norm (
    signer_response, ((1 `<<` 19) - (49 * 4)));
     _0 <- (init_msf);
    if ((signer_response_outside_bounds = (W8.of_int 0))) {
      (hints, result) <@ signature____decode_hint (hints,
      (Array61.init
      (fun i => signature_encoded.[((48 + (5 * ((20 * 256) %/ 8))) + i)])));
      if ((result = (W64.of_int 0))) {
        (* Erased call to spill *)
        (* Erased call to spill *)
        matrix_A <@ sample____matrix_A ((Array32.init
                                        (fun i => verification_key.[(0 + i)])
                                        ));
        signer_response <@ row_vector__ntt (signer_response);
        a_times_signer_response <@ row_vector____multiply_with_matrix_A (
        matrix_A, signer_response);
        (* Erased call to unspill *)
        challenge <@ sample____challenge (challenge,
        (Array48.init (fun i => signature_encoded.[(0 + i)])));
        challenge <@ polynomial__ntt (challenge);
        (* Erased call to unspill *)
        reconstructed_signer_commitment <@ reconstruct_signer_commitment (
        (Array1920.init (fun i => verification_key.[(32 + i)])), challenge,
        a_times_signer_response, hints);
        (* Erased call to unspill *)
        verification_key_hash <@ __hash_verification_key (verification_key,
        verification_key_hash);
        (* Erased call to unspill *)
        message_representative <@ __derive_message_representative (verification_key_hash,
        message, message_size);
        expected_commitment_hash <@ __derive_commitment_hash (message_representative,
        reconstructed_signer_commitment);
        (* Erased call to unspill *)
        result <@ __compare_commitment_hashes (expected_commitment_hash,
        (Array48.init (fun i => signature_encoded.[(0 + i)])));
      } else {
        
      }
    } else {
      
    }
    return result;
  }
  proc ml_dsa_65_keygen (verification_key:W8.t Array1952.t,
                         signing_key:W8.t Array4032.t,
                         randomness:W8.t Array32.t) : W8.t Array1952.t *
                                                      W8.t Array4032.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    (verification_key, signing_key) <@ __keygen_internal (verification_key,
    signing_key, randomness);
    return (verification_key, signing_key);
  }
  proc ml_dsa_65_sign (signature:W8.t Array3309.t,
                       signing_key:W8.t Array4032.t, message:W64.t,
                       message_size:W64.t, randomness:W8.t Array32.t) : 
  W8.t Array3309.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    signature <@ __sign_internal (signature, signing_key, message,
    message_size, randomness);
    return signature;
  }
  proc ml_dsa_65_verify (verification_key:W8.t Array1952.t, message:W64.t,
                         message_size:W64.t, signature:W8.t Array3309.t) : 
  W64.t = {
    var verification_result:W64.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    verification_result <@ __verify_internal (verification_key, message,
    message_size, signature);
    return verification_result;
  }
}.
