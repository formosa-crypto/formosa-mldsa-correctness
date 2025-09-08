require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array5 Array8 Array24 Array25 Array32 Array48 Array61 Array64 Array128
Array256 Array320 Array416 Array640 Array680 Array768 Array1280 Array1536
Array1920 Array1952 Array2496 Array3200 Array3309 Array4032 Array7680
WArray192 WArray1024 BArray32 BArray40 BArray48 BArray61 BArray64 BArray128
BArray192 BArray200 BArray320 BArray416 BArray640 BArray680 BArray768
BArray1024 BArray1920 BArray1952 BArray2496 BArray3200 BArray3309 BArray4032
BArray5120 BArray6144 BArray30720 SBArray200_32 SBArray1952_32 SBArray4032_32
SBArray3309_48 SBArray3309_61 SBArray200_64 SBArray4032_64 SBArray640_128
SBArray768_128 SBArray1920_320 SBArray2496_416 SBArray680_640 SBArray3200_640
SBArray3309_640 SBArray4032_640 SBArray4032_768 SBArray5120_1024
SBArray6144_1024 SBArray30720_1024 SBArray1952_1920 SBArray4032_2496
SBArray3309_3200 SBArray30720_5120.

abbrev zETAS_TIMES_MONTGOMERY_R =
(BArray1024.of_list32
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
(BArray192.of_list64
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
  proc error_polynomial__encode (encoded:BArray128.t, polynomial:BArray1024.t) : 
  BArray128.t = {
    var i:W64.t;
    var coefficient:W32.t;
    var low_nibble:W32.t;
    var high_nibble:W32.t;
    var out_offset:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      coefficient <- (BArray1024.get32 polynomial (W64.to_uint i));
      low_nibble <- (W32.of_int 4);
      low_nibble <- (low_nibble - coefficient);
      coefficient <-
      (BArray1024.get32 polynomial (W64.to_uint (i + (W64.of_int 1))));
      high_nibble <- (W32.of_int 4);
      high_nibble <- (high_nibble - coefficient);
      high_nibble <- (high_nibble `<<` (W8.of_int 4));
      high_nibble <- (high_nibble `|` low_nibble);
      out_offset <- i;
      out_offset <- (out_offset `>>` (W8.of_int 1));
      encoded <-
      (BArray128.set8 encoded (W64.to_uint out_offset)
      (truncateu8 high_nibble));
      i <- (i + (W64.of_int 2));
    }
    return encoded;
  }
  proc error_polynomial__decode (decoded:BArray1024.t, encoded:BArray128.t) : 
  BArray1024.t = {
    var i:W64.t;
    var nibble:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (256 %/ 2)))) {
      nibble <- (zeroextu32 (BArray128.get8 encoded (W64.to_uint i)));
      nibble <- (nibble `&` (W32.of_int 15));
      nibble <- (- nibble);
      nibble <- (nibble + (W32.of_int 4));
      decoded <-
      (BArray1024.set32 decoded (W64.to_uint ((W64.of_int 2) * i)) nibble);
      nibble <- (zeroextu32 (BArray128.get8 encoded (W64.to_uint i)));
      nibble <- (nibble `>>` (W8.of_int 4));
      nibble <- (- nibble);
      nibble <- (nibble + (W32.of_int 4));
      decoded <-
      (BArray1024.set32 decoded
      (W64.to_uint (((W64.of_int 2) * i) + (W64.of_int 1))) nibble);
      i <- (i + (W64.of_int 1));
    }
    return decoded;
  }
  proc gamma1____encode_polynomial (encoded:BArray640.t,
                                    polynomial:BArray1024.t) : BArray640.t = {
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
      (BArray1024.get32 polynomial
      (W64.to_uint (((W64.of_int 2) * i) + (W64.of_int 0)))));
      t1 <- (W32.of_int (1 `<<` 19));
      t1 <-
      (t1 -
      (BArray1024.get32 polynomial
      (W64.to_uint (((W64.of_int 2) * i) + (W64.of_int 1)))));
      encoded_bytes <- t0;
      encoded <-
      (BArray640.set8 encoded (W64.to_uint output_offset)
      (truncateu8 encoded_bytes));
      encoded_bytes <- t0;
      encoded_bytes <- (encoded_bytes `>>` (W8.of_int 8));
      encoded <-
      (BArray640.set8 encoded (W64.to_uint (output_offset + (W64.of_int 1)))
      (truncateu8 encoded_bytes));
      encoded_bytes <- t0;
      encoded_bytes <- (encoded_bytes `>>` (W8.of_int 16));
      byte <- (truncateu8 encoded_bytes);
      encoded_bytes <- t1;
      encoded_bytes <- (encoded_bytes `<<` (W8.of_int 4));
      byte <- (byte `|` (truncateu8 encoded_bytes));
      encoded <-
      (BArray640.set8 encoded (W64.to_uint (output_offset + (W64.of_int 2)))
      byte);
      encoded_bytes <- t1;
      encoded_bytes <- (encoded_bytes `>>` (W8.of_int 4));
      encoded <-
      (BArray640.set8 encoded (W64.to_uint (output_offset + (W64.of_int 3)))
      (truncateu8 encoded_bytes));
      encoded_bytes <- t1;
      encoded_bytes <- (encoded_bytes `>>` (W8.of_int 12));
      encoded <-
      (BArray640.set8 encoded (W64.to_uint (output_offset + (W64.of_int 4)))
      (truncateu8 encoded_bytes));
      output_offset <- (output_offset + (W64.of_int 5));
      i <- (i + (W64.of_int 1));
    }
    return encoded;
  }
  proc gamma1____decode_to_polynomial (polynomial:BArray1024.t,
                                       bytes:BArray640.t) : BArray1024.t = {
    var input_offset:W64.t;
    var output_offset:W64.t;
    var coefficient:W32.t;
    var temp:W32.t;
    input_offset <- (W64.of_int 0);
    output_offset <- (W64.of_int 0);
    while ((input_offset \ult (W64.of_int ((20 * 256) %/ 8)))) {
      coefficient <-
      (zeroextu32 (BArray640.get8 bytes (W64.to_uint input_offset)));
      temp <-
      (zeroextu32
      (BArray640.get8 bytes (W64.to_uint (input_offset + (W64.of_int 1)))));
      temp <- (temp `<<` (W8.of_int 8));
      coefficient <- (coefficient `|` temp);
      temp <-
      (zeroextu32
      (BArray640.get8 bytes (W64.to_uint (input_offset + (W64.of_int 2)))));
      temp <- (temp `<<` (W8.of_int 16));
      coefficient <- (coefficient `|` temp);
      coefficient <- (coefficient `&` (W32.of_int 1048575));
      coefficient <- (- coefficient);
      coefficient <- (coefficient + (W32.of_int (1 `<<` 19)));
      polynomial <-
      (BArray1024.set32 polynomial
      (W64.to_uint (output_offset + (W64.of_int 0))) coefficient);
      coefficient <-
      (zeroextu32
      (BArray640.get8 bytes (W64.to_uint (input_offset + (W64.of_int 2)))));
      coefficient <- (coefficient `>>` (W8.of_int 4));
      temp <-
      (zeroextu32
      (BArray640.get8 bytes (W64.to_uint (input_offset + (W64.of_int 3)))));
      temp <- (temp `<<` (W8.of_int 4));
      coefficient <- (coefficient `|` temp);
      temp <-
      (zeroextu32
      (BArray640.get8 bytes (W64.to_uint (input_offset + (W64.of_int 4)))));
      temp <- (temp `<<` (W8.of_int 12));
      coefficient <- (coefficient `|` temp);
      coefficient <- (- coefficient);
      coefficient <- (coefficient + (W32.of_int (1 `<<` 19)));
      polynomial <-
      (BArray1024.set32 polynomial
      (W64.to_uint (output_offset + (W64.of_int 1))) coefficient);
      input_offset <- (input_offset + (W64.of_int 5));
      output_offset <- (output_offset + (W64.of_int 2));
    }
    return polynomial;
  }
  proc gamma1____decode (decoded:BArray5120.t, encoded:BArray3200.t) : 
  BArray5120.t = {
    var aux:BArray1024.t;
    var i:int;
    i <- 0;
    while ((i < 5)) {
      aux <@ gamma1____decode_to_polynomial ((SBArray5120_1024.get_sub32
                                             decoded (i * 256)),
      (SBArray3200_640.get_sub8 encoded (i * ((20 * 256) %/ 8))));
      decoded <- (SBArray5120_1024.set_sub32 decoded (i * 256) aux);
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
  proc __theta_sum_ref1 (a:BArray200.t) : BArray40.t = {
    var c:BArray40.t;
    var x:int;
    var y:int;
    c <- witness;
    x <- 0;
    while ((x < 5)) {
      c <- (BArray40.set64 c x (BArray200.get64 a (x + 0)));
      x <- (x + 1);
    }
    y <- 1;
    while ((y < 5)) {
      x <- 0;
      while ((x < 5)) {
        c <-
        (BArray40.set64 c x
        ((BArray40.get64 c x) `^` (BArray200.get64 a (x + (y * 5)))));
        x <- (x + 1);
      }
      y <- (y + 1);
    }
    return c;
  }
  proc __theta_rol_ref1 (c:BArray40.t) : BArray40.t = {
    var aux:W64.t;
    var d:BArray40.t;
    var x:int;
    d <- witness;
    x <- 0;
    while ((x < 5)) {
      d <- (BArray40.set64 d x (BArray40.get64 c ((x + 1) %% 5)));
      aux <@ __rotate_left_64 ((BArray40.get64 d x), 1);
      d <- (BArray40.set64 d x aux);
      d <-
      (BArray40.set64 d x
      ((BArray40.get64 d x) `^` (BArray40.get64 c (((x - 1) + 5) %% 5))));
      x <- (x + 1);
    }
    return d;
  }
  proc __rol_sum_ref1 (a:BArray200.t, d:BArray40.t, y:int) : BArray40.t = {
    var aux:W64.t;
    var b:BArray40.t;
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
      b <- (BArray40.set64 b x (BArray200.get64 a (x_ + (y_ * 5))));
      b <-
      (BArray40.set64 b x ((BArray40.get64 b x) `^` (BArray40.get64 d x_)));
      if ((r <> 0)) {
        aux <@ __rotate_left_64 ((BArray40.get64 b x), r);
        b <- (BArray40.set64 b x aux);
      } else {
        
      }
      x <- (x + 1);
    }
    return b;
  }
  proc __set_row_ref1 (e:BArray200.t, b:BArray40.t, y:int, s_rc:W64.t) : 
  BArray200.t = {
    var x:int;
    var x1:int;
    var x2:int;
    var t:W64.t;
    x <- 0;
    while ((x < 5)) {
      x1 <- ((x + 1) %% 5);
      x2 <- ((x + 2) %% 5);
      t <- (BArray40.get64 b x1);
      t <- (invw t);
      t <- (t `&` (BArray40.get64 b x2));
      t <- (t `^` (BArray40.get64 b x));
      if (((x = 0) /\ (y = 0))) {
        t <- (t `^` s_rc);
      } else {
        
      }
      e <- (BArray200.set64 e (x + (y * 5)) t);
      x <- (x + 1);
    }
    return e;
  }
  proc __round_ref1 (e:BArray200.t, a:BArray200.t, rc:W64.t) : BArray200.t = {
    var s_rc:W64.t;
    var c:BArray40.t;
    var d:BArray40.t;
    var y:int;
    var b:BArray40.t;
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
  proc __keccakf1600_ref1 (a:BArray200.t) : BArray200.t = {
    var rC:BArray192.t;
    var s_e:BArray200.t;
    var e:BArray200.t;
    var c:W64.t;
    var rc:W64.t;
    rC <- witness;
    e <- witness;
    s_e <- witness;
    rC <- kECCAK1600_RC;
    e <- s_e;
    c <- (W64.of_int 0);
    while ((c \ult (W64.of_int (24 - 1)))) {
      rc <- (BArray192.get64 rC (W64.to_uint c));
      e <@ __round_ref1 (e, a, rc);
      rc <- (BArray192.get64 rC ((W64.to_uint c) + 1));
      a <@ __round_ref1 (a, e, rc);
      c <- (c + (W64.of_int 2));
    }
    return a;
  }
  proc _keccakf1600_ref1 (a:BArray200.t) : BArray200.t = {
    
    a <@ __keccakf1600_ref1 (a);
    return a;
  }
  proc __keccak_init_ref1 (state:BArray200.t) : BArray200.t = {
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
      state <- (BArray200.set64 state i t);
      i <- (i + 1);
    }
    return state;
  }
  proc __hash_verification_key (verification_key:BArray1952.t,
                                hash:BArray64.t) : BArray64.t = {
    var state_offset:W64.t;
    var verification_key_offset:W64.t;
    var state:BArray200.t;
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
        byte <-
        (BArray1952.get8 verification_key
        (W64.to_uint verification_key_offset));
        state <-
        (BArray200.set8 state (W64.to_uint state_offset)
        ((BArray200.get8 state (W64.to_uint state_offset)) `^` byte));
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
      byte <-
      (BArray1952.get8 verification_key (W64.to_uint verification_key_offset)
      );
      state <-
      (BArray200.set8 state (W64.to_uint state_offset)
      ((BArray200.get8 state (W64.to_uint state_offset)) `^` byte));
      verification_key_offset <- (verification_key_offset + (W64.of_int 1));
      state_offset <- (state_offset + (W64.of_int 1));
    }
    state <-
    (BArray200.set8 state (W64.to_uint state_offset)
    ((BArray200.get8 state (W64.to_uint state_offset)) `^` (W8.of_int 31)));
    state <-
    (BArray200.set8 state (136 - 1)
    ((BArray200.get8 state (136 - 1)) `^` (W8.of_int 128)));
    state <@ _keccakf1600_ref1 (state);
    (* Erased call to unspill *)
    state_offset <- (W64.of_int 0);
    while ((state_offset \ult (W64.of_int 64))) {
      byte <- (BArray200.get8 state (W64.to_uint state_offset));
      hash <- (BArray64.set8 hash (W64.to_uint state_offset) byte);
      state_offset <- (state_offset + (W64.of_int 1));
    }
    return hash;
  }
  proc __shake256_consider_permute (state:BArray200.t, offset:W64.t) : 
  BArray200.t * W64.t = {
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
  proc __derive_message_representative (hash_of_verification_key:BArray64.t,
                                        message:W64.t, message_size:W64.t) : 
  BArray64.t = {
    var message_representative:BArray64.t;
    var state:BArray200.t;
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
      byte <-
      (BArray64.get8 hash_of_verification_key (W64.to_uint state_offset));
      state <- (BArray200.set8 state (W64.to_uint state_offset) byte);
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
      (BArray200.set8 state (W64.to_uint state_offset)
      ((BArray200.get8 state (W64.to_uint state_offset)) `^` byte));
      state_offset <- (state_offset + (W64.of_int 1));
    }
    (state, state_offset) <@ __shake256_consider_permute (state,
    state_offset);
    state <-
    (BArray200.set8 state (W64.to_uint state_offset)
    ((BArray200.get8 state (W64.to_uint state_offset)) `^` (W8.of_int 31)));
    (state, state_offset) <@ __shake256_consider_permute (state,
    state_offset);
    state <-
    (BArray200.set8 state (136 - 1)
    ((BArray200.get8 state (136 - 1)) `^` (W8.of_int 128)));
    state <@ _keccakf1600_ref1 (state);
    state_offset <- (W64.of_int 0);
    while ((state_offset \ult (W64.of_int 64))) {
      byte <- (BArray200.get8 state (W64.to_uint state_offset));
      message_representative <-
      (BArray64.set8 message_representative (W64.to_uint state_offset) byte);
      state_offset <- (state_offset + (W64.of_int 1));
    }
    return message_representative;
  }
  proc __derive_commitment_hash (message_representative:BArray64.t,
                                 encoded_commitment:BArray768.t) : BArray48.t = {
    var commitment_hash:BArray48.t;
    var state:BArray200.t;
    var state_offset:W64.t;
    var byte:W8.t;
    var encoded_commitment_offset:W64.t;
    commitment_hash <- witness;
    state <- witness;
    state <@ __keccak_init_ref1 (state);
    state_offset <- (W64.of_int 0);
    while ((state_offset \ult (W64.of_int 64))) {
      byte <-
      (BArray64.get8 message_representative (W64.to_uint state_offset));
      state <- (BArray200.set8 state (W64.to_uint state_offset) byte);
      state_offset <- (state_offset + (W64.of_int 1));
    }
    encoded_commitment_offset <- (W64.of_int 0);
    while ((encoded_commitment_offset \ult
           (W64.of_int (72 + ((((((4 * 256) %/ 8) * 6) - 72) %/ 136) * 136))))) {
      while ((state_offset \ult (W64.of_int 136))) {
        byte <-
        (BArray768.get8 encoded_commitment
        (W64.to_uint encoded_commitment_offset));
        encoded_commitment_offset <-
        (encoded_commitment_offset + (W64.of_int 1));
        state <-
        (BArray200.set8 state (W64.to_uint state_offset)
        ((BArray200.get8 state (W64.to_uint state_offset)) `^` byte));
        state_offset <- (state_offset + (W64.of_int 1));
      }
      (* Erased call to spill *)
      state <@ _keccakf1600_ref1 (state);
      (* Erased call to unspill *)
      state_offset <- (W64.of_int 0);
    }
    while ((encoded_commitment_offset \ult
           (W64.of_int (((4 * 256) %/ 8) * 6)))) {
      byte <-
      (BArray768.get8 encoded_commitment
      (W64.to_uint encoded_commitment_offset));
      encoded_commitment_offset <-
      (encoded_commitment_offset + (W64.of_int 1));
      state <-
      (BArray200.set8 state (W64.to_uint state_offset)
      ((BArray200.get8 state (W64.to_uint state_offset)) `^` byte));
      state_offset <- (state_offset + (W64.of_int 1));
    }
    state <-
    (BArray200.set8 state (W64.to_uint state_offset)
    ((BArray200.get8 state (W64.to_uint state_offset)) `^` (W8.of_int 31)));
    state <-
    (BArray200.set8 state (136 - 1)
    ((BArray200.get8 state (136 - 1)) `^` (W8.of_int 128)));
    state <@ _keccakf1600_ref1 (state);
    state_offset <- (W64.of_int 0);
    while ((state_offset \ult (W64.of_int 48))) {
      byte <- (BArray200.get8 state (W64.to_uint state_offset));
      commitment_hash <-
      (BArray48.set8 commitment_hash (W64.to_uint state_offset) byte);
      state_offset <- (state_offset + (W64.of_int 1));
    }
    return commitment_hash;
  }
  proc __absorb_for_shake128 (state:BArray200.t, rho:BArray32.t, i:int, j:int) : 
  BArray200.t = {
    var k:W64.t;
    var byte:W8.t;
    state <@ __keccak_init_ref1 (state);
    k <- (W64.of_int 0);
    while ((k \ult (W64.of_int 32))) {
      byte <- (BArray32.get8 rho (W64.to_uint k));
      state <- (BArray200.set8 state (W64.to_uint k) byte);
      k <- (k + (W64.of_int 1));
    }
    state <- (BArray200.set8 state 32 (W8.of_int j));
    state <- (BArray200.set8 state 33 (W8.of_int i));
    state <- (BArray200.set8 state 34 (W8.of_int 31));
    state <- (BArray200.set8 state (168 - 1) (W8.of_int 128));
    return state;
  }
  proc rejection_sample_less_than_field_modulus (result:BArray1024.t,
                                                 sampled:W64.t,
                                                 state:BArray200.t) : 
  BArray1024.t * W64.t = {
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
          (BArray200.get8 state (W64.to_uint (xof_offset + (W64.of_int k)))));
          byte <- (byte `<<` (W8.of_int (8 * k)));
          try_coefficient <- (try_coefficient `|` byte);
          k <- (k + 1);
        }
        try_coefficient <- (try_coefficient `&` (W32.of_int 8388607));
        try_coefficient <- (protect_32 try_coefficient msf);
        b <- (try_coefficient \ult (W32.of_int 8380417));
        if (b) {
          msf <- (update_msf b msf);
          result <-
          (BArray1024.set32 result (W64.to_uint sampled) try_coefficient);
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
  proc __sample_polynomial (result:BArray1024.t, rho:BArray32.t, i:int, j:int) : 
  BArray1024.t = {
    var state:BArray200.t;
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
  proc sample____matrix_A (rho:BArray32.t) : BArray30720.t = {
    var aux:BArray1024.t;
    var matrix_A:BArray30720.t;
    var j:int;
    var i:int;
    matrix_A <- witness;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 6)) {
      j <- 0;
      while ((j < 5)) {
        (* Erased call to unspill *)
        aux <@ __sample_polynomial ((SBArray30720_1024.get_sub32 matrix_A
                                    (((i * 5) + j) * 256)),
        rho, i, j);
        matrix_A <-
        (SBArray30720_1024.set_sub32 matrix_A (((i * 5) + j) * 256) aux);
        j <- (j + 1);
      }
      i <- (i + 1);
    }
    return matrix_A;
  }
  proc __absorb_to_generate_challenges (commitment_hash:BArray48.t) : 
  BArray200.t = {
    var state:BArray200.t;
    var i:int;
    var byte:W8.t;
    state <- witness;
    state <@ __keccak_init_ref1 (state);
    i <- 0;
    while ((i < 48)) {
      byte <- (BArray48.get8 commitment_hash i);
      state <- (BArray200.set8 state i byte);
      i <- (i + 1);
    }
    state <- (BArray200.set8 state 48 (W8.of_int 31));
    state <- (BArray200.set8 state (136 - 1) (W8.of_int 128));
    return state;
  }
  proc sample____challenge (output_challenge:BArray1024.t, seed:BArray48.t) : 
  BArray1024.t = {
    var state:BArray200.t;
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
      byte <- (zeroextu64 (BArray200.get8 state j));
      byte <- (byte `<<` (W8.of_int (8 * j)));
      signs <- (signs `|` byte);
      j <- (j + 1);
    }
    xof_offset <- (W64.of_int 8);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      output_challenge <-
      (BArray1024.set32 output_challenge (W64.to_uint i) (W32.of_int 0));
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
      (zeroextu64 (BArray200.get8 state (W64.to_uint xof_offset)));
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
        (zeroextu64 (BArray200.get8 state (W64.to_uint xof_offset)));
         _0 <- (init_msf);
        xof_offset <- (xof_offset + (W64.of_int 1));
      }
      coefficient <-
      (BArray1024.get32 output_challenge (W64.to_uint sample_at));
      output_challenge <-
      (BArray1024.set32 output_challenge (W64.to_uint i) coefficient);
      shift <- (truncateu32 signs);
      shift <- (shift `&` (W32.of_int 1));
      shift <- (shift `<<` (W8.of_int 1));
      coefficient <- (W32.of_int 1);
      coefficient <- (coefficient - shift);
      output_challenge <-
      (BArray1024.set32 output_challenge (W64.to_uint sample_at) coefficient);
      signs <- (signs `>>` (W8.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return output_challenge;
  }
  proc __absorb_for_shake256 (rho_prime:BArray64.t, domain_separator:W16.t) : 
  BArray200.t = {
    var state:BArray200.t;
    var v:W16.t;
    state <- witness;
    state <@ __keccak_init_ref1 (state);
    state <- (SBArray200_64.set_sub8 state 0 (copy_64 rho_prime));
    v <- domain_separator;
    v <- (v `&` (W16.of_int 255));
    state <- (BArray200.set8 state 64 (truncateu8 v));
    v <- domain_separator;
    v <- (v `>>` (W8.of_int 8));
    state <- (BArray200.set8 state 65 (truncateu8 v));
    state <-
    (BArray200.set8 state 66 ((BArray200.get8 state 66) `^` (W8.of_int 31)));
    state <-
    (BArray200.set8 state (136 - 1)
    ((BArray200.get8 state (136 - 1)) `^` (W8.of_int 128)));
    return state;
  }
  proc __sample_mask_polynomial (mask:BArray1024.t, rho_prime:BArray64.t,
                                 domain_separator:W16.t) : BArray1024.t = {
    var inc:int;
    var state:BArray200.t;
    var mask_encoded_offset:W64.t;
    var i:W64.t;
    var byte:W8.t;
    var mask_encoded:BArray680.t;
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
        byte <- (BArray200.get8 state (W64.to_uint i));
        i <- (i + (W64.of_int 1));
        mask_encoded <-
        (BArray680.set8 mask_encoded (W64.to_uint mask_encoded_offset) byte);
        mask_encoded_offset <- (mask_encoded_offset + (W64.of_int 1));
      }
      block_being_squeezed <- (block_being_squeezed + 1);
      block_being_squeezed_0 <- (block_being_squeezed_0 + 1);
    }
    mask <@ gamma1____decode_to_polynomial (mask,
    (SBArray680_640.get_sub8 mask_encoded 0));
    return mask;
  }
  proc sample____mask (rho_prime:BArray64.t, domain_separator:W16.t) : 
  BArray5120.t * W16.t = {
    var aux:BArray1024.t;
    var mask:BArray5120.t;
    var i:int;
    mask <- witness;
    i <- 0;
    while ((i < 5)) {
      aux <@ __sample_mask_polynomial ((SBArray5120_1024.get_sub32 mask
                                       (256 * i)),
      rho_prime, domain_separator);
      mask <- (SBArray5120_1024.set_sub32 mask (256 * i) aux);
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
  proc polynomial____ntt_at_layer (polynomial:BArray1024.t, zeta_i:W64.t,
                                   lAYER:int) : BArray1024.t * W64.t = {
    var sTEP:int;
    var rOUNDS:int;
    var zetas:BArray1024.t;
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
        (sigextu64
        (BArray1024.get32 polynomial
        (W64.to_uint (offset + (W64.of_int sTEP)))));
        zeta_0 <- (sigextu64 (BArray1024.get32 zetas (W64.to_uint zeta_i)));
        t64 <- (t64 * zeta_0);
        t <@ __montgomery_reduce (t64);
        left_0 <- (BArray1024.get32 polynomial (W64.to_uint offset));
        left_0 <- (left_0 - t);
        polynomial <-
        (BArray1024.set32 polynomial
        (W64.to_uint (offset + (W64.of_int sTEP))) left_0);
        left_0 <- (BArray1024.get32 polynomial (W64.to_uint offset));
        left_0 <- (left_0 + t);
        polynomial <-
        (BArray1024.set32 polynomial (W64.to_uint offset) left_0);
        offset <- (offset + (W64.of_int 1));
      }
      round <- (round + (W64.of_int 1));
    }
    return (polynomial, zeta_i);
  }
  proc polynomial__ntt (polynomial:BArray1024.t) : BArray1024.t = {
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
  proc polynomial____invert_ntt_at_layer (polynomial:BArray1024.t,
                                          zeta_i:W64.t, lAYER:int) : 
  BArray1024.t * W64.t = {
    var sTEP:int;
    var rOUNDS:int;
    var zetas:BArray1024.t;
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
        t <-
        (BArray1024.get32 polynomial
        (W64.to_uint (offset + (W64.of_int sTEP))));
        t <- (t - (BArray1024.get32 polynomial (W64.to_uint offset)));
        left_0 <- (BArray1024.get32 polynomial (W64.to_uint offset));
        right_0 <-
        (BArray1024.get32 polynomial
        (W64.to_uint (offset + (W64.of_int sTEP))));
        left_0 <- (left_0 + right_0);
        polynomial <-
        (BArray1024.set32 polynomial (W64.to_uint offset) left_0);
        zeta_0 <- (sigextu64 (BArray1024.get32 zetas (W64.to_uint zeta_i)));
        t64 <- (sigextu64 t);
        t64 <- (t64 * zeta_0);
        t <@ __montgomery_reduce (t64);
        polynomial <-
        (BArray1024.set32 polynomial
        (W64.to_uint (offset + (W64.of_int sTEP))) t);
        offset <- (offset + (W64.of_int 1));
      }
      round <- (round + (W64.of_int 1));
    }
    return (polynomial, zeta_i);
  }
  proc polynomial__invert_ntt_montgomery (polynomial:BArray1024.t) : 
  BArray1024.t = {
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
      coefficient64 <-
      (sigextu64 (BArray1024.get32 polynomial (W64.to_uint j)));
      coefficient64 <- (coefficient64 * (W64.of_int 41978));
      coefficient <@ __montgomery_reduce (coefficient64);
      polynomial <-
      (BArray1024.set32 polynomial (W64.to_uint j) coefficient);
      j <- (j + (W64.of_int 1));
    }
    return polynomial;
  }
  proc polynomial__add (sum:BArray1024.t, lhs:BArray1024.t, rhs:BArray1024.t) : 
  BArray1024.t = {
    var i:W64.t;
    var lhs_coefficient:W32.t;
    var rhs_coefficient:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      lhs_coefficient <- (BArray1024.get32 lhs (W64.to_uint i));
      rhs_coefficient <- (BArray1024.get32 rhs (W64.to_uint i));
      lhs_coefficient <- (lhs_coefficient + rhs_coefficient);
      sum <- (BArray1024.set32 sum (W64.to_uint i) lhs_coefficient);
      i <- (i + (W64.of_int 1));
    }
    return sum;
  }
  proc polynomial__subtract (difference:BArray1024.t, lhs:BArray1024.t,
                             rhs:BArray1024.t) : BArray1024.t = {
    var i:W64.t;
    var lhs_coefficient:W32.t;
    var rhs_coefficient:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      lhs_coefficient <- (BArray1024.get32 lhs (W64.to_uint i));
      rhs_coefficient <- (BArray1024.get32 rhs (W64.to_uint i));
      lhs_coefficient <- (lhs_coefficient - rhs_coefficient);
      difference <-
      (BArray1024.set32 difference (W64.to_uint i) lhs_coefficient);
      i <- (i + (W64.of_int 1));
    }
    return difference;
  }
  proc polynomial____pointwise_add_to_total (total:BArray1024.t,
                                             polynomial:BArray1024.t) : 
  BArray1024.t = {
    var i:W64.t;
    var coefficient:W32.t;
    var running_total:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      coefficient <- (BArray1024.get32 polynomial (W64.to_uint i));
      running_total <- (BArray1024.get32 total (W64.to_uint i));
      running_total <- (running_total + coefficient);
      total <- (BArray1024.set32 total (W64.to_uint i) running_total);
      i <- (i + (W64.of_int 1));
    }
    return total;
  }
  proc polynomial__pointwise_montgomery_product (product:BArray1024.t,
                                                 lhs:BArray1024.t,
                                                 rhs:BArray1024.t) : 
  BArray1024.t = {
    var i:W64.t;
    var lhs_coefficient:W64.t;
    var rhs_coefficient:W64.t;
    var product_reduced:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      lhs_coefficient <- (sigextu64 (BArray1024.get32 lhs (W64.to_uint i)));
      rhs_coefficient <- (sigextu64 (BArray1024.get32 rhs (W64.to_uint i)));
      lhs_coefficient <- (lhs_coefficient * rhs_coefficient);
      product_reduced <@ __montgomery_reduce (lhs_coefficient);
      product <- (BArray1024.set32 product (W64.to_uint i) product_reduced);
      i <- (i + (W64.of_int 1));
    }
    return product;
  }
  proc polynomial____zero (polynomial:BArray1024.t) : BArray1024.t = {
    var i:W64.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      polynomial <-
      (BArray1024.set32 polynomial (W64.to_uint i) (W32.of_int 0));
      i <- (i + (W64.of_int 1));
    }
    return polynomial;
  }
  proc polynomial__conditionally_add_modulus (polynomial:BArray1024.t) : 
  BArray1024.t = {
    var i:W64.t;
    var coefficient:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      coefficient <- (BArray1024.get32 polynomial (W64.to_uint i));
      coefficient <@ coefficient____conditionally_add_modulus (coefficient);
      polynomial <-
      (BArray1024.set32 polynomial (W64.to_uint i) coefficient);
      i <- (i + (W64.of_int 1));
    }
    return polynomial;
  }
  proc polynomial____check_infinity_norm (polynomial:BArray1024.t,
                                          threshold:int) : W8.t = {
    var result:W8.t;
    var i:W64.t;
    var coefficient:W32.t;
    var ret:W8.t;
    result <- (W8.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      coefficient <- (BArray1024.get32 polynomial (W64.to_uint i));
      ret <@ coefficient____check_norm (coefficient, threshold);
      result <- (result `|` ret);
      i <- (i + (W64.of_int 1));
    }
    return result;
  }
  proc polynomial____make_hint (hints:BArray1024.t, f0:BArray1024.t,
                                f1:BArray1024.t) : BArray1024.t * W32.t = {
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
      a0 <- (BArray1024.get32 f0 (W64.to_uint i));
      a0 <- (protect_32 a0 msf);
      a1 <- (BArray1024.get32 f1 (W64.to_uint i));
      a1 <- (protect_32 a1 msf);
      (hint_0, msf) <@ coefficient____make_hint (a0, a1, msf);
      hints <- (BArray1024.set32 hints (W64.to_uint i) hint_0);
      weight <- (weight + hint_0);
      i <- (i + (W64.of_int 1));
      condition <- (i \ult (W64.of_int 256));
    }
    return (hints, weight);
  }
  proc polynomial__reduce32 (polynomial:BArray1024.t) : BArray1024.t = {
    var i:W64.t;
    var coeff:W32.t;
    var reduced:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      coeff <- (BArray1024.get32 polynomial (W64.to_uint i));
      reduced <@ coefficient____reduce32 (coeff);
      polynomial <- (BArray1024.set32 polynomial (W64.to_uint i) reduced);
      i <- (i + (W64.of_int 1));
    }
    return polynomial;
  }
  proc polynomial____shift_coefficients_left (polynomial:BArray1024.t) : 
  BArray1024.t = {
    var i:W64.t;
    var coefficient:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 256))) {
      coefficient <- (BArray1024.get32 polynomial (W64.to_uint i));
      coefficient <- (coefficient `<<` (W8.of_int 13));
      polynomial <-
      (BArray1024.set32 polynomial (W64.to_uint i) coefficient);
      i <- (i + (W64.of_int 1));
    }
    return polynomial;
  }
  proc polynomial__use_hints (commitment:BArray1024.t, hints:BArray1024.t) : 
  BArray1024.t = {
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
      h <- (BArray1024.get32 hints (W64.to_uint i));
      h <- (protect_32 h msf);
      a <- (BArray1024.get32 commitment (W64.to_uint i));
      a <- (protect_32 a msf);
      (a, msf) <@ coefficient____use_hint (a, h, msf);
      commitment <- (BArray1024.set32 commitment (W64.to_uint i) a);
      i <- (i + (W64.of_int 1));
      b <- (i \ult (W64.of_int 256));
    }
    return commitment;
  }
  proc row_vector__ntt (vector:BArray5120.t) : BArray5120.t = {
    var aux:BArray1024.t;
    var i:int;
    i <- 0;
    while ((i < 5)) {
      aux <@ polynomial__ntt ((SBArray5120_1024.get_sub32 vector (i * 256)));
      vector <- (SBArray5120_1024.set_sub32 vector (i * 256) aux);
      i <- (i + 1);
    }
    return vector;
  }
  proc row_vector__invert_ntt_montgomery (vector:BArray5120.t) : BArray5120.t = {
    var aux:BArray1024.t;
    var i:int;
    i <- 0;
    while ((i < 5)) {
      aux <@ polynomial__invert_ntt_montgomery ((SBArray5120_1024.get_sub32
                                                vector (i * 256)));
      vector <- (SBArray5120_1024.set_sub32 vector (i * 256) aux);
      i <- (i + 1);
    }
    return vector;
  }
  proc row_vector____add (lhs:BArray5120.t, rhs:BArray5120.t) : BArray5120.t = {
    var aux:BArray1024.t;
    var sum:BArray5120.t;
    var i:int;
    sum <- witness;
    i <- 0;
    while ((i < 5)) {
      aux <@ polynomial__add ((SBArray5120_1024.get_sub32 sum (256 * i)),
      (SBArray5120_1024.get_sub32 lhs (256 * i)),
      (SBArray5120_1024.get_sub32 rhs (256 * i)));
      sum <- (SBArray5120_1024.set_sub32 sum (256 * i) aux);
      i <- (i + 1);
    }
    return sum;
  }
  proc row_vector____dot_product (output:BArray1024.t, lhs:BArray5120.t,
                                  rhs:BArray5120.t) : BArray1024.t = {
    var product:BArray1024.t;
    var i:int;
    product <- witness;
    output <@ polynomial____zero (output);
    (* Erased call to spill *)
    i <- 0;
    while ((i < 5)) {
      (* Erased call to unspill *)
      product <@ polynomial__pointwise_montgomery_product (product,
      (SBArray5120_1024.get_sub32 lhs (256 * i)),
      (SBArray5120_1024.get_sub32 rhs (256 * i)));
      (* Erased call to unspill *)
      output <@ polynomial____pointwise_add_to_total (output, product);
      (* Erased call to spill *)
      i <- (i + 1);
    }
    return output;
  }
  proc row_vector____multiply_by_polynomial (vector:BArray5120.t,
                                             poly:BArray1024.t) : BArray5120.t = {
    var aux:BArray1024.t;
    var product:BArray5120.t;
    var i:int;
    product <- witness;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 5)) {
      aux <@ polynomial__pointwise_montgomery_product ((
                                                       SBArray5120_1024.get_sub32
                                                       product (i * 256)),
      (SBArray5120_1024.get_sub32 vector (i * 256)), poly);
      product <- (SBArray5120_1024.set_sub32 product (i * 256) aux);
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return product;
  }
  proc row_vector____multiply_with_matrix_A (matrix_A:BArray30720.t,
                                             vector:BArray5120.t) : BArray6144.t = {
    var aux:BArray1024.t;
    var out:BArray6144.t;
    var i:int;
    out <- witness;
    i <- 0;
    while ((i < 6)) {
      aux <@ row_vector____dot_product ((SBArray6144_1024.get_sub32 out
                                        (256 * i)),
      (SBArray30720_5120.get_sub32 matrix_A ((5 * 256) * i)), vector);
      out <- (SBArray6144_1024.set_sub32 out (256 * i) aux);
      i <- (i + 1);
    }
    return out;
  }
  proc row_vector__reduce32 (vector:BArray5120.t) : BArray5120.t = {
    var aux:BArray1024.t;
    var i:int;
    i <- 0;
    while ((i < 5)) {
      aux <@ polynomial__reduce32 ((SBArray5120_1024.get_sub32 vector
                                   (i * 256)));
      vector <- (SBArray5120_1024.set_sub32 vector (i * 256) aux);
      i <- (i + 1);
    }
    return vector;
  }
  proc row_vector____check_infinity_norm (vector:BArray5120.t, threshold:int) : 
  W8.t = {
    var result:W8.t;
    var i:int;
    var vector_element:BArray1024.t;
    var ret:W8.t;
    vector_element <- witness;
    result <- (W8.of_int 0);
    i <- 0;
    while ((i < 5)) {
      vector_element <- (SBArray5120_1024.get_sub32 vector (i * 256));
      ret <@ polynomial____check_infinity_norm (vector_element, threshold);
      result <- (result `|` ret);
      i <- (i + 1);
    }
    return result;
  }
  proc column_vector__reduce32 (vector:BArray6144.t) : BArray6144.t = {
    var aux:BArray1024.t;
    var i:int;
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__reduce32 ((SBArray6144_1024.get_sub32 vector
                                   (i * 256)));
      vector <- (SBArray6144_1024.set_sub32 vector (i * 256) aux);
      i <- (i + 1);
    }
    return vector;
  }
  proc column_vector__ntt (vector:BArray6144.t) : BArray6144.t = {
    var aux:BArray1024.t;
    var i:int;
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__ntt ((SBArray6144_1024.get_sub32 vector (i * 256)));
      vector <- (SBArray6144_1024.set_sub32 vector (i * 256) aux);
      i <- (i + 1);
    }
    return vector;
  }
  proc column_vector__invert_ntt_montgomery (vector:BArray6144.t) : BArray6144.t = {
    var aux:BArray1024.t;
    var i:int;
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__invert_ntt_montgomery ((SBArray6144_1024.get_sub32
                                                vector (i * 256)));
      vector <- (SBArray6144_1024.set_sub32 vector (i * 256) aux);
      i <- (i + 1);
    }
    return vector;
  }
  proc column_vector____power2round (v:BArray6144.t) : BArray6144.t *
                                                       BArray6144.t = {
    var t1:BArray6144.t;
    var t0:BArray6144.t;
    var i:W64.t;
    var x:W32.t;
    var y1:W32.t;
    var y2:W32.t;
    t0 <- witness;
    t1 <- witness;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (6 * 256)))) {
      x <- (BArray6144.get32 v (W64.to_uint i));
      (* Erased call to spill *)
      (y1, y2) <@ coefficient____power2round (x);
      (* Erased call to unspill *)
      t1 <- (BArray6144.set32 t1 (W64.to_uint i) y1);
      t0 <- (BArray6144.set32 t0 (W64.to_uint i) y2);
      i <- (i + (W64.of_int 1));
    }
    return (t1, t0);
  }
  proc column_vector____add (lhs:BArray6144.t, rhs:BArray6144.t) : BArray6144.t = {
    var aux:BArray1024.t;
    var sum:BArray6144.t;
    var i:int;
    sum <- witness;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__add ((SBArray6144_1024.get_sub32 sum (256 * i)),
      (SBArray6144_1024.get_sub32 lhs (256 * i)),
      (SBArray6144_1024.get_sub32 rhs (256 * i)));
      sum <- (SBArray6144_1024.set_sub32 sum (256 * i) aux);
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return sum;
  }
  proc column_vector____conditionally_add_modulus (vector:BArray6144.t) : 
  BArray6144.t = {
    var aux:BArray1024.t;
    var i:int;
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__conditionally_add_modulus ((
                                                    SBArray6144_1024.get_sub32
                                                    vector (i * 256)));
      vector <- (SBArray6144_1024.set_sub32 vector (i * 256) aux);
      i <- (i + 1);
    }
    return vector;
  }
  proc column_vector____decompose (vector:BArray6144.t) : BArray6144.t *
                                                          BArray6144.t = {
    var low:BArray6144.t;
    var high:BArray6144.t;
    var i:W64.t;
    var coefficient:W32.t;
    var low_bits:W32.t;
    var high_bits:W32.t;
    high <- witness;
    low <- witness;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (6 * 256)))) {
      coefficient <- (BArray6144.get32 vector (W64.to_uint i));
      (low_bits, high_bits) <@ coefficient____decompose (coefficient);
      low <- (BArray6144.set32 low (W64.to_uint i) low_bits);
      high <- (BArray6144.set32 high (W64.to_uint i) high_bits);
      i <- (i + (W64.of_int 1));
    }
    return (low, high);
  }
  proc column_vector____multiply_by_polynomial (vector:BArray6144.t,
                                                poly:BArray1024.t) : 
  BArray6144.t = {
    var aux:BArray1024.t;
    var product:BArray6144.t;
    var i:int;
    product <- witness;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__pointwise_montgomery_product ((
                                                       SBArray6144_1024.get_sub32
                                                       product (i * 256)),
      (SBArray6144_1024.get_sub32 vector (i * 256)), poly);
      product <- (SBArray6144_1024.set_sub32 product (i * 256) aux);
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return product;
  }
  proc column_vector____subtract (lhs:BArray6144.t, rhs:BArray6144.t) : 
  BArray6144.t = {
    var aux:BArray1024.t;
    var difference:BArray6144.t;
    var i:int;
    difference <- witness;
    i <- 0;
    while ((i < 6)) {
      aux <@ polynomial__subtract ((SBArray6144_1024.get_sub32 difference
                                   (256 * i)),
      (SBArray6144_1024.get_sub32 lhs (256 * i)),
      (SBArray6144_1024.get_sub32 rhs (256 * i)));
      difference <- (SBArray6144_1024.set_sub32 difference (256 * i) aux);
      i <- (i + 1);
    }
    return difference;
  }
  proc column_vector____check_infinity_norm (vector:BArray6144.t,
                                             threshold:int) : W8.t = {
    var result:W8.t;
    var i:int;
    var ret:W8.t;
    result <- (W8.of_int 0);
    i <- 0;
    while ((i < 6)) {
      ret <@ polynomial____check_infinity_norm ((SBArray6144_1024.get_sub32
                                                vector (i * 256)),
      threshold);
      result <- (result `|` ret);
      i <- (i + 1);
    }
    return result;
  }
  proc column_vector____make_hint (addend:BArray6144.t, original:BArray6144.t) : 
  BArray6144.t * W32.t = {
    var aux:BArray1024.t;
    var aux_0:W32.t;
    var hint_vector:BArray6144.t;
    var ones_in_hint_vector:W32.t;
    var i:int;
    var ones_in_hint:W32.t;
    hint_vector <- witness;
    ones_in_hint_vector <- (W32.of_int 0);
    i <- 0;
    while ((i < 6)) {
      (aux, aux_0) <@ polynomial____make_hint ((SBArray6144_1024.get_sub32
                                               hint_vector (i * 256)),
      (SBArray6144_1024.get_sub32 addend (i * 256)),
      (SBArray6144_1024.get_sub32 original (i * 256)));
      hint_vector <- (SBArray6144_1024.set_sub32 hint_vector (i * 256) aux);
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
  proc t0__encode_polynomial (encoded:BArray416.t, t0:BArray1024.t) : 
  BArray416.t = {
    var encoded_offset:W64.t;
    var t0_offset:W64.t;
    var i:W64.t;
    var coefficient:W32.t;
    var t:BArray32.t;
    var c:W8.t;
    var c1:W8.t;
    t <- witness;
    encoded_offset <- (W64.of_int 0);
    t0_offset <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (256 %/ 8)))) {
      coefficient <- (BArray1024.get32 t0 (W64.to_uint t0_offset));
      t0_offset <- (t0_offset + (W64.of_int 1));
      coefficient <@ t0__change_t0_interval (coefficient);
      t <- (BArray32.set32 t 0 coefficient);
      c <- (truncateu8 coefficient);
      encoded <- (BArray416.set8 encoded (W64.to_uint encoded_offset) c);
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- (BArray32.get32 t 0);
      coefficient <- (coefficient `>>` (W8.of_int 8));
      c <- (truncateu8 coefficient);
      coefficient <- (BArray1024.get32 t0 (W64.to_uint t0_offset));
      t0_offset <- (t0_offset + (W64.of_int 1));
      coefficient <@ t0__change_t0_interval (coefficient);
      t <- (BArray32.set32 t 1 coefficient);
      coefficient <- (coefficient `<<` (W8.of_int 5));
      c1 <- (truncateu8 coefficient);
      c <- (c `|` c1);
      encoded <- (BArray416.set8 encoded (W64.to_uint encoded_offset) c);
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- (BArray32.get32 t 1);
      coefficient <- (coefficient `>>` (W8.of_int 3));
      c <- (truncateu8 coefficient);
      encoded <- (BArray416.set8 encoded (W64.to_uint encoded_offset) c);
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- (BArray32.get32 t 1);
      coefficient <- (coefficient `>>` (W8.of_int 11));
      c <- (truncateu8 coefficient);
      coefficient <- (BArray1024.get32 t0 (W64.to_uint t0_offset));
      t0_offset <- (t0_offset + (W64.of_int 1));
      coefficient <@ t0__change_t0_interval (coefficient);
      t <- (BArray32.set32 t 2 coefficient);
      coefficient <- (coefficient `<<` (W8.of_int 2));
      c1 <- (truncateu8 coefficient);
      c <- (c `|` c1);
      encoded <- (BArray416.set8 encoded (W64.to_uint encoded_offset) c);
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- (BArray32.get32 t 2);
      coefficient <- (coefficient `>>` (W8.of_int 6));
      c <- (truncateu8 coefficient);
      coefficient <- (BArray1024.get32 t0 (W64.to_uint t0_offset));
      t0_offset <- (t0_offset + (W64.of_int 1));
      coefficient <@ t0__change_t0_interval (coefficient);
      t <- (BArray32.set32 t 3 coefficient);
      coefficient <- (coefficient `<<` (W8.of_int 7));
      c1 <- (truncateu8 coefficient);
      c <- (c `|` c1);
      encoded <- (BArray416.set8 encoded (W64.to_uint encoded_offset) c);
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- (BArray32.get32 t 3);
      coefficient <- (coefficient `>>` (W8.of_int 1));
      c <- (truncateu8 coefficient);
      encoded <- (BArray416.set8 encoded (W64.to_uint encoded_offset) c);
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- (BArray32.get32 t 3);
      coefficient <- (coefficient `>>` (W8.of_int 9));
      c <- (truncateu8 coefficient);
      coefficient <- (BArray1024.get32 t0 (W64.to_uint t0_offset));
      t0_offset <- (t0_offset + (W64.of_int 1));
      coefficient <@ t0__change_t0_interval (coefficient);
      t <- (BArray32.set32 t 4 coefficient);
      coefficient <- (coefficient `<<` (W8.of_int 4));
      c1 <- (truncateu8 coefficient);
      c <- (c `|` c1);
      encoded <- (BArray416.set8 encoded (W64.to_uint encoded_offset) c);
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- (BArray32.get32 t 4);
      coefficient <- (coefficient `>>` (W8.of_int 4));
      c <- (truncateu8 coefficient);
      encoded <- (BArray416.set8 encoded (W64.to_uint encoded_offset) c);
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- (BArray32.get32 t 4);
      coefficient <- (coefficient `>>` (W8.of_int 12));
      c <- (truncateu8 coefficient);
      coefficient <- (BArray1024.get32 t0 (W64.to_uint t0_offset));
      t0_offset <- (t0_offset + (W64.of_int 1));
      coefficient <@ t0__change_t0_interval (coefficient);
      t <- (BArray32.set32 t 5 coefficient);
      coefficient <- (coefficient `<<` (W8.of_int 1));
      c1 <- (truncateu8 coefficient);
      c <- (c `|` c1);
      encoded <- (BArray416.set8 encoded (W64.to_uint encoded_offset) c);
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- (BArray32.get32 t 5);
      coefficient <- (coefficient `>>` (W8.of_int 7));
      c <- (truncateu8 coefficient);
      coefficient <- (BArray1024.get32 t0 (W64.to_uint t0_offset));
      t0_offset <- (t0_offset + (W64.of_int 1));
      coefficient <@ t0__change_t0_interval (coefficient);
      t <- (BArray32.set32 t 6 coefficient);
      coefficient <- (coefficient `<<` (W8.of_int 6));
      c1 <- (truncateu8 coefficient);
      c <- (c `|` c1);
      encoded <- (BArray416.set8 encoded (W64.to_uint encoded_offset) c);
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- (BArray32.get32 t 6);
      coefficient <- (coefficient `>>` (W8.of_int 2));
      c <- (truncateu8 coefficient);
      encoded <- (BArray416.set8 encoded (W64.to_uint encoded_offset) c);
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- (BArray32.get32 t 6);
      coefficient <- (coefficient `>>` (W8.of_int 10));
      c <- (truncateu8 coefficient);
      coefficient <- (BArray1024.get32 t0 (W64.to_uint t0_offset));
      t0_offset <- (t0_offset + (W64.of_int 1));
      coefficient <@ t0__change_t0_interval (coefficient);
      t <- (BArray32.set32 t 7 coefficient);
      coefficient <- (coefficient `<<` (W8.of_int 3));
      c1 <- (truncateu8 coefficient);
      c <- (c `|` c1);
      encoded <- (BArray416.set8 encoded (W64.to_uint encoded_offset) c);
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      coefficient <- (BArray32.get32 t 7);
      coefficient <- (coefficient `>>` (W8.of_int 5));
      c <- (truncateu8 coefficient);
      encoded <- (BArray416.set8 encoded (W64.to_uint encoded_offset) c);
      encoded_offset <- (encoded_offset + (W64.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return encoded;
  }
  proc t0____encode (encoded:BArray2496.t, t0:BArray6144.t) : BArray2496.t = {
    var aux:BArray416.t;
    var j:int;
    (* Erased call to spill *)
    j <- 0;
    while ((j < 6)) {
      aux <@ t0__encode_polynomial ((SBArray2496_416.get_sub8 encoded
                                    (j * ((13 * 256) %/ 8))),
      (SBArray6144_1024.get_sub32 t0 (256 * j)));
      encoded <-
      (SBArray2496_416.set_sub8 encoded (j * ((13 * 256) %/ 8)) aux);
      (* Erased call to unspill *)
      j <- (j + 1);
    }
    return encoded;
  }
  proc t0____decode_polynomial (t0:BArray1024.t, src:BArray416.t) : BArray1024.t = {
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
      coefficient <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      encoded_byte <- (encoded_byte `<<` (W8.of_int 8));
      coefficient <- (coefficient `|` encoded_byte);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 13) - 1)));
      coefficient <@ t0__change_t0_interval (coefficient);
      t0 <- (BArray1024.set32 t0 (W64.to_uint output_offset) coefficient);
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      coefficient <- (coefficient `>>` (W8.of_int 5));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      encoded_byte <- (encoded_byte `<<` (W8.of_int 3));
      coefficient <- (coefficient `|` encoded_byte);
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      encoded_byte <- (encoded_byte `<<` (W8.of_int 11));
      coefficient <- (coefficient `|` encoded_byte);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 13) - 1)));
      coefficient <@ t0__change_t0_interval (coefficient);
      t0 <- (BArray1024.set32 t0 (W64.to_uint output_offset) coefficient);
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      coefficient <- (coefficient `>>` (W8.of_int 2));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      encoded_byte <- (encoded_byte `<<` (W8.of_int 6));
      coefficient <- (coefficient `|` encoded_byte);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 13) - 1)));
      coefficient <@ t0__change_t0_interval (coefficient);
      t0 <- (BArray1024.set32 t0 (W64.to_uint output_offset) coefficient);
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      coefficient <- (coefficient `>>` (W8.of_int 7));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      encoded_byte <- (encoded_byte `<<` (W8.of_int 1));
      coefficient <- (coefficient `|` encoded_byte);
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      encoded_byte <- (encoded_byte `<<` (W8.of_int 9));
      coefficient <- (coefficient `|` encoded_byte);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 13) - 1)));
      coefficient <@ t0__change_t0_interval (coefficient);
      t0 <- (BArray1024.set32 t0 (W64.to_uint output_offset) coefficient);
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      coefficient <- (coefficient `>>` (W8.of_int 4));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      encoded_byte <- (encoded_byte `<<` (W8.of_int 4));
      coefficient <- (coefficient `|` encoded_byte);
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      encoded_byte <- (encoded_byte `<<` (W8.of_int 12));
      coefficient <- (coefficient `|` encoded_byte);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 13) - 1)));
      coefficient <@ t0__change_t0_interval (coefficient);
      t0 <- (BArray1024.set32 t0 (W64.to_uint output_offset) coefficient);
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      coefficient <- (coefficient `>>` (W8.of_int 1));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      encoded_byte <- (encoded_byte `<<` (W8.of_int 7));
      coefficient <- (coefficient `|` encoded_byte);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 13) - 1)));
      coefficient <@ t0__change_t0_interval (coefficient);
      t0 <- (BArray1024.set32 t0 (W64.to_uint output_offset) coefficient);
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      coefficient <- (coefficient `>>` (W8.of_int 6));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      encoded_byte <- (encoded_byte `<<` (W8.of_int 2));
      coefficient <- (coefficient `|` encoded_byte);
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      encoded_byte <- (encoded_byte `<<` (W8.of_int 10));
      coefficient <- (coefficient `|` encoded_byte);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 13) - 1)));
      coefficient <@ t0__change_t0_interval (coefficient);
      t0 <- (BArray1024.set32 t0 (W64.to_uint output_offset) coefficient);
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      coefficient <- (coefficient `>>` (W8.of_int 3));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <-
      (zeroextu32 (BArray416.get8 src (W64.to_uint input_offset)));
      encoded_byte <- (encoded_byte `<<` (W8.of_int 5));
      coefficient <- (coefficient `|` encoded_byte);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 13) - 1)));
      coefficient <@ t0__change_t0_interval (coefficient);
      t0 <- (BArray1024.set32 t0 (W64.to_uint output_offset) coefficient);
      output_offset <- (output_offset + (W64.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return t0;
  }
  proc t0____decode (t0:BArray6144.t, encoded:BArray2496.t) : BArray6144.t = {
    var aux:BArray1024.t;
    var i:int;
    i <- 0;
    while ((i < 6)) {
      aux <@ t0____decode_polynomial ((SBArray6144_1024.get_sub32 t0
                                      (i * 256)),
      (SBArray2496_416.get_sub8 encoded (((13 * 256) %/ 8) * i)));
      t0 <- (SBArray6144_1024.set_sub32 t0 (i * 256) aux);
      i <- (i + 1);
    }
    return t0;
  }
  proc t1__encode_polynomial (encoded:BArray320.t, t1:BArray1024.t) : 
  BArray320.t = {
    var input_offset:W64.t;
    var output_offset:W64.t;
    var i:W64.t;
    var encoded_bytes:W32.t;
    var encoded_byte:W32.t;
    input_offset <- (W64.of_int 0);
    output_offset <- (W64.of_int 0);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (256 %/ 4)))) {
      encoded_bytes <- (BArray1024.get32 t1 (W64.to_uint input_offset));
      encoded <-
      (BArray320.set8 encoded (W64.to_uint output_offset)
      (truncateu8 encoded_bytes));
      output_offset <- (output_offset + (W64.of_int 1));
      encoded_bytes <- (BArray1024.get32 t1 (W64.to_uint input_offset));
      encoded_bytes <- (encoded_bytes `>>` (W8.of_int 8));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- (BArray1024.get32 t1 (W64.to_uint input_offset));
      encoded_byte <- (encoded_byte `<<` (W8.of_int 2));
      encoded_bytes <- (encoded_bytes `|` encoded_byte);
      encoded <-
      (BArray320.set8 encoded (W64.to_uint output_offset)
      (truncateu8 encoded_bytes));
      output_offset <- (output_offset + (W64.of_int 1));
      encoded_bytes <- (BArray1024.get32 t1 (W64.to_uint input_offset));
      encoded_bytes <- (encoded_bytes `>>` (W8.of_int 6));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- (BArray1024.get32 t1 (W64.to_uint input_offset));
      encoded_byte <- (encoded_byte `<<` (W8.of_int 4));
      encoded_bytes <- (encoded_bytes `|` encoded_byte);
      encoded <-
      (BArray320.set8 encoded (W64.to_uint output_offset)
      (truncateu8 encoded_bytes));
      output_offset <- (output_offset + (W64.of_int 1));
      encoded_bytes <- (BArray1024.get32 t1 (W64.to_uint input_offset));
      encoded_bytes <- (encoded_bytes `>>` (W8.of_int 4));
      input_offset <- (input_offset + (W64.of_int 1));
      encoded_byte <- (BArray1024.get32 t1 (W64.to_uint input_offset));
      encoded_byte <- (encoded_byte `<<` (W8.of_int 6));
      encoded_bytes <- (encoded_bytes `|` encoded_byte);
      encoded <-
      (BArray320.set8 encoded (W64.to_uint output_offset)
      (truncateu8 encoded_bytes));
      output_offset <- (output_offset + (W64.of_int 1));
      encoded_bytes <- (BArray1024.get32 t1 (W64.to_uint input_offset));
      encoded_bytes <- (encoded_bytes `>>` (W8.of_int 2));
      encoded <-
      (BArray320.set8 encoded (W64.to_uint output_offset)
      (truncateu8 encoded_bytes));
      output_offset <- (output_offset + (W64.of_int 1));
      input_offset <- (input_offset + (W64.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return encoded;
  }
  proc t1____encode (encoded:BArray1920.t, t1:BArray6144.t) : BArray1920.t = {
    var aux:BArray320.t;
    var j:int;
    (* Erased call to spill *)
    j <- 0;
    while ((j < 6)) {
      aux <@ t1__encode_polynomial ((SBArray1920_320.get_sub8 encoded
                                    (j * (((23 - 13) * 256) %/ 8))),
      (SBArray6144_1024.get_sub32 t1 (256 * j)));
      encoded <-
      (SBArray1920_320.set_sub8 encoded (j * (((23 - 13) * 256) %/ 8)) aux);
      (* Erased call to unspill *)
      j <- (j + 1);
    }
    return encoded;
  }
  proc t1__decode_polynomial (t1:BArray1024.t, encoded:BArray320.t) : 
  BArray1024.t = {
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
      coefficient <-
      (zeroextu32 (BArray320.get8 encoded (W64.to_uint input_offset)));
      input_offset <- (input_offset + (W64.of_int 1));
      temp1 <-
      (zeroextu32 (BArray320.get8 encoded (W64.to_uint input_offset)));
      input_offset <- (input_offset + (W64.of_int 1));
      temp2 <- temp1;
      temp1 <- (temp1 `<<` (W8.of_int 8));
      coefficient <- (coefficient `|` temp1);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 10) - 1)));
      t1 <- (BArray1024.set32 t1 (W64.to_uint output_offset) coefficient);
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <- (temp2 `>>` (W8.of_int 2));
      temp1 <-
      (zeroextu32 (BArray320.get8 encoded (W64.to_uint input_offset)));
      input_offset <- (input_offset + (W64.of_int 1));
      temp2 <- temp1;
      temp1 <- (temp1 `<<` (W8.of_int 6));
      coefficient <- (coefficient `|` temp1);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 10) - 1)));
      t1 <- (BArray1024.set32 t1 (W64.to_uint output_offset) coefficient);
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <- (temp2 `>>` (W8.of_int 4));
      temp1 <-
      (zeroextu32 (BArray320.get8 encoded (W64.to_uint input_offset)));
      input_offset <- (input_offset + (W64.of_int 1));
      temp2 <- temp1;
      temp1 <- (temp1 `<<` (W8.of_int 4));
      coefficient <- (coefficient `|` temp1);
      coefficient <- (coefficient `&` (W32.of_int ((1 `<<` 10) - 1)));
      t1 <- (BArray1024.set32 t1 (W64.to_uint output_offset) coefficient);
      output_offset <- (output_offset + (W64.of_int 1));
      coefficient <- (temp2 `>>` (W8.of_int 6));
      temp1 <-
      (zeroextu32 (BArray320.get8 encoded (W64.to_uint input_offset)));
      input_offset <- (input_offset + (W64.of_int 1));
      temp1 <- (temp1 `<<` (W8.of_int 2));
      coefficient <- (coefficient `|` temp1);
      t1 <- (BArray1024.set32 t1 (W64.to_uint output_offset) coefficient);
      output_offset <- (output_offset + (W64.of_int 1));
      i <- (i + (W64.of_int 1));
    }
    return t1;
  }
  proc signature____encode (signature:BArray3309.t,
                            commitment_hash:BArray48.t,
                            signer_response:BArray5120.t, hint_0:BArray6144.t) : 
  BArray3309.t = {
    var i:W64.t;
    var k:int;
    var polynomial_encoded:BArray640.t;
    var polynomial:BArray1024.t;
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
      signature <-
      (BArray3309.set8 signature (W64.to_uint i)
      (BArray48.get8 commitment_hash (W64.to_uint i)));
      i <- (i + (W64.of_int 1));
    }
    k <- 0;
    while ((k < 5)) {
      polynomial_encoded <-
      (SBArray3309_640.get_sub8 signature (48 + (k * ((20 * 256) %/ 8))));
      polynomial <- (SBArray5120_1024.get_sub32 signer_response (k * 256));
      polynomial_encoded <@ gamma1____encode_polynomial (polynomial_encoded,
      polynomial);
      signature <-
      (SBArray3309_640.set_sub8 signature (48 + (k * ((20 * 256) %/ 8)))
      polynomial_encoded);
      k <- (k + 1);
    }
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (55 + 6)))) {
      signature <-
      (BArray3309.set8 signature
      (W64.to_uint ((W64.of_int (48 + (5 * ((20 * 256) %/ 8)))) + i))
      (W8.of_int 0));
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
        hint_coefficient <-
        (BArray6144.get32 hint_0 (W64.to_uint hint_offset));
        hint_coefficient <- (protect_32 hint_coefficient msf);
        condition <- (hint_coefficient <> (W32.of_int 0));
        if (condition) {
          msf <- (update_msf condition msf);
          signature <-
          (BArray3309.set8 signature
          (W64.to_uint
          ((W64.of_int (48 + (5 * ((20 * 256) %/ 8)))) + hints_written))
          (truncateu8 j));
          hints_written <- (hints_written + (W64.of_int 1));
        } else {
          msf <- (update_msf (! condition) msf);
        }
        j <- (j + (W64.of_int 1));
        condition <- (j \ult (W64.of_int 256));
      }
      msf <- (update_msf (! condition) msf);
      signature <-
      (BArray3309.set8 signature
      (W64.to_uint ((W64.of_int ((48 + (5 * ((20 * 256) %/ 8))) + 55)) + i))
      (truncateu8 hints_written));
      i <- (i + (W64.of_int 1));
      condition <- (i \ult (W64.of_int 6));
    }
    return signature;
  }
  proc signature____decode_hint (hints:BArray6144.t, hint_encoded:BArray61.t) : 
  BArray6144.t * W64.t = {
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
        hints <- (BArray6144.set32 hints (W64.to_uint index) (W32.of_int 0));
        j <- (j + (W64.of_int 1));
      }
      current_true_hints_seen <-
      (zeroextu64
      (BArray61.get8 hint_encoded
      (W64.to_uint ((W64.of_int 55) + encoded_offset))));
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
            hint_at_j <-
            (zeroextu64 (BArray61.get8 hint_encoded (W64.to_uint j)));
             _1 <- (init_msf);
            if ((previous_true_hints_seen \ult j)) {
              hint_at_j_minus_one <-
              (zeroextu64
              (BArray61.get8 hint_encoded (W64.to_uint (j - (W64.of_int 1))))
              );
               _2 <- (init_msf);
              if ((hint_at_j \ule hint_at_j_minus_one)) {
                ill_formed_hint <- (W64.of_int 1);
              } else {
                
              }
            } else {
              
            }
            if ((ill_formed_hint = (W64.of_int 0))) {
              index <- (LEA_64 (decoded_offset + hint_at_j));
              hints <-
              (BArray6144.set32 hints (W64.to_uint index) (W32.of_int 1));
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
      hint_0 <-
      (zeroextu64 (BArray61.get8 hint_encoded (W64.to_uint encoded_offset)));
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
  proc s1____encode (encoded:BArray640.t, s1:BArray5120.t) : BArray640.t = {
    var aux:BArray128.t;
    var i:int;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 5)) {
      aux <@ error_polynomial__encode ((SBArray640_128.get_sub8 encoded
                                       (128 * i)),
      (SBArray5120_1024.get_sub32 s1 (256 * i)));
      encoded <- (SBArray640_128.set_sub8 encoded (128 * i) aux);
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return encoded;
  }
  proc s1____decode (s1:BArray5120.t, encoded:BArray640.t) : BArray5120.t = {
    var aux:BArray1024.t;
    var i:int;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 5)) {
      aux <@ error_polynomial__decode ((SBArray5120_1024.get_sub32 s1
                                       (i * 256)),
      (SBArray640_128.get_sub8 encoded (128 * i)));
      s1 <- (SBArray5120_1024.set_sub32 s1 (i * 256) aux);
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return s1;
  }
  proc s2____encode (encoded:BArray768.t, s2:BArray6144.t) : BArray768.t = {
    var aux:BArray128.t;
    var i:int;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 6)) {
      aux <@ error_polynomial__encode ((SBArray768_128.get_sub8 encoded
                                       (128 * i)),
      (SBArray6144_1024.get_sub32 s2 (256 * i)));
      encoded <- (SBArray768_128.set_sub8 encoded (128 * i) aux);
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return encoded;
  }
  proc s2____decode (s2:BArray6144.t, encoded:BArray768.t) : BArray6144.t = {
    var aux:BArray1024.t;
    var i:int;
    (* Erased call to spill *)
    i <- 0;
    while ((i < 6)) {
      aux <@ error_polynomial__decode ((SBArray6144_1024.get_sub32 s2
                                       (i * 256)),
      (SBArray768_128.get_sub8 encoded (128 * i)));
      s2 <- (SBArray6144_1024.set_sub32 s2 (i * 256) aux);
      (* Erased call to unspill *)
      i <- (i + 1);
    }
    return s2;
  }
  proc __absorb_to_generate_errors (rho_prime:BArray64.t, index:W16.t) : 
  BArray200.t = {
    var state:BArray200.t;
    var i:W64.t;
    var byte:W8.t;
    state <- witness;
    state <@ __keccak_init_ref1 (state);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 64))) {
      byte <- (BArray64.get8 rho_prime (W64.to_uint i));
      state <- (BArray200.set8 state (W64.to_uint i) byte);
      i <- (i + (W64.of_int 1));
    }
    state <- (BArray200.set8 state 64 (truncateu8 index));
    state <- (BArray200.set8 state 65 (W8.of_int 0));
    state <- (BArray200.set8 state 66 (W8.of_int 31));
    state <- (BArray200.set8 state (136 - 1) (W8.of_int 128));
    return state;
  }
  proc rejection_sample_less_than_eta (state:BArray200.t, error:BArray1024.t,
                                       sampled:W64.t) : BArray1024.t * W64.t = {
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
        byte <- (BArray200.get8 state (W64.to_uint xof_offset));
        try_coefficient <- (zeroextu32 byte);
        try_coefficient <- (try_coefficient `&` (W32.of_int 15));
        try_coefficient <- (protect_32 try_coefficient msf);
        b <- (try_coefficient \ult (W32.of_int 9));
        if (b) {
          msf <- (update_msf b msf);
          temp <- (W32.of_int 4);
          temp <- (temp - try_coefficient);
          error <- (BArray1024.set32 error (W64.to_uint sampled) temp);
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
            error <- (BArray1024.set32 error (W64.to_uint sampled) temp);
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
  proc __sample_error_polynomial (rho_prime:BArray64.t, i:int,
                                  error:BArray1024.t) : BArray1024.t = {
    var state:BArray200.t;
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
  proc sample____error_vectors (rho_prime:BArray64.t) : BArray5120.t *
                                                        BArray6144.t = {
    var aux:BArray1024.t;
    var s1:BArray5120.t;
    var s2:BArray6144.t;
    var i:int;
    s1 <- witness;
    s2 <- witness;
    i <- 0;
    while ((i < 5)) {
      aux <@ __sample_error_polynomial (rho_prime, i,
      (SBArray5120_1024.get_sub32 s1 (256 * i)));
      s1 <- (SBArray5120_1024.set_sub32 s1 (256 * i) aux);
      i <- (i + 1);
    }
    i <- 0;
    while ((i < 6)) {
      aux <@ __sample_error_polynomial (rho_prime, (5 + i),
      (SBArray6144_1024.get_sub32 s2 (256 * i)));
      s2 <- (SBArray6144_1024.set_sub32 s2 (256 * i) aux);
      i <- (i + 1);
    }
    return (s1, s2);
  }
  proc __prepare_state_for_shake256 (randomness:BArray32.t,
                                     number_of_rows:W8.t,
                                     number_of_columns:W8.t) : BArray200.t = {
    var state:BArray200.t;
    var i:W64.t;
    var byte:W8.t;
    state <- witness;
    state <@ __keccak_init_ref1 (state);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      byte <- (BArray32.get8 randomness (W64.to_uint i));
      state <- (BArray200.set8 state (W64.to_uint i) byte);
      i <- (i + (W64.of_int 1));
    }
    state <- (BArray200.set8 state 32 number_of_rows);
    state <- (BArray200.set8 state 33 number_of_columns);
    state <-
    (BArray200.set8 state 34 ((BArray200.get8 state 34) `^` (W8.of_int 31)));
    state <-
    (BArray200.set8 state (136 - 1)
    ((BArray200.get8 state (136 - 1)) `^` (W8.of_int 128)));
    return state;
  }
  proc __keygen_internal (verification_key:BArray1952.t,
                          signing_key:BArray4032.t, randomness:BArray32.t) : 
  BArray1952.t * BArray4032.t = {
    var aux_1:BArray1920.t;
    var aux_2:BArray2496.t;
    var aux:BArray640.t;
    var aux_0:BArray768.t;
    var state:BArray200.t;
    var seed_for_matrix_A:BArray32.t;
    var seed_for_error_vectors:BArray64.t;
    var seed_for_signing:BArray32.t;
    var s1:BArray5120.t;
    var s2:BArray6144.t;
    var i:W64.t;
    var matrix_A:BArray30720.t;
    var t:BArray6144.t;
    var t1:BArray6144.t;
    var t0:BArray6144.t;
    var verification_key_pointer_copy:BArray1952.t;
    var verification_key_hash:BArray64.t;
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
    seed_for_matrix_A <- (SBArray200_32.get_sub8 state 0);
    seed_for_error_vectors <- (SBArray200_64.get_sub8 state 32);
    seed_for_signing <- (SBArray200_32.get_sub8 state (32 + 64));
    (s1, s2) <@ sample____error_vectors (seed_for_error_vectors);
    (* Erased call to unspill *)
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      signing_key <-
      (BArray4032.set8 signing_key (W64.to_uint i)
      (BArray32.get8 seed_for_matrix_A (W64.to_uint i)));
      i <- (i + (W64.of_int 1));
    }
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 32))) {
      signing_key <-
      (BArray4032.set8 signing_key (W64.to_uint ((W64.of_int 32) + i))
      (BArray32.get8 seed_for_signing (W64.to_uint i)));
      i <- (i + (W64.of_int 1));
    }
    aux <@ s1____encode ((SBArray4032_640.get_sub8 signing_key
                         ((32 + 32) + 64)),
    s1);
    signing_key <-
    (SBArray4032_640.set_sub8 signing_key ((32 + 32) + 64) aux);
    aux_0 <@ s2____encode ((SBArray4032_768.get_sub8 signing_key
                           (((32 + 32) + 64) + (5 * 128))),
    s2);
    signing_key <-
    (SBArray4032_768.set_sub8 signing_key (((32 + 32) + 64) + (5 * 128))
    aux_0);
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
      verification_key <-
      (BArray1952.set8 verification_key (W64.to_uint i)
      (BArray32.get8 seed_for_matrix_A (W64.to_uint i)));
      i <- (i + (W64.of_int 1));
    }
    aux_1 <@ t1____encode ((SBArray1952_1920.get_sub8 verification_key 32),
    t1);
    verification_key <-
    (SBArray1952_1920.set_sub8 verification_key 32 aux_1);
    verification_key_pointer_copy <- verification_key;
    verification_key_hash <@ __hash_verification_key (verification_key_pointer_copy,
    verification_key_hash);
    (* Erased call to unspill *)
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 64))) {
      signing_key <-
      (BArray4032.set8 signing_key (W64.to_uint ((W64.of_int 64) + i))
      (BArray64.get8 verification_key_hash (W64.to_uint i)));
      i <- (i + (W64.of_int 1));
    }
    aux_2 <@ t0____encode ((SBArray4032_2496.get_sub8 signing_key
                           ((((32 + 32) + 64) + (5 * 128)) + (6 * 128))),
    t0);
    signing_key <-
    (SBArray4032_2496.set_sub8 signing_key
    ((((32 + 32) + 64) + (5 * 128)) + (6 * 128)) aux_2);
    return (verification_key, signing_key);
  }
  proc commitment____encode_polynomial (output:BArray128.t,
                                        commitment_polynomial:BArray1024.t) : 
  BArray128.t = {
    var i:W64.t;
    var encoded_byte:W32.t;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int (256 %/ 2)))) {
      encoded_byte <-
      (BArray1024.get32 commitment_polynomial
      (W64.to_uint (((W64.of_int 2) * i) + (W64.of_int 1))));
      encoded_byte <- (encoded_byte `<<` (W8.of_int 4));
      encoded_byte <-
      (encoded_byte `|`
      (BArray1024.get32 commitment_polynomial
      (W64.to_uint (((W64.of_int 2) * i) + (W64.of_int 0)))));
      output <-
      (BArray128.set8 output (W64.to_uint i) (truncateu8 encoded_byte));
      i <- (i + (W64.of_int 1));
    }
    return output;
  }
  proc commitment____encode (commitment:BArray6144.t) : BArray768.t = {
    var aux:BArray128.t;
    var encoded_commitment:BArray768.t;
    var i:int;
    encoded_commitment <- witness;
    i <- 0;
    while ((i < 6)) {
      aux <@ commitment____encode_polynomial ((SBArray768_128.get_sub8
                                              encoded_commitment
                                              (i * ((4 * 256) %/ 8))),
      (SBArray6144_1024.get_sub32 commitment (i * 256)));
      encoded_commitment <-
      (SBArray768_128.set_sub8 encoded_commitment (i * ((4 * 256) %/ 8)) aux);
      i <- (i + 1);
    }
    return encoded_commitment;
  }
  proc derive_seed_for_mask (k:BArray32.t, randomness:BArray32.t,
                             message_representative:BArray64.t,
                             seed_for_mask:BArray64.t) : BArray64.t = {
    var state:BArray200.t;
    state <- witness;
    state <@ __keccak_init_ref1 (state);
    state <- (SBArray200_32.set_sub8 state 0 (copy_64 k));
    state <- (SBArray200_32.set_sub8 state 32 (copy_64 randomness));
    state <-
    (SBArray200_64.set_sub8 state 64 (copy_64 message_representative));
    state <-
    (BArray200.set8 state 128 ((BArray200.get8 state 128) `^` (W8.of_int 31))
    );
    state <-
    (BArray200.set8 state (136 - 1)
    ((BArray200.get8 state (136 - 1)) `^` (W8.of_int 128)));
    (* Erased call to spill *)
    state <@ _keccakf1600_ref1 (state);
    (* Erased call to unspill *)
    seed_for_mask <- (copy_64 (SBArray200_64.get_sub8 state 0));
    return seed_for_mask;
  }
  proc __sign_internal (signature:BArray3309.t, signing_key:BArray4032.t,
                        pointer_to_message:W64.t, message_size:W64.t,
                        randomness:BArray32.t) : BArray3309.t = {
    var message_representative:BArray64.t;
    var seed_for_matrix_A:BArray32.t;
    var matrix_A:BArray30720.t;
    var seed_for_mask:BArray64.t;
    var s1:BArray5120.t;
    var s2:BArray6144.t;
    var t0:BArray6144.t;
    var domain_separator_for_mask:W16.t;
    var exit_rejection_sampling_loop:W8.t;
    var mask:BArray5120.t;
    var mask_as_ntt:BArray5120.t;
    var w:BArray6144.t;
    var w0:BArray6144.t;
    var w1:BArray6144.t;
    var commitment_encoded:BArray768.t;
    var commitment_hash:BArray48.t;
    var verifier_challenge:BArray1024.t;
    var cs1:BArray5120.t;
    var signer_response:BArray5120.t;
    var infinity_norm_check_result:W8.t;
    var cs2:BArray6144.t;
    var w0_minus_cs2:BArray6144.t;
    var ct0:BArray6144.t;
    var w0_minus_cs2_plus_ct0:BArray6144.t;
    var hint_0:BArray6144.t;
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
    message_representative <@ __derive_message_representative ((
                                                               SBArray4032_64.get_sub8
                                                               signing_key 64
                                                               ),
    pointer_to_message, message_size);
    (* Erased call to unspill *)
    seed_for_matrix_A <- (SBArray4032_32.get_sub8 signing_key 0);
     _0 <- (init_msf);
    matrix_A <@ sample____matrix_A (seed_for_matrix_A);
    (* Erased call to unspill *)
    (* Erased call to unspill *)
    seed_for_mask <@ derive_seed_for_mask ((SBArray4032_32.get_sub8
                                           signing_key 32),
    randomness, message_representative, seed_for_mask);
    (* Erased call to unspill *)
    s1 <@ s1____decode (s1,
    (SBArray4032_640.get_sub8 signing_key ((32 + 32) + 64)));
    s2 <@ s2____decode (s2,
    (SBArray4032_768.get_sub8 signing_key (((32 + 32) + 64) + (5 * 128))));
    t0 <@ t0____decode (t0,
    (SBArray4032_2496.get_sub8 signing_key
    ((((32 + 32) + 64) + (5 * 128)) + (6 * 128))));
    s1 <@ row_vector__ntt (s1);
    s2 <@ column_vector__ntt (s2);
    t0 <@ column_vector__ntt (t0);
    domain_separator_for_mask <- (W16.of_int 0);
    exit_rejection_sampling_loop <- (W8.of_int 0);
    while ((exit_rejection_sampling_loop <> (W8.of_int 1))) {
      (mask, domain_separator_for_mask) <@ sample____mask (seed_for_mask,
      domain_separator_for_mask);
      mask_as_ntt <- (copy_64 mask);
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
  proc __compare_commitment_hashes (lhs:BArray48.t, rhs:BArray48.t) : W64.t = {
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
      lhs_byte <- (BArray48.get8 lhs (W64.to_uint i));
      lhs_byte <- (protect_8 lhs_byte msf);
      rhs_byte <- (BArray48.get8 rhs (W64.to_uint i));
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
  proc reconstruct_signer_commitment (t1_encoded:BArray1920.t,
                                      challenge_as_ntt:BArray1024.t,
                                      a_times_signer_response:BArray6144.t,
                                      hints:BArray6144.t) : BArray768.t = {
    var commitment_encoded:BArray768.t;
    var i:int;
    var az_element:BArray1024.t;
    var t1_element:BArray1024.t;
    var c_times_t1:BArray1024.t;
    var commitment:BArray6144.t;
    var commitment_element:BArray1024.t;
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
      (SBArray6144_1024.get_sub32 a_times_signer_response (i * 256));
      t1_element <@ t1__decode_polynomial (t1_element,
      (SBArray1920_320.get_sub8 t1_encoded ((((23 - 13) * 256) %/ 8) * i)));
      t1_element <@ polynomial____shift_coefficients_left (t1_element);
      t1_element <@ polynomial__ntt (t1_element);
      (* Erased call to unspill *)
      c_times_t1 <@ polynomial__pointwise_montgomery_product (c_times_t1,
      challenge_as_ntt, t1_element);
      commitment_element <-
      (SBArray6144_1024.get_sub32 commitment (i * 256));
      commitment_element <@ polynomial__subtract (commitment_element,
      az_element, c_times_t1);
      commitment_element <@ polynomial__reduce32 (commitment_element);
      commitment_element <@ polynomial__invert_ntt_montgomery (commitment_element);
      commitment_element <@ polynomial__conditionally_add_modulus (commitment_element);
      commitment_element <- commitment_element;
      commitment_element <@ polynomial__use_hints (commitment_element,
      (SBArray6144_1024.get_sub32 hints (i * 256)));
      commitment <-
      (SBArray6144_1024.set_sub32 commitment (i * 256) commitment_element);
      i <- (i + 1);
    }
    commitment_encoded <@ commitment____encode (commitment);
    return commitment_encoded;
  }
  proc __verify_internal (verification_key:BArray1952.t, message:W64.t,
                          message_size:W64.t, signature_encoded:BArray3309.t) : 
  W64.t = {
    var result:W64.t;
    var signer_response:BArray5120.t;
    var signer_response_outside_bounds:W8.t;
    var hints:BArray6144.t;
    var matrix_A:BArray30720.t;
    var a_times_signer_response:BArray6144.t;
    var challenge:BArray1024.t;
    var reconstructed_signer_commitment:BArray768.t;
    var verification_key_hash:BArray64.t;
    var message_representative:BArray64.t;
    var expected_commitment_hash:BArray48.t;
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
    (SBArray3309_3200.get_sub8 signature_encoded 48));
    signer_response_outside_bounds <@ row_vector____check_infinity_norm (
    signer_response, ((1 `<<` 19) - (49 * 4)));
     _0 <- (init_msf);
    if ((signer_response_outside_bounds = (W8.of_int 0))) {
      (hints, result) <@ signature____decode_hint (hints,
      (SBArray3309_61.get_sub8 signature_encoded
      (48 + (5 * ((20 * 256) %/ 8)))));
      if ((result = (W64.of_int 0))) {
        (* Erased call to spill *)
        (* Erased call to spill *)
        matrix_A <@ sample____matrix_A ((SBArray1952_32.get_sub8
                                        verification_key 0));
        signer_response <@ row_vector__ntt (signer_response);
        a_times_signer_response <@ row_vector____multiply_with_matrix_A (
        matrix_A, signer_response);
        (* Erased call to unspill *)
        challenge <@ sample____challenge (challenge,
        (SBArray3309_48.get_sub8 signature_encoded 0));
        challenge <@ polynomial__ntt (challenge);
        (* Erased call to unspill *)
        reconstructed_signer_commitment <@ reconstruct_signer_commitment (
        (SBArray1952_1920.get_sub8 verification_key 32), challenge,
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
        (SBArray3309_48.get_sub8 signature_encoded 0));
      } else {
        
      }
    } else {
      
    }
    return result;
  }
  proc ml_dsa_65_keygen (verification_key:BArray1952.t,
                         signing_key:BArray4032.t, randomness:BArray32.t) : 
  BArray1952.t * BArray4032.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    (verification_key, signing_key) <@ __keygen_internal (verification_key,
    signing_key, randomness);
    return (verification_key, signing_key);
  }
  proc ml_dsa_65_sign (signature:BArray3309.t, signing_key:BArray4032.t,
                       message:W64.t, message_size:W64.t,
                       randomness:BArray32.t) : BArray3309.t = {
    var  _0:W64.t;
     _0 <- (init_msf);
    signature <@ __sign_internal (signature, signing_key, message,
    message_size, randomness);
    return signature;
  }
  proc ml_dsa_65_verify (verification_key:BArray1952.t, message:W64.t,
                         message_size:W64.t, signature:BArray3309.t) : 
  W64.t = {
    var verification_result:W64.t;
    var  _0:W64.t;
     _0 <- (init_msf);
    verification_result <@ __verify_internal (verification_key, message,
    message_size, signature);
    return verification_result;
  }
}.
