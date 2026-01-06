require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

require import
Array2 Array3 Array4 Array5 Array6 Array7 Array8 Array16 Array24 Array25
Array32 Array48 Array61 Array64 Array128 Array136 Array168 Array256 Array272
Array320 Array416 Array640 Array680 Array768 Array848 Array1280 Array1536
Array1920 Array1952 Array2048 Array2496 Array3200 Array3309 Array4032
Array7680 WArray8 WArray16 WArray32 WArray64 WArray96 WArray128 WArray160
WArray192 WArray256 WArray512 WArray768 WArray2048 BArray8 BArray16 BArray32
BArray40 BArray48 BArray61 BArray64 BArray96 BArray128 BArray136 BArray160
BArray168 BArray192 BArray200 BArray224 BArray256 BArray272 BArray320
BArray416 BArray512 BArray640 BArray680 BArray768 BArray800 BArray848
BArray1024 BArray1920 BArray1952 BArray2048 BArray2496 BArray3200 BArray3309
BArray4032 BArray5120 BArray6144 BArray30720 SBArray768_16 SBArray128_32
SBArray1952_32 SBArray4032_32 SBArray1952_48 SBArray3309_48 SBArray3309_61
SBArray128_64 SBArray4032_64 SBArray640_128 SBArray768_128 SBArray272_136
SBArray680_136 SBArray768_136 SBArray1952_136 SBArray848_168 SBArray1920_320
SBArray2496_416 SBArray680_640 SBArray3200_640 SBArray3309_640
SBArray4032_640 SBArray4032_768 SBArray5120_1024 SBArray6144_1024
SBArray30720_1024 SBArray1952_1920 SBArray4032_2496 SBArray3309_3200
SBArray30720_5120.

abbrev [-printing] commitment__ENCODING_SHUFFLES =
(W256.of_int
6809477063014005108496892811167092228318171255968858956394831878370493989120).

abbrev  eRROR_VECTOR_SHUFFLE_TABLE =
(BArray2048.of_list8
[(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 3); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 3); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 4); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 4); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 4); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 4);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 4); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 4); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 4); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 4); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 4); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 3); (W8.of_int 4); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 5); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 5);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 5); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 3); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3);
(W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 5); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 3); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 5);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 5); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 4); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 4); (W8.of_int 5); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 4); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 3); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 3); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 4); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 4);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 4); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 4); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 4); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 4); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 4); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 4);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 3); (W8.of_int 4); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 3); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 0); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 3); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 4); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 4); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 4);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 4); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 4); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 4);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 4); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 4); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 3); (W8.of_int 4); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 4); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 5);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 5); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 5);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3);
(W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 5);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 3); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 3); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 5); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 5);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 4); (W8.of_int 5); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 4); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 4); (W8.of_int 5); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 3); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 3); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 4);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 4); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 4); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 4); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 4); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 4); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 4);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 4); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 4); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 3); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 3); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 3); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 3); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 2); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 0); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 0); (W8.of_int 0); (W8.of_int 0);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6);
(W8.of_int 7); (W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3);
(W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 0);
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7)]).

abbrev [-printing] t1__mask =
(W256.of_int
27580025446916579586740047030762717305835781530194468456916412547466239).

abbrev  t1__DECODING_TABLE =
(BArray64.of_list256
[(W256.of_int
 (-1704488708535735317993730919615273811755981492442837930308886608702668544)
 );
(W256.of_int
161759680028012245712471816852122747571536270840244795705654356475904)]).

abbrev [-printing] t1__SHUFFLE_TO_GROUP =
(W128.of_int (-1152053784517354134044416)).

abbrev  t1__ENCODING_SHIFTS_TABLE =
(BArray96.of_list256
[(W256.of_int 138096238178506976811873579382829307350851889511329270071318);
(W256.of_int 8769009825346546976905862850151196547671258038272);
(W256.of_int 75325220824640169170112861481543258555010121551634147311628)]).

abbrev  t0__DECODING_TABLE =
(BArray96.of_list256
[(W256.of_int
 (-1683702690027913741012871262190298745403129414409667671300841849902661376)
 );
(W256.of_int
80879840039114529797782631482765660946599467588442375410801744805888);
(W256.of_int
220828923202046630884640982628521424684360592877637234731771588637630463)]).

abbrev  t0__ENCODING_SHIFTS_TABLE =
(BArray128.of_list256
[(W256.of_int 119264932972346934519345364012443492712099359123420733243411);
(W256.of_int 475368975159373001864691843072);
(W256.of_int 37662610412320084585056430740771629277505060775817073655814);
(W256.of_int 221360928884514619392)]).

abbrev [-printing] cONST_0123 =
(W256.of_int 18831305206160042292187933003464876175252262292329349513216).

abbrev  matrix_A__DECODING_TABLE =
(BArray96.of_list256
[(W256.of_int 31385508682779410369523405889615886801803926611390921441280);
(W256.of_int
(-432808243909779573675567928807470101786712732301848327860692622735061155584)
);
(W256.of_int
226156397384342666605459106258636701594091082888230722833791023177481060351)]
).

abbrev  matrix_A__SHUFFLE_TABLE =
(BArray256.of_list8
[(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 7); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 8); (W8.of_int 9);
(W8.of_int 10); (W8.of_int 11); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 8); (W8.of_int 9); (W8.of_int 10);
(W8.of_int 11); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 8); (W8.of_int 9); (W8.of_int 10); (W8.of_int 11);
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 8); (W8.of_int 9);
(W8.of_int 10); (W8.of_int 11); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 12); (W8.of_int 13);
(W8.of_int 14); (W8.of_int 15); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 12); (W8.of_int 13); (W8.of_int 14);
(W8.of_int 15); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 12); (W8.of_int 13); (W8.of_int 14); (W8.of_int 15);
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int 0); (W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4);
(W8.of_int 5); (W8.of_int 6); (W8.of_int 7); (W8.of_int 12); (W8.of_int 13);
(W8.of_int 14); (W8.of_int 15); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 8); (W8.of_int 9);
(W8.of_int 10); (W8.of_int 11); (W8.of_int 12); (W8.of_int 13);
(W8.of_int 14); (W8.of_int 15); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 0); (W8.of_int 1);
(W8.of_int 2); (W8.of_int 3); (W8.of_int 8); (W8.of_int 9); (W8.of_int 10);
(W8.of_int 11); (W8.of_int 12); (W8.of_int 13); (W8.of_int 14);
(W8.of_int 15); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int 4); (W8.of_int 5); (W8.of_int 6); (W8.of_int 7);
(W8.of_int 8); (W8.of_int 9); (W8.of_int 10); (W8.of_int 11); (W8.of_int 12);
(W8.of_int 13); (W8.of_int 14); (W8.of_int 15); (W8.of_int (-1));
(W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int (-1)); (W8.of_int 0);
(W8.of_int 1); (W8.of_int 2); (W8.of_int 3); (W8.of_int 4); (W8.of_int 5);
(W8.of_int 6); (W8.of_int 7); (W8.of_int 8); (W8.of_int 9); (W8.of_int 10);
(W8.of_int 11); (W8.of_int 12); (W8.of_int 13); (W8.of_int 14);
(W8.of_int 15)]).

abbrev  keccakF1600RoundConstants =
(BArray768.of_list256
[(W256.of_int 6277101735386680764176071790128604879584176795969512275969);
(W256.of_int 206504092890751023779864409751650843328560248233805014854828162);
(W256.of_int
(-57896044618657891154337237002533387566728630465883811983015055433200855646070)
);
(W256.of_int
(-57896044605177918687001956587831074660851270707671256656745893357814858874880)
);
(W256.of_int 206560586806369503906741994397762000772476505824968740465311883);
(W256.of_int
13479973339852421633450939126351338586088633588469736715148203130881);
(W256.of_int
(-57896044605177917877255832722949256082138009781081227190387086677747775274879)
);
(W256.of_int
(-57896044618657891964083360867415206145441891392473841449373862113267939246071)
);
(W256.of_int 866240039483361945456297907037747473382616397843792694083722);
(W256.of_int 853685836012588583927945763457490263623448044251853669531784);
(W256.of_int
13480179078138900667299665761280331841242166839448401411882560290825);
(W256.of_int
13479973396346337251931066003935984697246077504727327878873813614602);
(W256.of_int
13480179894162126267568165104169664557960801185391384887919156166795);
(W256.of_int
(-57896044618658096836129800417901987324072977609879901317736128966209602322293)
);
(W256.of_int
(-57896044618657891160614338737920068330904702256012416862599232229170367922039)
);
(W256.of_int
(-57896044618657892001745971279735290730498322133245470726878922889085012901885)
);
(W256.of_int
(-57896044618657892008023073015121971494674393923374075606463099685054525177854)
);
(W256.of_int
(-57896044618658096905177919507155475730009767301294554993162073721874237357952)
);
(W256.of_int 205750840682504622088163281136835410743010147018288673381711882);
(W256.of_int
(-57896044605178124312300604384719547540610971740509902075209375727097995067382)
);
(W256.of_int
(-57896044605177917877255832722949256082138009781081227190387086677747775274879)
);
(W256.of_int
(-57896044618657891217108254356400195208489348367169860778856823392895978405760)
);
(W256.of_int
13479973339852421633450939126351338586088633588469736715148203130881);
(W256.of_int
(-57896044605177918636785142704737628547442696386642417620072478990058760667128)
)]).

abbrev  shake_sep =
(BArray32.of_list64
[(W64.of_int (-9223372036854775808)); (W64.of_int (-9223372036854775808));
(W64.of_int (-9223372036854775808)); (W64.of_int (-9223372036854775808))]).

abbrev [-printing] rho8 =
(W256.of_int
13620818001941277694121380808605999856886653716761013959207994299728839901191
).

abbrev [-printing] rho56 =
(W256.of_int
10910488462195273559651782724632284871561478246514020268633800075540923875841
).

abbrev  kECCAK_RHOTATES_RIGHT =
(BArray192.of_list256
[(W256.of_int 144373339913893657577751063007562604548177214458152943091773);
(W256.of_int 232252764209307188274174373867837442080505530800860351692863);
(W256.of_int 156927543384667019098616994515559168111335794127330162507795);
(W256.of_int 351517697181654122777866749001917765472957616589092975280182);
(W256.of_int 276192476357013953622045746931053922384479139705868246843454);
(W256.of_int 313855086769334038206421612937983674734430261968315659321364)]).

abbrev  kECCAK_RHOTATES_LEFT =
(BArray192.of_list256
[(W256.of_int 257361171150853911329517531560668107745210100483895842570243);
(W256.of_int 169481746855440380633094220700393270212881784141188433969153);
(W256.of_int 244806967680080549808651600052671544182051520814718623154221);
(W256.of_int 50216813883093446129401845566312946820429698352955810381834);
(W256.of_int 125542034707733615285222847637176789908908175236180538818562);
(W256.of_int 87879424295413530700846981630247037558957052973733126340652)]).

abbrev  kECCAK1600_RC =
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

abbrev  zETAS_TO_INVERT_LAYER_6 =
(BArray8.of_list32 [(W32.of_int (-518909)); (W32.of_int (-2608894))]).

abbrev  zETAS_TO_INVERT_LAYER_5 =
(BArray16.of_list32
[(W32.of_int 466468); (W32.of_int (-876248)); (W32.of_int (-777960));
(W32.of_int 237124)]).

abbrev  zETAS_TO_INVERT_LAYER_4 =
(BArray32.of_list32
[(W32.of_int 2680103); (W32.of_int 3111497); (W32.of_int (-2884855));
(W32.of_int 3119733); (W32.of_int (-2091905)); (W32.of_int (-359251));
(W32.of_int 2353451); (W32.of_int 1826347)]).

abbrev  zETAS_TO_INVERT_LAYER_3 =
(BArray64.of_list32
[(W32.of_int 280005); (W32.of_int 4010497); (W32.of_int (-19422));
(W32.of_int 1757237); (W32.of_int (-3277672)); (W32.of_int (-1399561));
(W32.of_int (-3859737)); (W32.of_int (-2118186)); (W32.of_int (-2108549));
(W32.of_int 2619752); (W32.of_int (-1119584)); (W32.of_int (-549488));
(W32.of_int 3585928); (W32.of_int (-1079900)); (W32.of_int 1024112);
(W32.of_int 2725464)]).

abbrev  zETAS_TO_INVERT_LAYER_2 =
(BArray512.of_list256
[(W256.of_int
 55858097833101550257214085554898365818120118939289856544579935031533063981);
(W256.of_int
105163311027759753657778087208235454592057129092071682892877310237938875440);
(W256.of_int
25725989914184953801617746899476742653944181040072196426454101837991327827);
(W256.of_int
21889966941809614170064575509624246080299888430238795568055695825414134682);
(W256.of_int
(-43147210895140552674126020849390261598795394536363723224061988817370319988)
);
(W256.of_int
94555623449686201047046586089202287911895030785269406424979215626557937175);
(W256.of_int
94513323293355592920583638744342789667917531388272404646804202659466555225);
(W256.of_int
(-45812120743968864641291703575538650621127909064993469193858518144591140138)
);
(W256.of_int
63320826751879736535069744341302438400871249283798704129972914700106057053);
(W256.of_int
95437348505640655333834790623064550541058135367234548429171322106916072013);
(W256.of_int
96366226508326934740561615237334246202685117296625000557156943582056431169);
(W256.of_int
(-104095427540025280815714770235714915413038677656764623303505208897845490052)
);
(W256.of_int
(-68411269083022995552342786355098589395800322542083880897111870443293524305)
);
(W256.of_int
(-44799127707661490680986551545104751950660152152719002346056174221244420052)
);
(W256.of_int
82964517896806024708470005111380135907348798935390409998868367704828796613);
(W256.of_int
72954235777068957422335349253495230275540662222309750361511250266905736736)]).

abbrev  zETAS_TO_INVERT_LAYER_1 =
(BArray512.of_list256
[(W256.of_int
 (-81394801961692367886430385872069775591899888374899243279001081876171810855)
 );
(W256.of_int
34661567679679177301116532790068060848189603243687759106031639884244584450);
(W256.of_int
(-64955246559009626209334090610844950686859823444064428462419434932632520814)
);
(W256.of_int
5110203972054881556156591894762920528448975955081272796495122244267393014);
(W256.of_int
64416910343834614792393674441495836491133256368070832133925939380646307848);
(W256.of_int
(-100408034753660554592467491302376209402241585185804306979514679237786310208)
);
(W256.of_int
1194002118272767818204969697142475014804055004809772772326363503993317210);
(W256.of_int
(-90137400428898195608591888407911072567948167381482086222197180771257596536)
);
(W256.of_int
(-10298322189995975550492998599235942704890266878993213373882488288311628702)
);
(W256.of_int
(-18092847172484030768594150646838607120362146941117652454946646810846033417)
);
(W256.of_int
(-80007523985717796585815385341741418921177183815858461275034603165699132407)
);
(W256.of_int
91992999638536873929403675040794761538037322390893756773920815590270398111);
(W256.of_int
(-86006085160608795653219616202775328578590887095922183230672569182969532470)
);
(W256.of_int
(-33905098535969462031579012142083424424900777513339595321775290397735469834)
);
(W256.of_int
(-39157974545820129459247333378438079185440363582611062924321782937515733061)
);
(W256.of_int
(-105963212645560354748648894728962413671494752281642171317139502339957090279)
)]).

abbrev  zETAS_TO_INVERT_LAYER_0 =
(BArray512.of_list256
[(W256.of_int
 (-14947025766810884518519340178851830259972079680536628082551345248834016818)
 );
(W256.of_int
(-79236226866924585952449654367977996136871924539618190998681853009488910935)
);
(W256.of_int
(-11503350912960617613730640784158756079862038378229427709112689681143332901)
);
(W256.of_int
(-81929013263830893704991921825282108025075782622382010162513630324042812402)
);
(W256.of_int
(-85824995177798504282796294437560123626439291842320922633474527581536220099)
);
(W256.of_int
(-54286764273279474617153417324944689044923369866922433929488586482031684697)
);
(W256.of_int
(-14623371649451712728712467712169116528326753931430007783612848928714236385)
);
(W256.of_int
(-34499592299998942396114060243824569874827496206622141668637037974906472241)
);
(W256.of_int
(-35939172576451990257306214357269889304653686414943338569916213557288891026)
);
(W256.of_int
(-101558550446453650186530786043368056571637735915462539611172798861872728410)
);
(W256.of_int
76629361786750316726400779924715828393657363260547957195302525993867565638);
(W256.of_int
9228308866127115427653890041133811097211812064444699926619978848773806372);
(W256.of_int
(-17667554029197039999021031754983291937999381450166200406335605094401629758)
);
(W256.of_int
24282877894665662847114239626329772913956173036192043697149135726675756796);
(W256.of_int
7198224895570446916806461394142653175548603531300001347978374732042946014);
(W256.of_int
56391230786829500805896074122730759173243203946337935118236635448285439010)]).

abbrev  lAYER_5_ZETAS =
(BArray128.of_list256
[(W256.of_int
 6392850394989879782919009689269382774612906998598077359118130409487179332);
(W256.of_int
(-20973733154113172374116031522976669396413195272188229214344316118293536488)
);
(W256.of_int
(-23623572392751038233765597253728972386203994192070686609939037874369158872)
);
(W256.of_int
12575952404860491736722831142078028559353475404522730510421197583764889124)]).

abbrev  lAYER_4_ZETAS =
(BArray256.of_list256
[(W256.of_int
 49238217727174735462858186387578100159688428240787953942213019850271088171);
(W256.of_int
63448913458525191735085973044570427962987806332373120219353262977758521643);
(W256.of_int
(-9685360842428916145196834697753182983500981930324890315881936664396135251));
(W256.of_int
(-56397620285930186220742767687038759905129124854486734450534966836456319873)
);
(W256.of_int
84107835315332748371338501606473572188354819374915131634898543954979953269);
(W256.of_int
(-77775510000624713868157743535565931642824611623174616916724477422490879223)
);
(W256.of_int
83885793194530397492084942439958067066428266592234113411818227656112962121);
(W256.of_int
72255433959293710361838475334592620664244765969128822575549411552005776679)]).

abbrev  lAYER_3_ZETAS =
(BArray512.of_list256
[(W256.of_int
 73478364100347066145449536207869676010979875339599156186179113790095332952);
(W256.of_int
27610004907617431235323091930369958891020619642669127546773784053578440816);
(W256.of_int
(-29114019452687944652141730252662392625468968366251687480112978488363874908)
);
(W256.of_int
96676427654751394334623229099637232984438995494630684149338570296686720904);
(W256.of_int
(-14814140217741789410927691322378018811565773299786869881706381995571438192)
);
(W256.of_int
(-30183897976476251147078379349797082433450187480859935071749606949296084320)
);
(W256.of_int
70628374217605672732670001650962551502832747150821133068371149173069183336);
(W256.of_int
(-56846341638362717550793306634037796725107942789763916007716703659955858565)
);
(W256.of_int
(-57106154644454540695932518592234727621174745748323529001381711937296945706)
);
(W256.of_int
(-104058276733509297387884342293575725750886975620944943210190348485148730649)
);
(W256.of_int
(-37732062966262529937847409797042295828500025804886578957538547746756451081)
);
(W256.of_int
(-88365835373040579013342948867416487189184821000834832474730864937308128104)
);
(W256.of_int
47375015812574144245615171089146026461735045189417729391814688206912933941);
(W256.of_int
(-523589124344640168283556650424675203124767070476937215935262608098085854));
(W256.of_int
108122785253941937128917104982143485304890013997556525086078105349340869121);
(W256.of_int
7548919868293134767531912872774892140000535686570969834094701950491968965)]).

abbrev  lAYER_2_ZETAS =
(BArray512.of_list256
[(W256.of_int
 2582115852594215372922399554661124157277897753758022393249206975595104871);
(W256.of_int
95180393253896215529297919275801403125147833943906619600164777952522728653);
(W256.of_int
(-96844091563113441459207722112818379943157009722955851967939200150180289277)
);
(W256.of_int
105560026643059242874414333339279123590254343489504880656670121511773358036);
(W256.of_int
(-82058394089112118315595779323790756700487005185220852200797524175183604347)
);
(W256.of_int
(-77311583238268369291883430017183366157182291952749413423133918758353597802)
);
(W256.of_int
(-8100547337178139787008245328587635352700729757627470271676080386151676928));
(W256.of_int
(-14539445321086234152463082975167421569381635625639435689228564068424231268)
);
(W256.of_int
(-44317218660873969801110717389997338879307479034035967944316937582115679683)
);
(W256.of_int
(-103033744840025696354203701758616738032860190620728572595116874234736574946)
);
(W256.of_int
(-57711755926579748053954944473419501097706598159769197715058567402163436481)
);
(W256.of_int
99740910873226578859027498567763075504868159311739122747018415153785312348);
(W256.of_int
14325275504712524173736726246318565876195315536473979690242352211913630632);
(W256.of_int
104632712317280022276696336606463762131530400452447840796497601825375948662);
(W256.of_int
(-68933321490407250339359046639266418582417944507082254287320285389600881356)
);
(W256.of_int
(-75427945684089319846559526199054989292473894219667903397284946799304401580)
)]).

abbrev  lAYER_1_ZETAS =
(BArray512.of_list256
[(W256.of_int
 (-81992045660348812641476123197708666079241631123768297083540656699031157019)
 );
(W256.of_int
(-42737446665651130700293348505910636389708383368459145663957684787411823011)
);
(W256.of_int
(-26965365622709106780368661443443548512078695116176182616612116382728007819)
);
(W256.of_int
3421810351684802082964769067296309699936088410999557092647286114297533056);
(W256.of_int
73204208402624985713511618444513909716812773993549855077803124974272385266);
(W256.of_int
(-66781028067627493451451431699303436410367131290803476159769148694121498717)
);
(W256.of_int
(-35268139519884621783682773031740188428473545878656661145853861037123190142)
);
(W256.of_int
(-38564289560124577164223236705581139589637471190934819397139455616074765347)
);
(W256.of_int
83521699114705755838561325406274439130886830666761290636494297414977256425);
(W256.of_int
106724130180471185595712043181305186969900588105579027577994805152403467520);
(W256.of_int
(-87612466623198314199249342155859137881401108183911389095677359257120461878)
);
(W256.of_int
(-35502340576636688572867201419187530558567181874942573856296599846840404628)
);
(W256.of_int
(-49913672231130794101676053937559106172010661027002323394503420373148441492)
);
(W256.of_int
36162185271468838823349331853221926688304910074992295741345607920165534867);
(W256.of_int
(-38815340583547530020537411524095712066112549812346116746967645504362275291)
);
(W256.of_int
103525143788042270064916081275428900954501718048654818943189921863570681506)]
).

abbrev  lAYER_0_ZETAS =
(BArray512.of_list256
[(W256.of_int
 (-96043758579160644217776514638953766832040475090913850812646157387223274861)
 );
(W256.of_int
(-86093273615620618052689901656884593902421885036751304584651663901315558667)
);
(W256.of_int
(-14086545173911089561949528993457026072356098848467443862900796059865465250)
);
(W256.of_int
(-96943573748591673632705333890837508601762989505283144305719118595512467423)
);
(W256.of_int
5474055421981223595793975988818518111412432267915805729515223516017146137);
(W256.of_int
43027373937766165928586588799055057712463440178580726831465884900303527653);
(W256.of_int
(-28334095136827246491389516096410921694855453151494860059292548015584803560)
);
(W256.of_int
(-52912723625957039508985463083087738847792605820588336715244713961281836866)
);
(W256.of_int
91826414120696613313678319861910223306340101487465572345151919031776475475);
(W256.of_int
(-101827529838471838058920640338224688687792744157920897239160857356254332620)
);
(W256.of_int
(-32551035205553071989555012365732791000044387452985845181336240680081471912)
);
(W256.of_int
(-48503801831739795329241971286407911108857526471346587968315404362093466434)
);
(W256.of_int
12727197713517537082815509913119745890371516046578436962151070568165777724);
(W256.of_int
(-103361523849251602159785089487568870121220845713788474355019617747115344571)
);
(W256.of_int
(-95591532408285370970768713552277605216736587735721877751913636348105119900)
);
(W256.of_int
53293964247218654718527730774000289571803083760351434456930051142633097808)]).

abbrev [-printing] tWO_POW_22_VECTOR =
(W256.of_int
113078212172144670016600318886917095060348232468446510094543828752187523072).

abbrev [-printing] iNVERSE_OF_MODULUS_MOD_MONTGOMERY_R_VECTOR =
(W256.of_int
1583315853253120773718772168429862829322770379248453373268938642773050925057).

abbrev  polynomial__CONSTANTS_TABLE =
(BArray160.of_list256
[(W256.of_int
 404399200101416122972727962327899080730729934460329449514903409786895);
(W256.of_int
27633945340263435069803077425739770516599878854789179050185066335437825);
(W256.of_int
14120973028821288748410904079750511260587920143459567849941203224302714368);
(W256.of_int
3423913227525323174502430081042878883520180111764122672559515536195711);
(W256.of_int
13803492696795003664135781114125621955608915096245911876775369720726016)]).

abbrev  gamma1__DECODING_SHIFTS_TABLE =
(BArray64.of_list256
[(W256.of_int
 (-425713140823427258726663558789254841410387362057345797737825556725963292416)
 );
(W256.of_int
107839786668602559184514066897402134367680229671084479353429526839296)]).

abbrev  gamma1__ENCODING_SHIFTS_TABLE =
(BArray64.of_list256
[(W256.of_int 75325220824640169170112861481543258555010121551634147311628);
(W256.of_int
(-392023588615790074933092468460461382420127193604147098349862656))]).

abbrev [-printing] error_polynomial__SHIFTS =
(W256.of_int
107839786668602559184514066897402134367680229671084479353429526839296).

abbrev [-printing] error_polynomial__DECODING_SHUFFLES =
(W256.of_int
(-6793906561703790865943291268746375741561545978554779831640812377080064)).

abbrev [-printing] error_polynomial__ENCODING_SHUFFLES =
(W256.of_int
6809477063014005108496892811167092228318171255968858956394831878370493989120).

abbrev [-printing] hALF_OF_BITS_IN_T0_VECTOR =
(W256.of_int
110427941574360029313086248913004975644871320769967295014202957765808128).

abbrev [-printing] mODULUS_VECTOR =
(W256.of_int
225935595421087293402315996791205668696012104344015382954355885915737415681).

module M = {
  proc error_polynomial__encode (encoded:BArray128.t, polynomial:BArray1024.t) : 
  BArray128.t = {
    var temp:W64.t;
    var shift:W256.t;
    var eta_0:W256.t;
    var encoding_shuffles:W256.t;
    var input_offset:W64.t;
    var output_offset:W64.t;
    var c0:W256.t;
    var c1:W256.t;
    var c2:W256.t;
    var c3:W256.t;
    var c4:W256.t;
    var c5:W256.t;
    var c6:W256.t;
    var c7:W256.t;
    temp <- (W64.of_int ((16 `<<` 8) + 1));
    shift <- (zeroextu256 (VMOV_64 temp));
    shift <- (VPBROADCAST_16u16 (truncateu16 shift));
    temp <- (W64.of_int 4);
    eta_0 <- (zeroextu256 (VMOV_64 temp));
    eta_0 <- (VPBROADCAST_8u32 (truncateu32 eta_0));
    encoding_shuffles <- error_polynomial__ENCODING_SHUFFLES;
    input_offset <- (W64.of_int 0);
    output_offset <- (W64.of_int 0);
    while ((input_offset \ult (W64.of_int ((256 * 32) %/ 8)))) {
      c0 <- (BArray1024.get256d polynomial (W64.to_uint input_offset));
      c0 <- (VPSUB_8u32 eta_0 c0);
      input_offset <- (input_offset + (W64.of_int 32));
      c1 <- (BArray1024.get256d polynomial (W64.to_uint input_offset));
      c1 <- (VPSUB_8u32 eta_0 c1);
      input_offset <- (input_offset + (W64.of_int 32));
      c2 <- (BArray1024.get256d polynomial (W64.to_uint input_offset));
      c2 <- (VPSUB_8u32 eta_0 c2);
      input_offset <- (input_offset + (W64.of_int 32));
      c3 <- (BArray1024.get256d polynomial (W64.to_uint input_offset));
      c3 <- (VPSUB_8u32 eta_0 c3);
      input_offset <- (input_offset + (W64.of_int 32));
      c4 <- (BArray1024.get256d polynomial (W64.to_uint input_offset));
      c4 <- (VPSUB_8u32 eta_0 c4);
      input_offset <- (input_offset + (W64.of_int 32));
      c5 <- (BArray1024.get256d polynomial (W64.to_uint input_offset));
      c5 <- (VPSUB_8u32 eta_0 c5);
      input_offset <- (input_offset + (W64.of_int 32));
      c6 <- (BArray1024.get256d polynomial (W64.to_uint input_offset));
      c6 <- (VPSUB_8u32 eta_0 c6);
      input_offset <- (input_offset + (W64.of_int 32));
      c7 <- (BArray1024.get256d polynomial (W64.to_uint input_offset));
      c7 <- (VPSUB_8u32 eta_0 c7);
      input_offset <- (input_offset + (W64.of_int 32));
      c0 <- (VPACKUS_8u32 c0 c1);
      c1 <- (VPACKUS_8u32 c2 c3);
      c2 <- (VPACKUS_8u32 c4 c5);
      c3 <- (VPACKUS_8u32 c6 c7);
      c0 <- (VPACKUS_16u16 c0 c1);
      c1 <- (VPACKUS_16u16 c2 c3);
      c0 <- (VPMADDUBSW_256 c0 shift);
      c1 <- (VPMADDUBSW_256 c1 shift);
      c0 <- (VPACKUS_16u16 c0 c1);
      c0 <- (VPERMQ c0 (W8.of_int 216));
      c0 <- (VPSHUFB_256 c0 encoding_shuffles);
      encoded <- (BArray128.set256d encoded (W64.to_uint output_offset) c0);
      output_offset <- (output_offset + (W64.of_int 32));
    }
    return encoded;
  }
  proc error_polynomial__decode (decoded:BArray1024.t, encoded:BArray128.t) : 
  BArray1024.t = {
    var temp:W64.t;
    var mask:W256.t;
    var eta_0:W256.t;
    var decoding_shuffles:W256.t;
    var shifts:W256.t;
    var coefficients:W256.t;
    var input_offset:W64.t;
    var output_offset:W64.t;
    var bytes:W128.t;
    var byte_group:W64.t;
    temp <- (W64.of_int ((1 `<<` 4) - 1));
    mask <- (zeroextu256 (VMOV_64 temp));
    mask <- (VPBROADCAST_8u32 (truncateu32 mask));
    temp <- (W64.of_int 4);
    eta_0 <- (zeroextu256 (VMOV_64 temp));
    eta_0 <- (VPBROADCAST_8u32 (truncateu32 eta_0));
    decoding_shuffles <- error_polynomial__DECODING_SHUFFLES;
    shifts <- error_polynomial__SHIFTS;
    coefficients <- (set0_256);
    input_offset <- (W64.of_int 0);
    output_offset <- (W64.of_int 0);
    while ((input_offset \ult (W64.of_int 128))) {
      bytes <- (BArray128.get128d encoded (W64.to_uint input_offset));
      input_offset <- (input_offset + (W64.of_int 16));
      byte_group <- (W64.of_int 0);
      while ((byte_group \ult (W64.of_int 4))) {
        coefficients <- (VINSERTI128 coefficients bytes (W8.of_int 0));
        coefficients <- (VINSERTI128 coefficients bytes (W8.of_int 1));
        coefficients <- (VPSHUFB_256 coefficients decoding_shuffles);
        coefficients <- (VPSRLV_8u32 coefficients shifts);
        coefficients <- (VPAND_256 coefficients mask);
        coefficients <- (VPSUB_8u32 eta_0 coefficients);
        decoded <-
        (BArray1024.set256d decoded (W64.to_uint output_offset) coefficients);
        output_offset <- (output_offset + (W64.of_int 32));
        bytes <- (VPSRLDQ_128 bytes (W8.of_int 4));
        byte_group <- (byte_group + (W64.of_int 1));
      }
    }
    return decoded;
  }
  proc gamma1__coefficients_to_bytestream (gamma1:W256.t, coefficients:W256.t) : 
  W128.t * W128.t = {
    var bytestream_lower:W128.t;
    var bytestream_upper:W128.t;
    var shifts:W256.t;
    var bytestream:W256.t;
    coefficients <- (VPSUB_8u32 gamma1 coefficients);
    shifts <- (BArray64.get256 gamma1__ENCODING_SHIFTS_TABLE 0);
    bytestream <- (VPSLLV_8u32 coefficients shifts);
    bytestream <- (VPSRL_4u64 bytestream (W128.of_int 12));
    shifts <- (BArray64.get256 gamma1__ENCODING_SHIFTS_TABLE 1);
    bytestream <- (VPSHUFB_256 bytestream shifts);
    bytestream_lower <- (VEXTRACTI128 bytestream (W8.of_int 0));
    bytestream_upper <- (VEXTRACTI128 bytestream (W8.of_int 1));
    return (bytestream_lower, bytestream_upper);
  }
  proc gamma1____encode_polynomial (output:BArray640.t,
                                    polynomial:BArray1024.t) : BArray640.t = {
    var temp:W64.t;
    var gamma1:W256.t;
    var output_offset:int;
    var input_offset:int;
    var coefficients:W256.t;
    var lower:W128.t;
    var upper:W128.t;
    var final_output_block:BArray16.t;
    var i:int;
    final_output_block <- witness;
    temp <- (W64.of_int (1 `<<` 19));
    gamma1 <- (zeroextu256 (VMOV_64 temp));
    gamma1 <- (VPBROADCAST_8u32 (truncateu32 gamma1));
    output_offset <- 0;
    input_offset <- 0;
    while ((input_offset < (((256 * 32) %/ 8) - 32))) {
      coefficients <- (BArray1024.get256d polynomial input_offset);
      (lower, upper) <@ gamma1__coefficients_to_bytestream (gamma1,
      coefficients);
      output <- (BArray640.set128d output output_offset lower);
      output_offset <- (output_offset + 10);
      output <- (BArray640.set128d output output_offset upper);
      output_offset <- (output_offset + 10);
      input_offset <- (input_offset + 32);
    }
    coefficients <- (BArray1024.get256d polynomial input_offset);
    (lower, upper) <@ gamma1__coefficients_to_bytestream (gamma1,
    coefficients);
    output <- (BArray640.set128d output output_offset lower);
    output_offset <- (output_offset + 10);
    final_output_block <- (BArray16.set128d final_output_block 0 upper);
    i <- 0;
    while ((i < 10)) {
      output <-
      (BArray640.set8 output (output_offset + i)
      (BArray16.get8 final_output_block i));
      i <- (i + 1);
    }
    return output;
  }
  proc gamma1____decode_to_polynomial (polynomial:BArray1024.t,
                                       bytes:BArray640.t) : BArray1024.t = {
    var temp:W64.t;
    var temp1:W128.t;
    var gamma1:W256.t;
    var gamma1_times_2_mask:W256.t;
    var coefficients:W256.t;
    var input_offset:int;
    var output_offset:int;
    var sixteen_bytes:W128.t;
    var shifts:W256.t;
    temp <- (W64.of_int (1 `<<` 19));
    temp1 <- (VMOV_64 temp);
    gamma1 <- (VPBROADCAST_8u32 (truncateu32 temp1));
    temp <- (W64.of_int (((1 `<<` 19) `<<` 1) - 1));
    temp1 <- (VMOV_64 temp);
    gamma1_times_2_mask <- (VPBROADCAST_8u32 (truncateu32 temp1));
    coefficients <- (set0_256);
    input_offset <- 0;
    output_offset <- 0;
    while ((input_offset < ((20 * 256) %/ 8))) {
      sixteen_bytes <- (BArray640.get128d bytes input_offset);
      input_offset <- (input_offset + 4);
      coefficients <- (VINSERTI128 coefficients sixteen_bytes (W8.of_int 0));
      sixteen_bytes <- (BArray640.get128d bytes input_offset);
      input_offset <- (input_offset + 16);
      coefficients <- (VINSERTI128 coefficients sixteen_bytes (W8.of_int 1));
      shifts <- (BArray64.get256 gamma1__DECODING_SHIFTS_TABLE 0);
      coefficients <- (VPSHUFB_256 coefficients shifts);
      shifts <- (BArray64.get256 gamma1__DECODING_SHIFTS_TABLE 1);
      coefficients <- (VPSRLV_8u32 coefficients shifts);
      coefficients <- (VPAND_256 coefficients gamma1_times_2_mask);
      coefficients <- (VPSUB_8u32 gamma1 coefficients);
      polynomial <-
      (BArray1024.set256d polynomial output_offset coefficients);
      output_offset <- (output_offset + 32);
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
  proc polynomial__decompose (lows:BArray1024.t, highs:BArray1024.t,
                              polynomial:BArray1024.t) : BArray1024.t *
                                                         BArray1024.t = {
    var modulus:W256.t;
    var modulus_halved:W256.t;
    var mask:W256.t;
    var v:W256.t;
    var alpha:W256.t;
    var offs:W256.t;
    var shift:W256.t;
    var offset:W64.t;
    var coefficients:W256.t;
    var upper:W256.t;
    var lower:W256.t;
    var comparisons:W256.t;
    modulus <- mODULUS_VECTOR;
    modulus_halved <- (VPSRL_8u32 modulus (W128.of_int 1));
    mask <- (BArray160.get256 polynomial__CONSTANTS_TABLE 0);
    v <- (BArray160.get256 polynomial__CONSTANTS_TABLE 1);
    alpha <- (BArray160.get256 polynomial__CONSTANTS_TABLE 2);
    offs <- (BArray160.get256 polynomial__CONSTANTS_TABLE 3);
    shift <- (BArray160.get256 polynomial__CONSTANTS_TABLE 4);
    offset <- (W64.of_int 0);
    while ((offset \ult (W64.of_int ((256 * 32) %/ 8)))) {
      coefficients <- (BArray1024.get256d polynomial (W64.to_uint offset));
      upper <- (VPADD_8u32 coefficients offs);
      upper <- (VPSRL_8u32 upper (W128.of_int 7));
      upper <- (VPMULHU_16u16 upper v);
      upper <- (VPMULHRS_16u16 upper shift);
      upper <- (VPAND_256 upper mask);
      lower <- (VPMULL_8u32 upper alpha);
      lower <- (VPSUB_8u32 coefficients lower);
      comparisons <- (VPCMPGT_8u32 lower modulus_halved);
      comparisons <- (VPAND_256 comparisons modulus);
      lower <- (VPSUB_8u32 lower comparisons);
      lows <- (BArray1024.set256d lows (W64.to_uint offset) lower);
      highs <- (BArray1024.set256d highs (W64.to_uint offset) upper);
      offset <- (offset + (W64.of_int 32));
    }
    return (lows, highs);
  }
  proc polynomial__use_hints (commitment:BArray1024.t,
                              hint_polynomial:BArray1024.t) : BArray1024.t = {
    var mask:W256.t;
    var lows:BArray1024.t;
    var highs:BArray1024.t;
    var offset:W64.t;
    var low:W256.t;
    var hints:W256.t;
    var high:W256.t;
    var coefficients:W256.t;
    highs <- witness;
    lows <- witness;
    mask <- (BArray160.get256 polynomial__CONSTANTS_TABLE 0);
    (lows, highs) <@ polynomial__decompose (lows, highs, commitment);
    offset <- (W64.of_int 0);
    while ((offset \ult (W64.of_int ((256 * 32) %/ 8)))) {
      low <- (BArray1024.get256d lows (W64.to_uint offset));
      hints <- (BArray1024.get256d hint_polynomial (W64.to_uint offset));
      hints <- (VPSIGN_8u32 hints low);
      high <- (BArray1024.get256d highs (W64.to_uint offset));
      coefficients <- (VPADD_8u32 high hints);
      coefficients <- (VPAND_256 coefficients mask);
      commitment <-
      (BArray1024.set256d commitment (W64.to_uint offset) coefficients);
      offset <- (offset + (W64.of_int 32));
    }
    return commitment;
  }
  proc polynomial____make_hint (hints:BArray1024.t,
                                low_coefficients:BArray1024.t,
                                high_coefficients:BArray1024.t) : BArray1024.t *
                                                                  W64.t = {
    var weight:W64.t;
    var temp:W64.t;
    var gamma2:W256.t;
    var minus_gamma2:W256.t;
    var offset:W64.t;
    var low:W256.t;
    var high:W256.t;
    var abs_low:W256.t;
    var low_out_of_bounds:W256.t;
    var low_equals_minus_gamma2_and_high_is_nonzero:W256.t;
    var hint_block:W256.t;
    var num_hints:W64.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    temp <- (W64.of_int ((8380417 - 1) %/ 32));
    gamma2 <- (zeroextu256 (VMOV_64 temp));
    gamma2 <- (VPBROADCAST_8u32 (truncateu32 gamma2));
    temp <- (W64.of_int (- ((8380417 - 1) %/ 32)));
    minus_gamma2 <- (zeroextu256 (VMOV_64 temp));
    minus_gamma2 <- (VPBROADCAST_8u32 (truncateu32 minus_gamma2));
    weight <- (W64.of_int 0);
    offset <- (W64.of_int 0);
    while ((offset \ult (W64.of_int ((256 * 32) %/ 8)))) {
      low <- (BArray1024.get256d low_coefficients (W64.to_uint offset));
      high <- (BArray1024.get256d high_coefficients (W64.to_uint offset));
      abs_low <- (VPABS_8u32 low);
      low_out_of_bounds <- (VPCMPGT_8u32 abs_low gamma2);
      low_equals_minus_gamma2_and_high_is_nonzero <-
      (VPCMPEQ_8u32 low minus_gamma2);
      low_equals_minus_gamma2_and_high_is_nonzero <-
      (VPSIGN_8u32 low_equals_minus_gamma2_and_high_is_nonzero high);
      hint_block <-
      (VPOR_256 low_out_of_bounds low_equals_minus_gamma2_and_high_is_nonzero
      );
      hint_block <- hint_block;
      num_hints <- (zeroextu64 (MOVEMASK_8u32 hint_block));
      ( _0,  _1,  _2,  _3,  _4, num_hints) <- (POPCNT_64 num_hints);
      hint_block <- (VPSRL_8u32 hint_block (W128.of_int 31));
      hints <- (BArray1024.set256d hints (W64.to_uint offset) hint_block);
      offset <- (offset + (W64.of_int 32));
      weight <- (weight + num_hints);
    }
    return (hints, weight);
  }
  proc polynomial____power2round (highbits:BArray1024.t,
                                  lowbits:BArray1024.t,
                                  polynomial:BArray1024.t) : BArray1024.t *
                                                             BArray1024.t = {
    var half_t0_bits:W256.t;
    var temp:W64.t;
    var ones_vector:W256.t;
    var offset:W64.t;
    var coefficients:W256.t;
    var high:W256.t;
    var low:W256.t;
    half_t0_bits <- hALF_OF_BITS_IN_T0_VECTOR;
    temp <- (W64.of_int 1);
    ones_vector <- (zeroextu256 (VMOV_64 temp));
    ones_vector <- (VPBROADCAST_8u32 (truncateu32 ones_vector));
    offset <- (W64.of_int 0);
    while ((offset \ult (W64.of_int ((256 * 32) %/ 8)))) {
      coefficients <- (BArray1024.get256d polynomial (W64.to_uint offset));
      high <- (VPADD_8u32 coefficients half_t0_bits);
      high <- (VPSUB_8u32 high ones_vector);
      high <- (VPSRA_8u32 high (W128.of_int 13));
      low <- (VPSLL_8u32 high (W128.of_int 13));
      low <- (VPSUB_8u32 coefficients low);
      highbits <- (BArray1024.set256d highbits (W64.to_uint offset) high);
      lowbits <- (BArray1024.set256d lowbits (W64.to_uint offset) low);
      offset <- (offset + (W64.of_int 32));
    }
    return (highbits, lowbits);
  }
  proc montgomery_multiply_and_reduce (lhs:W256.t, rhs:W256.t) : W256.t = {
    var product_low:W256.t;
    var lhs_high:W256.t;
    var rhs_high:W256.t;
    var product_high:W256.t;
    var t_low:W256.t;
    var t_high:W256.t;
    lhs_high <- (VMOVSHDUP_256 lhs);
    rhs_high <- (VMOVSHDUP_256 rhs);
    product_low <- (VPMUL_256 lhs rhs);
    product_high <- (VPMUL_256 lhs_high rhs_high);
    t_low <-
    (VPMUL_256 product_low iNVERSE_OF_MODULUS_MOD_MONTGOMERY_R_VECTOR);
    t_high <-
    (VPMUL_256 product_high iNVERSE_OF_MODULUS_MOD_MONTGOMERY_R_VECTOR);
    t_low <- (VPMUL_256 t_low mODULUS_VECTOR);
    t_high <- (VPMUL_256 t_high mODULUS_VECTOR);
    product_low <- (VPSUB_4u64 product_low t_low);
    product_high <- (VPSUB_4u64 product_high t_high);
    product_low <- (VMOVSHDUP_256 product_low);
    product_low <- (VPBLEND_8u32 product_low product_high (W8.of_int 170));
    return product_low;
  }
  proc polynomial__pointwise_montgomery_multiply_and_reduce (product:BArray1024.t,
                                                             lhs:BArray1024.t,
                                                             rhs:BArray1024.t) : 
  BArray1024.t = {
    var offset:W64.t;
    var lhs_coeffs:W256.t;
    var rhs_coeffs:W256.t;
    var product_coeffs:W256.t;
    offset <- (W64.of_int 0);
    while ((offset \ult (W64.of_int ((256 * 32) %/ 8)))) {
      lhs_coeffs <- (BArray1024.get256d lhs (W64.to_uint offset));
      rhs_coeffs <- (BArray1024.get256d rhs (W64.to_uint offset));
      product_coeffs <@ montgomery_multiply_and_reduce (lhs_coeffs,
      rhs_coeffs);
      product <-
      (BArray1024.set256d product (W64.to_uint offset) product_coeffs);
      offset <- (offset + (W64.of_int 32));
      lhs_coeffs <- (BArray1024.get256d lhs (W64.to_uint offset));
      rhs_coeffs <- (BArray1024.get256d rhs (W64.to_uint offset));
      product_coeffs <@ montgomery_multiply_and_reduce (lhs_coeffs,
      rhs_coeffs);
      product <-
      (BArray1024.set256d product (W64.to_uint offset) product_coeffs);
      offset <- (offset + (W64.of_int 32));
    }
    return product;
  }
  proc polynomial__conditionally_add_modulus (polynomial:BArray1024.t) : 
  BArray1024.t = {
    var modulus:W256.t;
    var zero:W256.t;
    var offset:W64.t;
    var lhs:W256.t;
    var mask:W256.t;
    var rhs:W256.t;
    modulus <- mODULUS_VECTOR;
    zero <- (set0_256);
    offset <- (W64.of_int 0);
    while ((offset \ult (W64.of_int ((256 * 32) %/ 8)))) {
      lhs <- (BArray1024.get256d polynomial (W64.to_uint offset));
      mask <- (VPCMPGT_8u32 zero lhs);
      rhs <- (VPAND_256 modulus mask);
      lhs <- (VPADD_8u32 lhs rhs);
      polynomial <- (BArray1024.set256d polynomial (W64.to_uint offset) lhs);
      offset <- (offset + (W64.of_int 32));
    }
    return polynomial;
  }
  proc polynomial__reduce32 (polynomial:BArray1024.t) : BArray1024.t = {
    var two_pow_22:W256.t;
    var modulus:W256.t;
    var offset:W64.t;
    var a:W256.t;
    var t:W256.t;
    two_pow_22 <- tWO_POW_22_VECTOR;
    modulus <- mODULUS_VECTOR;
    offset <- (W64.of_int 0);
    while ((offset \ult (W64.of_int ((256 * 32) %/ 8)))) {
      a <- (BArray1024.get256d polynomial (W64.to_uint offset));
      t <- (VPADD_8u32 a two_pow_22);
      t <- (VPSRA_8u32 t (W128.of_int 23));
      t <- (VPMULL_8u32 t modulus);
      a <- (VPSUB_8u32 a t);
      polynomial <- (BArray1024.set256d polynomial (W64.to_uint offset) a);
      offset <- (offset + (W64.of_int 32));
    }
    return polynomial;
  }
  proc polynomial__butterfly_2 (polynomial:BArray1024.t, start:W64.t,
                                zetas:W256.t) : BArray1024.t = {
    var lhs_start:W64.t;
    var lhs:W256.t;
    var rhs_start:W64.t;
    var rhs:W256.t;
    var summands:W256.t;
    var zeta_products:W256.t;
    var add_terms:W256.t;
    var sub_terms:W256.t;
    lhs_start <- start;
    lhs_start <- (lhs_start * (W64.of_int 32));
    lhs <- (BArray1024.get256d polynomial (W64.to_uint lhs_start));
    lhs <- (VPSHUFD_256 lhs (W8.of_int 216));
    rhs_start <- lhs_start;
    rhs_start <- (rhs_start + (W64.of_int 32));
    rhs <- (BArray1024.get256d polynomial (W64.to_uint rhs_start));
    rhs <- (VPSHUFD_256 rhs (W8.of_int 216));
    summands <- (VPUNPCKL_4u64 lhs rhs);
    zeta_products <- (VPUNPCKH_4u64 lhs rhs);
    zeta_products <@ montgomery_multiply_and_reduce (zeta_products, zetas);
    add_terms <- (VPADD_8u32 summands zeta_products);
    sub_terms <- (VPSUB_8u32 summands zeta_products);
    lhs <- (VPUNPCKL_4u64 add_terms sub_terms);
    lhs <- (VPSHUFD_256 lhs (W8.of_int 216));
    rhs <- (VPUNPCKH_4u64 add_terms sub_terms);
    rhs <- (VPSHUFD_256 rhs (W8.of_int 216));
    polynomial <-
    (BArray1024.set256d polynomial (W64.to_uint lhs_start) lhs);
    polynomial <-
    (BArray1024.set256d polynomial (W64.to_uint rhs_start) rhs);
    return polynomial;
  }
  proc polynomial__ntt_at_layer_0 (polynomial:BArray1024.t) : BArray1024.t = {
    var i:int;
    var start:W64.t;
    var zetas:W256.t;
    i <- 0;
    while ((i < 16)) {
      start <- (W64.of_int (i * 2));
      zetas <- (BArray512.get256 lAYER_0_ZETAS i);
      polynomial <@ polynomial__butterfly_2 (polynomial, start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__butterfly_4 (polynomial:BArray1024.t, start:W64.t,
                                zetas:W256.t) : BArray1024.t = {
    var lhs_start:W64.t;
    var lhs:W256.t;
    var rhs_start:W64.t;
    var rhs:W256.t;
    var summands:W256.t;
    var zeta_products:W256.t;
    var add_terms:W256.t;
    var sub_terms:W256.t;
    lhs_start <- start;
    lhs_start <- (lhs_start * (W64.of_int 32));
    lhs <- (BArray1024.get256d polynomial (W64.to_uint lhs_start));
    rhs_start <- lhs_start;
    rhs_start <- (rhs_start + (W64.of_int 32));
    rhs <- (BArray1024.get256d polynomial (W64.to_uint rhs_start));
    summands <- (VPUNPCKL_4u64 lhs rhs);
    zeta_products <- (VPUNPCKH_4u64 lhs rhs);
    zeta_products <@ montgomery_multiply_and_reduce (zeta_products, zetas);
    add_terms <- (VPADD_8u32 summands zeta_products);
    sub_terms <- (VPSUB_8u32 summands zeta_products);
    lhs <- (VPUNPCKL_4u64 add_terms sub_terms);
    polynomial <-
    (BArray1024.set256d polynomial (W64.to_uint lhs_start) lhs);
    rhs <- (VPUNPCKH_4u64 add_terms sub_terms);
    polynomial <-
    (BArray1024.set256d polynomial (W64.to_uint rhs_start) rhs);
    return polynomial;
  }
  proc polynomial__ntt_at_layer_1 (polynomial:BArray1024.t) : BArray1024.t = {
    var i:int;
    var start:W64.t;
    var zetas:W256.t;
    i <- 0;
    while ((i < 16)) {
      start <- (W64.of_int (i * 2));
      zetas <- (BArray512.get256 lAYER_1_ZETAS i);
      polynomial <@ polynomial__butterfly_4 (polynomial, start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__butterfly_8 (polynomial:BArray1024.t, start:W64.t,
                                zetas:W256.t) : BArray1024.t = {
    var lhs_start:W64.t;
    var lhs:W256.t;
    var lhs_truncated:W128.t;
    var rhs_start:W64.t;
    var rhs:W256.t;
    var rhs_truncated:W128.t;
    var summands:W256.t;
    var zeta_products:W256.t;
    var add_terms:W256.t;
    var sub_terms:W256.t;
    lhs_start <- start;
    lhs_start <- (lhs_start * (W64.of_int 32));
    lhs <- (BArray1024.get256d polynomial (W64.to_uint lhs_start));
    lhs_truncated <- (truncateu128 lhs);
    rhs_start <- lhs_start;
    rhs_start <- (rhs_start + (W64.of_int 32));
    rhs <- (BArray1024.get256d polynomial (W64.to_uint rhs_start));
    rhs_truncated <- (truncateu128 rhs);
    summands <- (set0_256);
    summands <- (VINSERTI128 summands lhs_truncated (W8.of_int 0));
    summands <- (VINSERTI128 summands rhs_truncated (W8.of_int 1));
    zeta_products <- (VPERM2I128 rhs lhs (W8.of_int 19));
    zeta_products <@ montgomery_multiply_and_reduce (zeta_products, zetas);
    add_terms <- (VPADD_8u32 summands zeta_products);
    sub_terms <- (VPSUB_8u32 summands zeta_products);
    lhs_truncated <- (truncateu128 add_terms);
    rhs_truncated <- (truncateu128 sub_terms);
    lhs <- (VINSERTI128 lhs lhs_truncated (W8.of_int 0));
    lhs <- (VINSERTI128 lhs rhs_truncated (W8.of_int 1));
    polynomial <-
    (BArray1024.set256d polynomial (W64.to_uint lhs_start) lhs);
    rhs <- (VPERM2I128 sub_terms add_terms (W8.of_int 19));
    polynomial <-
    (BArray1024.set256d polynomial (W64.to_uint rhs_start) rhs);
    return polynomial;
  }
  proc polynomial__ntt_at_layer_2 (polynomial:BArray1024.t) : BArray1024.t = {
    var i:int;
    var start:W64.t;
    var zetas:W256.t;
    i <- 0;
    while ((i < 16)) {
      start <- (W64.of_int (i * 2));
      zetas <- (BArray512.get256 lAYER_2_ZETAS i);
      polynomial <@ polynomial__butterfly_8 (polynomial, start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__ntt_round (polynomial:BArray1024.t, step:W64.t,
                              step_by:W64.t, start:W64.t, zetas:W256.t) : 
  BArray1024.t = {
    var offset:W64.t;
    var i:W64.t;
    var bound:W64.t;
    var index:W64.t;
    var coeffs_i:W256.t;
    var index_plus_step:W64.t;
    var coeffs_i_plus_step:W256.t;
    var product:W256.t;
    offset <- start;
    offset <- (offset * step);
    offset <- (offset * (W64.of_int 2));
    offset <- (offset `>>` (W8.of_int 3));
    i <- offset;
    bound <- offset;
    bound <- (bound + step_by);
    while ((i \ult bound)) {
      index <- i;
      index <- (index * (W64.of_int 32));
      coeffs_i <- (BArray1024.get256d polynomial (W64.to_uint index));
      index_plus_step <- i;
      index_plus_step <- (index_plus_step + step_by);
      index_plus_step <- (index_plus_step * (W64.of_int 32));
      coeffs_i_plus_step <-
      (BArray1024.get256d polynomial (W64.to_uint index_plus_step));
      product <@ montgomery_multiply_and_reduce (coeffs_i_plus_step, zetas);
      coeffs_i_plus_step <- (VPSUB_8u32 coeffs_i product);
      polynomial <-
      (BArray1024.set256d polynomial (W64.to_uint index_plus_step)
      coeffs_i_plus_step);
      coeffs_i <- (VPADD_8u32 coeffs_i product);
      polynomial <-
      (BArray1024.set256d polynomial (W64.to_uint index) coeffs_i);
      i <- (i + (W64.of_int 1));
    }
    return polynomial;
  }
  proc polynomial__ntt_at_layer_3 (polynomial:BArray1024.t) : BArray1024.t = {
    var step:W64.t;
    var step_by:W64.t;
    var i:int;
    var start:W64.t;
    var zetas:W256.t;
    step <- (W64.of_int (1 `<<` 3));
    step_by <- (W64.of_int ((1 `<<` 3) %/ 8));
    i <- 0;
    while ((i < 16)) {
      start <- (W64.of_int i);
      zetas <- (BArray512.get256 lAYER_3_ZETAS i);
      polynomial <@ polynomial__ntt_round (polynomial, step, step_by, 
      start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__ntt_at_layer_4 (polynomial:BArray1024.t) : BArray1024.t = {
    var step:W64.t;
    var step_by:W64.t;
    var i:int;
    var start:W64.t;
    var zetas:W256.t;
    step <- (W64.of_int (1 `<<` 4));
    step_by <- (W64.of_int ((1 `<<` 4) %/ 8));
    i <- 0;
    while ((i < 8)) {
      start <- (W64.of_int i);
      zetas <- (BArray256.get256 lAYER_4_ZETAS i);
      polynomial <@ polynomial__ntt_round (polynomial, step, step_by, 
      start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__ntt_at_layer_5 (polynomial:BArray1024.t) : BArray1024.t = {
    var step:W64.t;
    var step_by:W64.t;
    var i:int;
    var start:W64.t;
    var zetas:W256.t;
    step <- (W64.of_int (1 `<<` 5));
    step_by <- (W64.of_int ((1 `<<` 5) %/ 8));
    i <- 0;
    while ((i < 4)) {
      start <- (W64.of_int i);
      zetas <- (BArray128.get256 lAYER_5_ZETAS i);
      polynomial <@ polynomial__ntt_round (polynomial, step, step_by, 
      start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__multiply (polynomial:BArray1024.t, start:W64.t,
                             step_by:W64.t, zeta_0:W32.t) : BArray1024.t = {
    var index_i_plus_step_by:W64.t;
    var coeffs_i_plus_step_by:W256.t;
    var constants:W256.t;
    var prod02:W256.t;
    var prod13:W256.t;
    var c02:W256.t;
    var c13:W256.t;
    var res02:W256.t;
    var res13:W256.t;
    var t:W256.t;
    var index_i:W64.t;
    var coeffs_i:W256.t;
    index_i_plus_step_by <- start;
    index_i_plus_step_by <- (index_i_plus_step_by + step_by);
    index_i_plus_step_by <- (index_i_plus_step_by * (W64.of_int 32));
    coeffs_i_plus_step_by <-
    (BArray1024.get256d polynomial (W64.to_uint index_i_plus_step_by));
    constants <- (zeroextu256 (VMOV_32 zeta_0));
    constants <- (VPBROADCAST_8u32 (truncateu32 constants));
    prod02 <- (VPMUL_256 coeffs_i_plus_step_by constants);
    coeffs_i_plus_step_by <-
    (VPSHUFD_256 coeffs_i_plus_step_by (W8.of_int 245));
    constants <- (VPSHUFD_256 constants (W8.of_int 245));
    prod13 <- (VPMUL_256 coeffs_i_plus_step_by constants);
    constants <- iNVERSE_OF_MODULUS_MOD_MONTGOMERY_R_VECTOR;
    c02 <- (VPMUL_256 prod02 constants);
    c13 <- (VPMUL_256 prod13 constants);
    constants <- mODULUS_VECTOR;
    c02 <- (VPMUL_256 c02 constants);
    c13 <- (VPMUL_256 c13 constants);
    res02 <- (VPSUB_8u32 prod02 c02);
    res13 <- (VPSUB_8u32 prod13 c13);
    res02 <- (VPSHUFD_256 res02 (W8.of_int 245));
    t <-
    (VPBLEND_8u32 res02 res13
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    index_i <- start;
    index_i <- (index_i * (W64.of_int 32));
    coeffs_i <- (BArray1024.get256d polynomial (W64.to_uint index_i));
    coeffs_i_plus_step_by <- (VPSUB_8u32 coeffs_i t);
    polynomial <-
    (BArray1024.set256d polynomial (W64.to_uint index_i_plus_step_by)
    coeffs_i_plus_step_by);
    coeffs_i <- (VPADD_8u32 coeffs_i t);
    polynomial <-
    (BArray1024.set256d polynomial (W64.to_uint index_i) coeffs_i);
    return polynomial;
  }
  proc polynomial____layer (polynomial:BArray1024.t, _start:int,
                            _step_by:int, _zeta:int) : BArray1024.t = {
    var step_by:W64.t;
    var zeta_0:W64.t;
    var i:int;
    var start:W64.t;
    step_by <- (W64.of_int _step_by);
    zeta_0 <- (W64.of_int _zeta);
    i <- 0;
    while ((i < 4)) {
      start <- (W64.of_int (_start + i));
      polynomial <@ polynomial__multiply (polynomial, start, step_by,
      (truncateu32 zeta_0));
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__ntt_at_layer_7_and_6 (polynomial:BArray1024.t) : BArray1024.t = {
    var sTEP_BY_7:int;
    var sTEP_BY_6:int;
    var zETA_7:int;
    var zETA_60:int;
    var zETA_61:int;
    sTEP_BY_7 <- (2 * 8);
    sTEP_BY_6 <- ((1 `<<` 6) %/ 8);
    zETA_7 <- 25847;
    zETA_60 <- (- 2608894);
    zETA_61 <- (- 518909);
    polynomial <@ polynomial____layer (polynomial, 0, sTEP_BY_7, zETA_7);
    polynomial <@ polynomial____layer (polynomial, 8, sTEP_BY_7, zETA_7);
    polynomial <@ polynomial____layer (polynomial, 0, sTEP_BY_6, zETA_60);
    polynomial <@ polynomial____layer (polynomial, 16, sTEP_BY_6, zETA_61);
    polynomial <@ polynomial____layer (polynomial, 4, sTEP_BY_7, zETA_7);
    polynomial <@ polynomial____layer (polynomial, 12, sTEP_BY_7, zETA_7);
    polynomial <@ polynomial____layer (polynomial, 4, sTEP_BY_6, zETA_60);
    polynomial <@ polynomial____layer (polynomial, 20, sTEP_BY_6, zETA_61);
    return polynomial;
  }
  proc polynomial__ntt (polynomial:BArray1024.t) : BArray1024.t = {
    
    polynomial <@ polynomial__ntt_at_layer_7_and_6 (polynomial);
    polynomial <@ polynomial__ntt_at_layer_5 (polynomial);
    polynomial <@ polynomial__ntt_at_layer_4 (polynomial);
    polynomial <@ polynomial__ntt_at_layer_3 (polynomial);
    polynomial <@ polynomial__ntt_at_layer_2 (polynomial);
    polynomial <@ polynomial__ntt_at_layer_1 (polynomial);
    polynomial <@ polynomial__ntt_at_layer_0 (polynomial);
    return polynomial;
  }
  proc polynomial__invert_at_layer_0 (polynomial:BArray1024.t, start:W64.t,
                                      zetas:W256.t) : BArray1024.t = {
    var coeffs_i_start:W64.t;
    var coeffs_i:W256.t;
    var coeffs_i_plus_1_start:W64.t;
    var coeffs_i_plus_1:W256.t;
    var low_values:W256.t;
    var high_values:W256.t;
    var differences:W256.t;
    var sums:W256.t;
    coeffs_i_start <- start;
    coeffs_i_start <- (coeffs_i_start * (W64.of_int 32));
    coeffs_i <- (BArray1024.get256d polynomial (W64.to_uint coeffs_i_start));
    coeffs_i <- (VPSHUFD_256 coeffs_i (W8.of_int 216));
    coeffs_i_plus_1_start <- coeffs_i_start;
    coeffs_i_plus_1_start <- (coeffs_i_plus_1_start + (W64.of_int 32));
    coeffs_i_plus_1 <-
    (BArray1024.get256d polynomial (W64.to_uint coeffs_i_plus_1_start));
    coeffs_i_plus_1 <- (VPSHUFD_256 coeffs_i_plus_1 (W8.of_int 216));
    low_values <- (VPUNPCKL_4u64 coeffs_i coeffs_i_plus_1);
    high_values <- (VPUNPCKH_4u64 coeffs_i coeffs_i_plus_1);
    differences <- (VPSUB_8u32 high_values low_values);
    sums <- (VPADD_8u32 high_values low_values);
    differences <@ montgomery_multiply_and_reduce (differences, zetas);
    coeffs_i <- (VPUNPCKL_4u64 sums differences);
    coeffs_i_plus_1 <- (VPUNPCKH_4u64 sums differences);
    coeffs_i <- (VPSHUFD_256 coeffs_i (W8.of_int 216));
    coeffs_i_plus_1 <- (VPSHUFD_256 coeffs_i_plus_1 (W8.of_int 216));
    polynomial <-
    (BArray1024.set256d polynomial (W64.to_uint coeffs_i_start) coeffs_i);
    polynomial <-
    (BArray1024.set256d polynomial (W64.to_uint coeffs_i_plus_1_start)
    coeffs_i_plus_1);
    return polynomial;
  }
  proc polynomial__invert_ntt_at_layer_0 (polynomial:BArray1024.t) : 
  BArray1024.t = {
    var i:int;
    var start:W64.t;
    var zetas:W256.t;
    i <- 0;
    while ((i < 16)) {
      start <- (W64.of_int (i * 2));
      zetas <- (BArray512.get256 zETAS_TO_INVERT_LAYER_0 i);
      polynomial <@ polynomial__invert_at_layer_0 (polynomial, start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_at_layer_1 (polynomial:BArray1024.t, start:W64.t,
                                      zetas:W256.t) : BArray1024.t = {
    var coeffs_i_start:W64.t;
    var coeffs_i:W256.t;
    var coeffs_i_plus_1_start:W64.t;
    var coeffs_i_plus_1:W256.t;
    var low_values:W256.t;
    var high_values:W256.t;
    var differences:W256.t;
    var sums:W256.t;
    coeffs_i_start <- start;
    coeffs_i_start <- (coeffs_i_start * (W64.of_int 32));
    coeffs_i <- (BArray1024.get256d polynomial (W64.to_uint coeffs_i_start));
    coeffs_i_plus_1_start <- coeffs_i_start;
    coeffs_i_plus_1_start <- (coeffs_i_plus_1_start + (W64.of_int 32));
    coeffs_i_plus_1 <-
    (BArray1024.get256d polynomial (W64.to_uint coeffs_i_plus_1_start));
    low_values <- (VPUNPCKL_4u64 coeffs_i coeffs_i_plus_1);
    high_values <- (VPUNPCKH_4u64 coeffs_i coeffs_i_plus_1);
    differences <- (VPSUB_8u32 high_values low_values);
    sums <- (VPADD_8u32 high_values low_values);
    differences <@ montgomery_multiply_and_reduce (differences, zetas);
    coeffs_i <- (VPUNPCKL_4u64 sums differences);
    coeffs_i_plus_1 <- (VPUNPCKH_4u64 sums differences);
    polynomial <-
    (BArray1024.set256d polynomial (W64.to_uint coeffs_i_start) coeffs_i);
    polynomial <-
    (BArray1024.set256d polynomial (W64.to_uint coeffs_i_plus_1_start)
    coeffs_i_plus_1);
    return polynomial;
  }
  proc polynomial__invert_ntt_at_layer_1 (polynomial:BArray1024.t) : 
  BArray1024.t = {
    var i:int;
    var start:W64.t;
    var zetas:W256.t;
    i <- 0;
    while ((i < 16)) {
      start <- (W64.of_int (i * 2));
      zetas <- (BArray512.get256 zETAS_TO_INVERT_LAYER_1 i);
      polynomial <@ polynomial__invert_at_layer_1 (polynomial, start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_at_layer_2 (polynomial:BArray1024.t, start:W64.t,
                                      zetas:W256.t) : BArray1024.t = {
    var coeffs_i_start:W64.t;
    var coeffs_i:W256.t;
    var coeffs_i_plus_1_start:W64.t;
    var coeffs_i_plus_1:W256.t;
    var low_values:W256.t;
    var high_values:W256.t;
    var differences:W256.t;
    var sums:W256.t;
    coeffs_i_start <- start;
    coeffs_i_start <- (coeffs_i_start * (W64.of_int 32));
    coeffs_i <- (BArray1024.get256d polynomial (W64.to_uint coeffs_i_start));
    coeffs_i_plus_1_start <- coeffs_i_start;
    coeffs_i_plus_1_start <- (coeffs_i_plus_1_start + (W64.of_int 32));
    coeffs_i_plus_1 <-
    (BArray1024.get256d polynomial (W64.to_uint coeffs_i_plus_1_start));
    low_values <- (VPERM2I128 coeffs_i coeffs_i_plus_1 (W8.of_int 32));
    high_values <- (VPERM2I128 coeffs_i coeffs_i_plus_1 (W8.of_int 49));
    differences <- (VPSUB_8u32 high_values low_values);
    sums <- (VPADD_8u32 high_values low_values);
    differences <@ montgomery_multiply_and_reduce (differences, zetas);
    coeffs_i <- (VPERM2I128 sums differences (W8.of_int 32));
    coeffs_i_plus_1 <- (VPERM2I128 sums differences (W8.of_int 49));
    polynomial <-
    (BArray1024.set256d polynomial (W64.to_uint coeffs_i_start) coeffs_i);
    polynomial <-
    (BArray1024.set256d polynomial (W64.to_uint coeffs_i_plus_1_start)
    coeffs_i_plus_1);
    return polynomial;
  }
  proc polynomial__invert_ntt_at_layer_2 (polynomial:BArray1024.t) : 
  BArray1024.t = {
    var i:int;
    var start:W64.t;
    var zetas:W256.t;
    i <- 0;
    while ((i < 16)) {
      start <- (W64.of_int (i * 2));
      zetas <- (BArray512.get256 zETAS_TO_INVERT_LAYER_2 i);
      polynomial <@ polynomial__invert_at_layer_2 (polynomial, start, zetas);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_ntt_round (polynomial:BArray1024.t, offset:W64.t,
                                     step_by:W64.t, zeta_0:W32.t) : BArray1024.t = {
    var zetas:W256.t;
    var i:W64.t;
    var index_i:W64.t;
    var coeffs_i:W256.t;
    var index_i_plus_step_by:W64.t;
    var coeffs_i_plus_step_by:W256.t;
    var a_minus_b:W256.t;
    zetas <- (zeroextu256 (VMOV_32 zeta_0));
    zetas <- (VPBROADCAST_8u32 (truncateu32 zetas));
    i <- offset;
    offset <- (offset + step_by);
    while ((i \ult offset)) {
      index_i <- i;
      index_i <- (index_i * (W64.of_int 32));
      coeffs_i <- (BArray1024.get256d polynomial (W64.to_uint index_i));
      index_i_plus_step_by <- i;
      index_i_plus_step_by <- (index_i_plus_step_by + step_by);
      index_i_plus_step_by <- (index_i_plus_step_by * (W64.of_int 32));
      coeffs_i_plus_step_by <-
      (BArray1024.get256d polynomial (W64.to_uint index_i_plus_step_by));
      a_minus_b <- (VPSUB_8u32 coeffs_i_plus_step_by coeffs_i);
      coeffs_i <- (VPADD_8u32 coeffs_i coeffs_i_plus_step_by);
      coeffs_i_plus_step_by <@ montgomery_multiply_and_reduce (a_minus_b,
      zetas);
      polynomial <-
      (BArray1024.set256d polynomial (W64.to_uint index_i) coeffs_i);
      polynomial <-
      (BArray1024.set256d polynomial (W64.to_uint index_i_plus_step_by)
      coeffs_i_plus_step_by);
      i <- (i + (W64.of_int 1));
    }
    return polynomial;
  }
  proc polynomial__invert_ntt_at_layer_3 (polynomial:BArray1024.t) : 
  BArray1024.t = {
    var sTEP:int;
    var sTEP_BY:int;
    var i:int;
    var offset:W64.t;
    var step_by:W64.t;
    var zeta_0:W32.t;
    sTEP <- 8;
    sTEP_BY <- (sTEP %/ 8);
    i <- 0;
    while ((i < 16)) {
      offset <- (W64.of_int (((i * sTEP) * 2) %/ 8));
      step_by <- (W64.of_int sTEP_BY);
      zeta_0 <- (BArray64.get32 zETAS_TO_INVERT_LAYER_3 i);
      polynomial <@ polynomial__invert_ntt_round (polynomial, offset,
      step_by, zeta_0);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_ntt_at_layer_4 (polynomial:BArray1024.t) : 
  BArray1024.t = {
    var sTEP:int;
    var sTEP_BY:int;
    var i:int;
    var offset:W64.t;
    var step_by:W64.t;
    var zeta_0:W32.t;
    sTEP <- 16;
    sTEP_BY <- (sTEP %/ 8);
    i <- 0;
    while ((i < 8)) {
      offset <- (W64.of_int (((i * sTEP) * 2) %/ 8));
      step_by <- (W64.of_int sTEP_BY);
      zeta_0 <- (BArray32.get32 zETAS_TO_INVERT_LAYER_4 i);
      polynomial <@ polynomial__invert_ntt_round (polynomial, offset,
      step_by, zeta_0);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_ntt_at_layer_5 (polynomial:BArray1024.t) : 
  BArray1024.t = {
    var sTEP:int;
    var sTEP_BY:int;
    var i:int;
    var offset:W64.t;
    var step_by:W64.t;
    var zeta_0:W32.t;
    sTEP <- 32;
    sTEP_BY <- (sTEP %/ 8);
    i <- 0;
    while ((i < 4)) {
      offset <- (W64.of_int (((i * sTEP) * 2) %/ 8));
      step_by <- (W64.of_int sTEP_BY);
      zeta_0 <- (BArray16.get32 zETAS_TO_INVERT_LAYER_5 i);
      polynomial <@ polynomial__invert_ntt_round (polynomial, offset,
      step_by, zeta_0);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_ntt_at_layer_6 (polynomial:BArray1024.t) : 
  BArray1024.t = {
    var sTEP:int;
    var sTEP_BY:int;
    var i:int;
    var offset:W64.t;
    var step_by:W64.t;
    var zeta_0:W32.t;
    sTEP <- 64;
    sTEP_BY <- (sTEP %/ 8);
    i <- 0;
    while ((i < 2)) {
      offset <- (W64.of_int (((i * sTEP) * 2) %/ 8));
      step_by <- (W64.of_int sTEP_BY);
      zeta_0 <- (BArray8.get32 zETAS_TO_INVERT_LAYER_6 i);
      polynomial <@ polynomial__invert_ntt_round (polynomial, offset,
      step_by, zeta_0);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_ntt_at_layer_7 (polynomial:BArray1024.t) : 
  BArray1024.t = {
    var sTEP:int;
    var sTEP_BY:int;
    var i:int;
    var offset:W64.t;
    var step_by:W64.t;
    var zeta_0:W32.t;
    sTEP <- 128;
    sTEP_BY <- (sTEP %/ 8);
    i <- 0;
    while ((i < 1)) {
      offset <- (W64.of_int (((i * sTEP) * 2) %/ 8));
      step_by <- (W64.of_int sTEP_BY);
      zeta_0 <- (W32.of_int 25847);
      polynomial <@ polynomial__invert_ntt_round (polynomial, offset,
      step_by, zeta_0);
      i <- (i + 1);
    }
    return polynomial;
  }
  proc polynomial__invert_ntt_montgomery (polynomial:BArray1024.t) : 
  BArray1024.t = {
    var temp:W64.t;
    var twiddle_factors:W256.t;
    var i:W64.t;
    var coefficients:W256.t;
    polynomial <@ polynomial__invert_ntt_at_layer_0 (polynomial);
    polynomial <@ polynomial__invert_ntt_at_layer_1 (polynomial);
    polynomial <@ polynomial__invert_ntt_at_layer_2 (polynomial);
    polynomial <@ polynomial__invert_ntt_at_layer_3 (polynomial);
    polynomial <@ polynomial__invert_ntt_at_layer_4 (polynomial);
    polynomial <@ polynomial__invert_ntt_at_layer_5 (polynomial);
    polynomial <@ polynomial__invert_ntt_at_layer_6 (polynomial);
    polynomial <@ polynomial__invert_ntt_at_layer_7 (polynomial);
    temp <- (W64.of_int 41978);
    twiddle_factors <- (zeroextu256 (VMOV_32 (truncateu32 temp)));
    twiddle_factors <- (VPBROADCAST_8u32 (truncateu32 twiddle_factors));
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int ((256 * 32) %/ 8)))) {
      coefficients <- (BArray1024.get256d polynomial (W64.to_uint i));
      coefficients <@ montgomery_multiply_and_reduce (coefficients,
      twiddle_factors);
      polynomial <-
      (BArray1024.set256d polynomial (W64.to_uint i) coefficients);
      i <- (i + (W64.of_int 32));
    }
    return polynomial;
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
    var zeros_u256:W256.t;
    var zero_u64:W64.t;
    var i:int;
    zeros_u256 <- (set0_256);
    zero_u64 <- (W64.of_int 0);
    i <- 0;
    while ((i < 6)) {
      state <- (BArray200.set256d state (i * 32) zeros_u256);
      i <- (i + 1);
    }
    state <- (BArray200.set64d state 192 zero_u64);
    return state;
  }
  proc __keccakf1600_pround_avx2 (state:BArray224.t) : BArray224.t = {
    var c00:W256.t;
    var c14:W256.t;
    var t2:W256.t;
    var t4:W256.t;
    var t0:W256.t;
    var t1:W256.t;
    var d14:W256.t;
    var d00:W256.t;
    var t3:W256.t;
    var t5:W256.t;
    var t6:W256.t;
    var t7:W256.t;
    var t8:W256.t;
    c00 <-
    (VPSHUFD_256 (BArray224.get256 state 2)
    (W8.of_int
    ((2 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 1))))))));
    c14 <- ((BArray224.get256 state 5) `^` (BArray224.get256 state 3));
    t2 <- ((BArray224.get256 state 4) `^` (BArray224.get256 state 6));
    c14 <- (c14 `^` (BArray224.get256 state 1));
    c14 <- (c14 `^` t2);
    t4 <-
    (VPERMQ c14
    (W8.of_int
    ((3 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((0 %% (2 ^ 2)) + ((2 ^ 2) * ((1 %% (2 ^ 2)) + ((2 ^ 2) * 2))))))));
    c00 <- (c00 `^` (BArray224.get256 state 2));
    t0 <-
    (VPERMQ c00
    (W8.of_int
    ((2 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 1))))))));
    t1 <- (c14 \vshr64u256 (W128.of_int 63));
    t2 <- (c14 \vadd64u256 c14);
    t1 <- (t1 `|` t2);
    d14 <-
    (VPERMQ t1
    (W8.of_int
    ((1 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((2 %% (2 ^ 2)) + ((2 ^ 2) * ((3 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    d00 <- (t1 `^` t4);
    d00 <-
    (VPERMQ d00
    (W8.of_int
    ((0 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((0 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    c00 <- (c00 `^` (BArray224.get256 state 0));
    c00 <- (c00 `^` t0);
    t0 <- (c00 \vshr64u256 (W128.of_int 63));
    t1 <- (c00 \vadd64u256 c00);
    t1 <- (t1 `|` t0);
    state <- (BArray224.set256 state 2 ((BArray224.get256 state 2) `^` d00));
    state <- (BArray224.set256 state 0 ((BArray224.get256 state 0) `^` d00));
    d14 <-
    (VPBLEND_8u32 d14 t1
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t4 <-
    (VPBLEND_8u32 t4 c00
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    d14 <- (d14 `^` t4);
    t3 <-
    (VPSLLV_4u64 (BArray224.get256 state 2)
    (BArray192.get256 kECCAK_RHOTATES_LEFT 0));
    state <-
    (BArray224.set256 state 2
    (VPSRLV_4u64 (BArray224.get256 state 2)
    (BArray192.get256 kECCAK_RHOTATES_RIGHT 0)));
    state <- (BArray224.set256 state 2 ((BArray224.get256 state 2) `|` t3));
    state <- (BArray224.set256 state 3 ((BArray224.get256 state 3) `^` d14));
    t4 <-
    (VPSLLV_4u64 (BArray224.get256 state 3)
    (BArray192.get256 kECCAK_RHOTATES_LEFT 2));
    state <-
    (BArray224.set256 state 3
    (VPSRLV_4u64 (BArray224.get256 state 3)
    (BArray192.get256 kECCAK_RHOTATES_RIGHT 2)));
    state <- (BArray224.set256 state 3 ((BArray224.get256 state 3) `|` t4));
    state <- (BArray224.set256 state 4 ((BArray224.get256 state 4) `^` d14));
    t5 <-
    (VPSLLV_4u64 (BArray224.get256 state 4)
    (BArray192.get256 kECCAK_RHOTATES_LEFT 3));
    state <-
    (BArray224.set256 state 4
    (VPSRLV_4u64 (BArray224.get256 state 4)
    (BArray192.get256 kECCAK_RHOTATES_RIGHT 3)));
    state <- (BArray224.set256 state 4 ((BArray224.get256 state 4) `|` t5));
    state <- (BArray224.set256 state 5 ((BArray224.get256 state 5) `^` d14));
    t6 <-
    (VPSLLV_4u64 (BArray224.get256 state 5)
    (BArray192.get256 kECCAK_RHOTATES_LEFT 4));
    state <-
    (BArray224.set256 state 5
    (VPSRLV_4u64 (BArray224.get256 state 5)
    (BArray192.get256 kECCAK_RHOTATES_RIGHT 4)));
    state <- (BArray224.set256 state 5 ((BArray224.get256 state 5) `|` t6));
    state <- (BArray224.set256 state 6 ((BArray224.get256 state 6) `^` d14));
    t3 <-
    (VPERMQ (BArray224.get256 state 2)
    (W8.of_int
    ((1 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 2))))))));
    t4 <-
    (VPERMQ (BArray224.get256 state 3)
    (W8.of_int
    ((1 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 2))))))));
    t7 <-
    (VPSLLV_4u64 (BArray224.get256 state 6)
    (BArray192.get256 kECCAK_RHOTATES_LEFT 5));
    t1 <-
    (VPSRLV_4u64 (BArray224.get256 state 6)
    (BArray192.get256 kECCAK_RHOTATES_RIGHT 5));
    t1 <- (t1 `|` t7);
    state <- (BArray224.set256 state 1 ((BArray224.get256 state 1) `^` d14));
    t5 <-
    (VPERMQ (BArray224.get256 state 4)
    (W8.of_int
    ((3 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((2 %% (2 ^ 2)) + ((2 ^ 2) * ((1 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    t6 <-
    (VPERMQ (BArray224.get256 state 5)
    (W8.of_int
    ((2 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((0 %% (2 ^ 2)) + ((2 ^ 2) * ((3 %% (2 ^ 2)) + ((2 ^ 2) * 1))))))));
    t8 <-
    (VPSLLV_4u64 (BArray224.get256 state 1)
    (BArray192.get256 kECCAK_RHOTATES_LEFT 1));
    t2 <-
    (VPSRLV_4u64 (BArray224.get256 state 1)
    (BArray192.get256 kECCAK_RHOTATES_RIGHT 1));
    t2 <- (t2 `|` t8);
    t7 <- (VPSRLDQ_256 t1 (W8.of_int 8));
    t0 <- ((invw t1) `&` t7);
    state <-
    (BArray224.set256 state 3
    (VPBLEND_8u32 t2 t6
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    )));
    t8 <-
    (VPBLEND_8u32 t4 t2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state <-
    (BArray224.set256 state 5
    (VPBLEND_8u32 t3 t4
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    )));
    t7 <-
    (VPBLEND_8u32 t2 t3
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state <-
    (BArray224.set256 state 3
    (VPBLEND_8u32 (BArray224.get256 state 3) t4
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    )));
    t8 <-
    (VPBLEND_8u32 t8 t5
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state <-
    (BArray224.set256 state 5
    (VPBLEND_8u32 (BArray224.get256 state 5) t2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    )));
    t7 <-
    (VPBLEND_8u32 t7 t6
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state <-
    (BArray224.set256 state 3
    (VPBLEND_8u32 (BArray224.get256 state 3) t5
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    )));
    t8 <-
    (VPBLEND_8u32 t8 t6
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state <-
    (BArray224.set256 state 5
    (VPBLEND_8u32 (BArray224.get256 state 5) t6
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    )));
    t7 <-
    (VPBLEND_8u32 t7 t4
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state <-
    (BArray224.set256 state 3 ((invw (BArray224.get256 state 3)) `&` t8));
    state <-
    (BArray224.set256 state 5 ((invw (BArray224.get256 state 5)) `&` t7));
    state <-
    (BArray224.set256 state 6
    (VPBLEND_8u32 t5 t2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    )));
    t8 <-
    (VPBLEND_8u32 t3 t5
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state <- (BArray224.set256 state 3 ((BArray224.get256 state 3) `^` t3));
    state <-
    (BArray224.set256 state 6
    (VPBLEND_8u32 (BArray224.get256 state 6) t3
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    )));
    t8 <-
    (VPBLEND_8u32 t8 t4
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state <- (BArray224.set256 state 5 ((BArray224.get256 state 5) `^` t5));
    state <-
    (BArray224.set256 state 6
    (VPBLEND_8u32 (BArray224.get256 state 6) t4
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    )));
    t8 <-
    (VPBLEND_8u32 t8 t2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state <-
    (BArray224.set256 state 6 ((invw (BArray224.get256 state 6)) `&` t8));
    state <- (BArray224.set256 state 6 ((BArray224.get256 state 6) `^` t6));
    state <-
    (BArray224.set256 state 4
    (VPERMQ t1
    (W8.of_int
    ((2 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((1 %% (2 ^ 2)) + ((2 ^ 2) * 0)))))))));
    t8 <-
    (VPBLEND_8u32 (BArray224.get256 state 4) (BArray224.get256 state 0)
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state <-
    (BArray224.set256 state 1
    (VPERMQ t1
    (W8.of_int
    ((1 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((2 %% (2 ^ 2)) + ((2 ^ 2) * ((3 %% (2 ^ 2)) + ((2 ^ 2) * 0)))))))));
    state <-
    (BArray224.set256 state 1
    (VPBLEND_8u32 (BArray224.get256 state 1) (BArray224.get256 state 0)
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    )));
    state <-
    (BArray224.set256 state 1 ((invw (BArray224.get256 state 1)) `&` t8));
    state <-
    (BArray224.set256 state 2
    (VPBLEND_8u32 t4 t5
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    )));
    t7 <-
    (VPBLEND_8u32 t6 t4
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state <-
    (BArray224.set256 state 2
    (VPBLEND_8u32 (BArray224.get256 state 2) t6
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    )));
    t7 <-
    (VPBLEND_8u32 t7 t3
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state <-
    (BArray224.set256 state 2
    (VPBLEND_8u32 (BArray224.get256 state 2) t3
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    )));
    t7 <-
    (VPBLEND_8u32 t7 t5
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state <-
    (BArray224.set256 state 2 ((invw (BArray224.get256 state 2)) `&` t7));
    state <- (BArray224.set256 state 2 ((BArray224.get256 state 2) `^` t2));
    t0 <-
    (VPERMQ t0
    (W8.of_int
    ((0 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((0 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 0))))))));
    state <-
    (BArray224.set256 state 3
    (VPERMQ (BArray224.get256 state 3)
    (W8.of_int
    ((3 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((2 %% (2 ^ 2)) + ((2 ^ 2) * ((1 %% (2 ^ 2)) + ((2 ^ 2) * 0)))))))));
    state <-
    (BArray224.set256 state 5
    (VPERMQ (BArray224.get256 state 5)
    (W8.of_int
    ((1 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((3 %% (2 ^ 2)) + ((2 ^ 2) * ((0 %% (2 ^ 2)) + ((2 ^ 2) * 2)))))))));
    state <-
    (BArray224.set256 state 6
    (VPERMQ (BArray224.get256 state 6)
    (W8.of_int
    ((2 %% (2 ^ 2)) +
    ((2 ^ 2) *
    ((0 %% (2 ^ 2)) + ((2 ^ 2) * ((3 %% (2 ^ 2)) + ((2 ^ 2) * 1)))))))));
    state <-
    (BArray224.set256 state 4
    (VPBLEND_8u32 t6 t3
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    )));
    t7 <-
    (VPBLEND_8u32 t5 t6
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state <-
    (BArray224.set256 state 4
    (VPBLEND_8u32 (BArray224.get256 state 4) t5
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    )));
    t7 <-
    (VPBLEND_8u32 t7 t2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((0 %% (2 ^ 1)) + ((2 ^ 1) * 0))))))))))))))
    ));
    state <-
    (BArray224.set256 state 4
    (VPBLEND_8u32 (BArray224.get256 state 4) t2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    )));
    t7 <-
    (VPBLEND_8u32 t7 t3
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    state <-
    (BArray224.set256 state 4 ((invw (BArray224.get256 state 4)) `&` t7));
    state <- (BArray224.set256 state 0 ((BArray224.get256 state 0) `^` t0));
    state <- (BArray224.set256 state 1 ((BArray224.get256 state 1) `^` t1));
    state <- (BArray224.set256 state 4 ((BArray224.get256 state 4) `^` t4));
    return state;
  }
  proc _keccakf1600_avx2 (state:BArray224.t) : BArray224.t = {
    var round_constants:BArray192.t;
    var r:W64.t;
    var rc:W256.t;
    round_constants <- witness;
    round_constants <- kECCAK1600_RC;
    r <- (W64.of_int 0);
    state <@ __keccakf1600_pround_avx2 (state);
    rc <-
    (VPBROADCAST_4u64 (BArray192.get64 round_constants (W64.to_uint r)));
    state <- (BArray224.set256 state 0 ((BArray224.get256 state 0) `^` rc));
    r <- (r + (W64.of_int 1));
    while ((r \ult (W64.of_int 24))) {
      state <@ __keccakf1600_pround_avx2 (state);
      rc <-
      (VPBROADCAST_4u64 (BArray192.get64 round_constants (W64.to_uint r)));
      state <-
      (BArray224.set256 state 0 ((BArray224.get256 state 0) `^` rc));
      r <- (r + (W64.of_int 1));
    }
    return state;
  }
  proc __state_init_avx2 () : BArray224.t = {
    var st:BArray224.t;
    var i:int;
    st <- witness;
    i <- 0;
    while ((i < 7)) {
      st <- (BArray224.set256 st i (set0_256));
      i <- (i + 1);
    }
    return st;
  }
  proc __perm_reg3456_avx2 (r3:W256.t, r4:W256.t, r5:W256.t, r6:W256.t) : 
  W256.t * W256.t * W256.t * W256.t = {
    var st3:W256.t;
    var st4:W256.t;
    var st5:W256.t;
    var st6:W256.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    t256_0 <-
    (VPBLEND_8u32 r3 r5
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_1 <-
    (VPBLEND_8u32 r6 r4
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_2 <-
    (VPBLEND_8u32 r4 r3
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    st3 <-
    (VPBLEND_8u32 t256_0 t256_1
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    st4 <-
    (VPBLEND_8u32 t256_1 t256_0
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_0 <-
    (VPBLEND_8u32 r5 r6
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    st5 <-
    (VPBLEND_8u32 t256_0 t256_2
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    st6 <-
    (VPBLEND_8u32 t256_2 t256_0
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    return (st3, st4, st5, st6);
  }
  proc __addstate_r3456_avx2 (st:BArray224.t, r3:W256.t, r4:W256.t,
                              r5:W256.t, r6:W256.t) : BArray224.t = {
    
    (r3, r4, r5, r6) <@ __perm_reg3456_avx2 (r3, r4, r5, r6);
    st <- (BArray224.set256 st 3 ((BArray224.get256 st 3) `^` r3));
    st <- (BArray224.set256 st 4 ((BArray224.get256 st 4) `^` r4));
    st <- (BArray224.set256 st 5 ((BArray224.get256 st 5) `^` r5));
    st <- (BArray224.set256 st 6 ((BArray224.get256 st 6) `^` r6));
    return st;
  }
  proc __rol_4u64_rho56 (a:W256.t) : W256.t = {
    var r:W256.t;
    r <- (VPSHUFB_256 a rho56);
    return r;
  }
  proc __rol_4u64_rho8 (a:W256.t) : W256.t = {
    var r:W256.t;
    r <- (VPSHUFB_256 a rho8);
    return r;
  }
  proc __rol_4u64 (a:W256.t, o:int) : W256.t = {
    var r:W256.t;
    var t256:W256.t;
    r <- (VPSLL_4u64 a (W128.of_int o));
    t256 <- (VPSRL_4u64 a (W128.of_int (64 - o)));
    r <- (r `|` t256);
    return r;
  }
  proc __prepare_theta (a_4x:BArray800.t) : W256.t * W256.t * W256.t *
                                            W256.t * W256.t = {
    var ca:W256.t;
    var ce:W256.t;
    var ci:W256.t;
    var co:W256.t;
    var cu:W256.t;
    ca <- (BArray800.get256 a_4x 20);
    ca <- (ca `^` (BArray800.get256 a_4x 15));
    ca <- (ca `^` (BArray800.get256 a_4x 10));
    ca <- (ca `^` (BArray800.get256 a_4x 5));
    ca <- (ca `^` (BArray800.get256 a_4x 0));
    ce <- (BArray800.get256 a_4x 21);
    ce <- (ce `^` (BArray800.get256 a_4x 16));
    ce <- (ce `^` (BArray800.get256 a_4x 11));
    ce <- (ce `^` (BArray800.get256 a_4x 6));
    ce <- (ce `^` (BArray800.get256 a_4x 1));
    ci <- (BArray800.get256 a_4x 22);
    ci <- (ci `^` (BArray800.get256 a_4x 17));
    ci <- (ci `^` (BArray800.get256 a_4x 12));
    ci <- (ci `^` (BArray800.get256 a_4x 7));
    ci <- (ci `^` (BArray800.get256 a_4x 2));
    co <- (BArray800.get256 a_4x 23);
    co <- (co `^` (BArray800.get256 a_4x 18));
    co <- (co `^` (BArray800.get256 a_4x 13));
    co <- (co `^` (BArray800.get256 a_4x 8));
    co <- (co `^` (BArray800.get256 a_4x 3));
    cu <- (BArray800.get256 a_4x 24);
    cu <- (cu `^` (BArray800.get256 a_4x 19));
    cu <- (cu `^` (BArray800.get256 a_4x 14));
    cu <- (cu `^` (BArray800.get256 a_4x 9));
    cu <- (cu `^` (BArray800.get256 a_4x 4));
    return (ca, ce, ci, co, cu);
  }
  proc __first (ca:W256.t, ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t) : 
  W256.t * W256.t * W256.t * W256.t * W256.t = {
    var da:W256.t;
    var de:W256.t;
    var di:W256.t;
    var do_0:W256.t;
    var du:W256.t;
    var ce1:W256.t;
    var ci1:W256.t;
    var co1:W256.t;
    var cu1:W256.t;
    var ca1:W256.t;
    ce1 <@ __rol_4u64 (ce, 1);
    da <- (cu `^` ce1);
    ci1 <@ __rol_4u64 (ci, 1);
    de <- (ca `^` ci1);
    co1 <@ __rol_4u64 (co, 1);
    di <- (ce `^` co1);
    cu1 <@ __rol_4u64 (cu, 1);
    do_0 <- (ci `^` cu1);
    ca1 <@ __rol_4u64 (ca, 1);
    du <- (co `^` ca1);
    return (da, de, di, do_0, du);
  }
  proc __second_even (a_4x:BArray800.t, e_4x:BArray800.t, index:int,
                      ca:W256.t, ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t,
                      da:W256.t, de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  BArray800.t * BArray800.t * W256.t * W256.t * W256.t * W256.t * W256.t = {
    var t256:W256.t;
    var bba:W256.t;
    var bbe:W256.t;
    var bbi:W256.t;
    var bbo:W256.t;
    var bbu:W256.t;
    t256 <- (BArray800.get256 a_4x 0);
    t256 <- (t256 `^` da);
    a_4x <- (BArray800.set256 a_4x 0 t256);
    bba <- t256;
    t256 <- (BArray800.get256 a_4x 6);
    t256 <- (t256 `^` de);
    a_4x <- (BArray800.set256 a_4x 6 t256);
    bbe <@ __rol_4u64 (t256, 44);
    t256 <- (BArray800.get256 a_4x 12);
    t256 <- (t256 `^` di);
    a_4x <- (BArray800.set256 a_4x 12 t256);
    bbi <@ __rol_4u64 (t256, 43);
    t256 <- (VPANDN_256 bbe bbi);
    t256 <- (t256 `^` bba);
    t256 <- (t256 `^` (BArray768.get256 keccakF1600RoundConstants index));
    e_4x <- (BArray800.set256 e_4x 0 t256);
    ca <- t256;
    t256 <- (BArray800.get256 a_4x 18);
    t256 <- (t256 `^` do_0);
    a_4x <- (BArray800.set256 a_4x 18 t256);
    bbo <@ __rol_4u64 (t256, 21);
    t256 <- (VPANDN_256 bbi bbo);
    t256 <- (t256 `^` bbe);
    e_4x <- (BArray800.set256 e_4x 1 t256);
    ce <- t256;
    t256 <- (BArray800.get256 a_4x 24);
    t256 <- (t256 `^` du);
    a_4x <- (BArray800.set256 a_4x 24 t256);
    bbu <@ __rol_4u64 (t256, 14);
    t256 <- (VPANDN_256 bbo bbu);
    t256 <- (t256 `^` bbi);
    e_4x <- (BArray800.set256 e_4x 2 t256);
    ci <- t256;
    t256 <- (VPANDN_256 bbu bba);
    t256 <- (t256 `^` bbo);
    e_4x <- (BArray800.set256 e_4x 3 t256);
    co <- t256;
    t256 <- (VPANDN_256 bba bbe);
    t256 <- (t256 `^` bbu);
    e_4x <- (BArray800.set256 e_4x 4 t256);
    cu <- t256;
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __third_even (a_4x:BArray800.t, e_4x:BArray800.t, ca:W256.t,
                     ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  BArray800.t * BArray800.t * W256.t * W256.t * W256.t * W256.t * W256.t = {
    var t256:W256.t;
    var bga:W256.t;
    var bge:W256.t;
    var bgi:W256.t;
    var bgo:W256.t;
    var bgu:W256.t;
    t256 <- (BArray800.get256 a_4x 3);
    t256 <- (t256 `^` do_0);
    a_4x <- (BArray800.set256 a_4x 3 t256);
    bga <@ __rol_4u64 (t256, 28);
    t256 <- (BArray800.get256 a_4x 9);
    t256 <- (t256 `^` du);
    a_4x <- (BArray800.set256 a_4x 9 t256);
    bge <@ __rol_4u64 (t256, 20);
    t256 <- (BArray800.get256 a_4x 10);
    t256 <- (t256 `^` da);
    a_4x <- (BArray800.set256 a_4x 10 t256);
    bgi <@ __rol_4u64 (t256, 3);
    t256 <- (VPANDN_256 bge bgi);
    t256 <- (t256 `^` bga);
    e_4x <- (BArray800.set256 e_4x 5 t256);
    ca <- (ca `^` t256);
    t256 <- (BArray800.get256 a_4x 16);
    t256 <- (t256 `^` de);
    a_4x <- (BArray800.set256 a_4x 16 t256);
    bgo <@ __rol_4u64 (t256, 45);
    t256 <- (VPANDN_256 bgi bgo);
    t256 <- (t256 `^` bge);
    e_4x <- (BArray800.set256 e_4x 6 t256);
    ce <- (ce `^` t256);
    t256 <- (BArray800.get256 a_4x 22);
    t256 <- (t256 `^` di);
    a_4x <- (BArray800.set256 a_4x 22 t256);
    bgu <@ __rol_4u64 (t256, 61);
    t256 <- (VPANDN_256 bgo bgu);
    t256 <- (t256 `^` bgi);
    e_4x <- (BArray800.set256 e_4x 7 t256);
    ci <- (ci `^` t256);
    t256 <- (VPANDN_256 bgu bga);
    t256 <- (t256 `^` bgo);
    e_4x <- (BArray800.set256 e_4x 8 t256);
    co <- (co `^` t256);
    t256 <- (VPANDN_256 bga bge);
    t256 <- (t256 `^` bgu);
    e_4x <- (BArray800.set256 e_4x 9 t256);
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __fourth_even (a_4x:BArray800.t, e_4x:BArray800.t, ca:W256.t,
                      ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                      de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  BArray800.t * BArray800.t * W256.t * W256.t * W256.t * W256.t * W256.t = {
    var t256:W256.t;
    var bka:W256.t;
    var bke:W256.t;
    var bki:W256.t;
    var bko:W256.t;
    var bku:W256.t;
    t256 <- (BArray800.get256 a_4x 1);
    t256 <- (t256 `^` de);
    a_4x <- (BArray800.set256 a_4x 1 t256);
    bka <@ __rol_4u64 (t256, 1);
    t256 <- (BArray800.get256 a_4x 7);
    t256 <- (t256 `^` di);
    a_4x <- (BArray800.set256 a_4x 7 t256);
    bke <@ __rol_4u64 (t256, 6);
    t256 <- (BArray800.get256 a_4x 13);
    t256 <- (t256 `^` do_0);
    a_4x <- (BArray800.set256 a_4x 13 t256);
    bki <@ __rol_4u64 (t256, 25);
    t256 <- (VPANDN_256 bke bki);
    t256 <- (t256 `^` bka);
    e_4x <- (BArray800.set256 e_4x 10 t256);
    ca <- (ca `^` t256);
    t256 <- (BArray800.get256 a_4x 19);
    t256 <- (t256 `^` du);
    a_4x <- (BArray800.set256 a_4x 19 t256);
    bko <@ __rol_4u64_rho8 (t256);
    t256 <- (VPANDN_256 bki bko);
    t256 <- (t256 `^` bke);
    e_4x <- (BArray800.set256 e_4x 11 t256);
    ce <- (ce `^` t256);
    t256 <- (BArray800.get256 a_4x 20);
    t256 <- (t256 `^` da);
    a_4x <- (BArray800.set256 a_4x 20 t256);
    bku <@ __rol_4u64 (t256, 18);
    t256 <- (VPANDN_256 bko bku);
    t256 <- (t256 `^` bki);
    e_4x <- (BArray800.set256 e_4x 12 t256);
    ci <- (ci `^` t256);
    t256 <- (VPANDN_256 bku bka);
    t256 <- (t256 `^` bko);
    e_4x <- (BArray800.set256 e_4x 13 t256);
    co <- (co `^` t256);
    t256 <- (VPANDN_256 bka bke);
    t256 <- (t256 `^` bku);
    e_4x <- (BArray800.set256 e_4x 14 t256);
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __fifth_even (a_4x:BArray800.t, e_4x:BArray800.t, ca:W256.t,
                     ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  BArray800.t * BArray800.t * W256.t * W256.t * W256.t * W256.t * W256.t = {
    var t256:W256.t;
    var bma:W256.t;
    var bme:W256.t;
    var bmi:W256.t;
    var bmo:W256.t;
    var bmu:W256.t;
    t256 <- (BArray800.get256 a_4x 4);
    t256 <- (t256 `^` du);
    a_4x <- (BArray800.set256 a_4x 4 t256);
    bma <@ __rol_4u64 (t256, 27);
    t256 <- (BArray800.get256 a_4x 5);
    t256 <- (t256 `^` da);
    a_4x <- (BArray800.set256 a_4x 5 t256);
    bme <@ __rol_4u64 (t256, 36);
    t256 <- (BArray800.get256 a_4x 11);
    t256 <- (t256 `^` de);
    a_4x <- (BArray800.set256 a_4x 11 t256);
    bmi <@ __rol_4u64 (t256, 10);
    t256 <- (VPANDN_256 bme bmi);
    t256 <- (t256 `^` bma);
    e_4x <- (BArray800.set256 e_4x 15 t256);
    ca <- (ca `^` t256);
    t256 <- (BArray800.get256 a_4x 17);
    t256 <- (t256 `^` di);
    a_4x <- (BArray800.set256 a_4x 17 t256);
    bmo <@ __rol_4u64 (t256, 15);
    t256 <- (VPANDN_256 bmi bmo);
    t256 <- (t256 `^` bme);
    e_4x <- (BArray800.set256 e_4x 16 t256);
    ce <- (ce `^` t256);
    t256 <- (BArray800.get256 a_4x 23);
    t256 <- (t256 `^` do_0);
    a_4x <- (BArray800.set256 a_4x 23 t256);
    bmu <@ __rol_4u64_rho56 (t256);
    t256 <- (VPANDN_256 bmo bmu);
    t256 <- (t256 `^` bmi);
    e_4x <- (BArray800.set256 e_4x 17 t256);
    ci <- (ci `^` t256);
    t256 <- (VPANDN_256 bmu bma);
    t256 <- (t256 `^` bmo);
    e_4x <- (BArray800.set256 e_4x 18 t256);
    co <- (co `^` t256);
    t256 <- (VPANDN_256 bma bme);
    t256 <- (t256 `^` bmu);
    e_4x <- (BArray800.set256 e_4x 19 t256);
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __sixth_even (a_4x:BArray800.t, e_4x:BArray800.t, ca:W256.t,
                     ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  BArray800.t * BArray800.t * W256.t * W256.t * W256.t * W256.t * W256.t = {
    var t256:W256.t;
    var bsa:W256.t;
    var bse:W256.t;
    var bsi:W256.t;
    var bso:W256.t;
    var bsu:W256.t;
    t256 <- (BArray800.get256 a_4x 2);
    t256 <- (t256 `^` di);
    a_4x <- (BArray800.set256 a_4x 2 t256);
    bsa <@ __rol_4u64 (t256, 62);
    t256 <- (BArray800.get256 a_4x 8);
    t256 <- (t256 `^` do_0);
    a_4x <- (BArray800.set256 a_4x 8 t256);
    bse <@ __rol_4u64 (t256, 55);
    t256 <- (BArray800.get256 a_4x 14);
    t256 <- (t256 `^` du);
    a_4x <- (BArray800.set256 a_4x 14 t256);
    bsi <@ __rol_4u64 (t256, 39);
    t256 <- (VPANDN_256 bse bsi);
    t256 <- (t256 `^` bsa);
    e_4x <- (BArray800.set256 e_4x 20 t256);
    ca <- (ca `^` t256);
    t256 <- (BArray800.get256 a_4x 15);
    t256 <- (t256 `^` da);
    a_4x <- (BArray800.set256 a_4x 15 t256);
    bso <@ __rol_4u64 (t256, 41);
    t256 <- (VPANDN_256 bsi bso);
    t256 <- (t256 `^` bse);
    e_4x <- (BArray800.set256 e_4x 21 t256);
    ce <- (ce `^` t256);
    t256 <- (BArray800.get256 a_4x 21);
    t256 <- (t256 `^` de);
    a_4x <- (BArray800.set256 a_4x 21 t256);
    bsu <@ __rol_4u64 (t256, 2);
    t256 <- (VPANDN_256 bso bsu);
    t256 <- (t256 `^` bsi);
    e_4x <- (BArray800.set256 e_4x 22 t256);
    ci <- (ci `^` t256);
    t256 <- (VPANDN_256 bsu bsa);
    t256 <- (t256 `^` bso);
    e_4x <- (BArray800.set256 e_4x 23 t256);
    co <- (co `^` t256);
    t256 <- (VPANDN_256 bsa bse);
    t256 <- (t256 `^` bsu);
    e_4x <- (BArray800.set256 e_4x 24 t256);
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __second_odd (a_4x:BArray800.t, e_4x:BArray800.t, index:int,
                     ca:W256.t, ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t,
                     da:W256.t, de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  BArray800.t * BArray800.t * W256.t * W256.t * W256.t * W256.t * W256.t = {
    var t256:W256.t;
    var bba:W256.t;
    var bbe:W256.t;
    var bbi:W256.t;
    var bbo:W256.t;
    var bbu:W256.t;
    t256 <- (BArray800.get256 a_4x 0);
    t256 <- (t256 `^` da);
    a_4x <- (BArray800.set256 a_4x 0 t256);
    bba <- t256;
    t256 <- (BArray800.get256 a_4x 6);
    t256 <- (t256 `^` de);
    a_4x <- (BArray800.set256 a_4x 6 t256);
    bbe <@ __rol_4u64 (t256, 44);
    t256 <- (BArray800.get256 a_4x 12);
    t256 <- (t256 `^` di);
    a_4x <- (BArray800.set256 a_4x 12 t256);
    bbi <@ __rol_4u64 (t256, 43);
    t256 <- (VPANDN_256 bbe bbi);
    t256 <- (t256 `^` bba);
    t256 <- (t256 `^` (BArray768.get256 keccakF1600RoundConstants index));
    e_4x <- (BArray800.set256 e_4x 0 t256);
    ca <- t256;
    t256 <- (BArray800.get256 a_4x 18);
    t256 <- (t256 `^` do_0);
    a_4x <- (BArray800.set256 a_4x 18 t256);
    bbo <@ __rol_4u64 (t256, 21);
    t256 <- (VPANDN_256 bbi bbo);
    t256 <- (t256 `^` bbe);
    e_4x <- (BArray800.set256 e_4x 1 t256);
    ce <- t256;
    t256 <- (BArray800.get256 a_4x 24);
    t256 <- (t256 `^` du);
    a_4x <- (BArray800.set256 a_4x 24 t256);
    bbu <@ __rol_4u64 (t256, 14);
    t256 <- (VPANDN_256 bbo bbu);
    t256 <- (t256 `^` bbi);
    e_4x <- (BArray800.set256 e_4x 2 t256);
    ci <- t256;
    t256 <- (VPANDN_256 bbu bba);
    t256 <- (t256 `^` bbo);
    e_4x <- (BArray800.set256 e_4x 3 t256);
    co <- t256;
    t256 <- (VPANDN_256 bba bbe);
    t256 <- (t256 `^` bbu);
    e_4x <- (BArray800.set256 e_4x 4 t256);
    cu <- t256;
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __third_odd (a_4x:BArray800.t, e_4x:BArray800.t, ca:W256.t, ce:W256.t,
                    ci:W256.t, co:W256.t, cu:W256.t, da:W256.t, de:W256.t,
                    di:W256.t, do_0:W256.t, du:W256.t) : BArray800.t *
                                                         BArray800.t *
                                                         W256.t * W256.t *
                                                         W256.t * W256.t *
                                                         W256.t = {
    var t256:W256.t;
    var bga:W256.t;
    var bge:W256.t;
    var bgi:W256.t;
    var bgo:W256.t;
    var bgu:W256.t;
    t256 <- (BArray800.get256 a_4x 3);
    t256 <- (t256 `^` do_0);
    a_4x <- (BArray800.set256 a_4x 3 t256);
    bga <@ __rol_4u64 (t256, 28);
    t256 <- (BArray800.get256 a_4x 9);
    t256 <- (t256 `^` du);
    a_4x <- (BArray800.set256 a_4x 9 t256);
    bge <@ __rol_4u64 (t256, 20);
    t256 <- (BArray800.get256 a_4x 10);
    t256 <- (t256 `^` da);
    a_4x <- (BArray800.set256 a_4x 10 t256);
    bgi <@ __rol_4u64 (t256, 3);
    t256 <- (VPANDN_256 bge bgi);
    t256 <- (t256 `^` bga);
    e_4x <- (BArray800.set256 e_4x 5 t256);
    ca <- (ca `^` t256);
    t256 <- (BArray800.get256 a_4x 16);
    t256 <- (t256 `^` de);
    a_4x <- (BArray800.set256 a_4x 16 t256);
    bgo <@ __rol_4u64 (t256, 45);
    t256 <- (VPANDN_256 bgi bgo);
    t256 <- (t256 `^` bge);
    e_4x <- (BArray800.set256 e_4x 6 t256);
    ce <- (ce `^` t256);
    t256 <- (BArray800.get256 a_4x 22);
    t256 <- (t256 `^` di);
    a_4x <- (BArray800.set256 a_4x 22 t256);
    bgu <@ __rol_4u64 (t256, 61);
    t256 <- (VPANDN_256 bgo bgu);
    t256 <- (t256 `^` bgi);
    e_4x <- (BArray800.set256 e_4x 7 t256);
    ci <- (ci `^` t256);
    t256 <- (VPANDN_256 bgu bga);
    t256 <- (t256 `^` bgo);
    e_4x <- (BArray800.set256 e_4x 8 t256);
    co <- (co `^` t256);
    t256 <- (VPANDN_256 bga bge);
    t256 <- (t256 `^` bgu);
    e_4x <- (BArray800.set256 e_4x 9 t256);
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __fourth_odd (a_4x:BArray800.t, e_4x:BArray800.t, ca:W256.t,
                     ce:W256.t, ci:W256.t, co:W256.t, cu:W256.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  BArray800.t * BArray800.t * W256.t * W256.t * W256.t * W256.t * W256.t = {
    var t256:W256.t;
    var bka:W256.t;
    var bke:W256.t;
    var bki:W256.t;
    var bko:W256.t;
    var bku:W256.t;
    t256 <- (BArray800.get256 a_4x 1);
    t256 <- (t256 `^` de);
    a_4x <- (BArray800.set256 a_4x 1 t256);
    bka <@ __rol_4u64 (t256, 1);
    t256 <- (BArray800.get256 a_4x 7);
    t256 <- (t256 `^` di);
    a_4x <- (BArray800.set256 a_4x 7 t256);
    bke <@ __rol_4u64 (t256, 6);
    t256 <- (BArray800.get256 a_4x 13);
    t256 <- (t256 `^` do_0);
    a_4x <- (BArray800.set256 a_4x 13 t256);
    bki <@ __rol_4u64 (t256, 25);
    t256 <- (VPANDN_256 bke bki);
    t256 <- (t256 `^` bka);
    e_4x <- (BArray800.set256 e_4x 10 t256);
    ca <- (ca `^` t256);
    t256 <- (BArray800.get256 a_4x 19);
    t256 <- (t256 `^` du);
    a_4x <- (BArray800.set256 a_4x 19 t256);
    bko <@ __rol_4u64_rho8 (t256);
    t256 <- (VPANDN_256 bki bko);
    t256 <- (t256 `^` bke);
    e_4x <- (BArray800.set256 e_4x 11 t256);
    ce <- (ce `^` t256);
    t256 <- (BArray800.get256 a_4x 20);
    t256 <- (t256 `^` da);
    a_4x <- (BArray800.set256 a_4x 20 t256);
    bku <@ __rol_4u64 (t256, 18);
    t256 <- (VPANDN_256 bko bku);
    t256 <- (t256 `^` bki);
    e_4x <- (BArray800.set256 e_4x 12 t256);
    ci <- (ci `^` t256);
    t256 <- (VPANDN_256 bku bka);
    t256 <- (t256 `^` bko);
    e_4x <- (BArray800.set256 e_4x 13 t256);
    co <- (co `^` t256);
    t256 <- (VPANDN_256 bka bke);
    t256 <- (t256 `^` bku);
    e_4x <- (BArray800.set256 e_4x 14 t256);
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __fifth_odd (a_4x:BArray800.t, e_4x:BArray800.t, ca:W256.t, ce:W256.t,
                    ci:W256.t, co:W256.t, cu:W256.t, da:W256.t, de:W256.t,
                    di:W256.t, do_0:W256.t, du:W256.t) : BArray800.t *
                                                         BArray800.t *
                                                         W256.t * W256.t *
                                                         W256.t * W256.t *
                                                         W256.t = {
    var t256:W256.t;
    var bma:W256.t;
    var bme:W256.t;
    var bmi:W256.t;
    var bmo:W256.t;
    var bmu:W256.t;
    t256 <- (BArray800.get256 a_4x 4);
    t256 <- (t256 `^` du);
    a_4x <- (BArray800.set256 a_4x 4 t256);
    bma <@ __rol_4u64 (t256, 27);
    t256 <- (BArray800.get256 a_4x 5);
    t256 <- (t256 `^` da);
    a_4x <- (BArray800.set256 a_4x 5 t256);
    bme <@ __rol_4u64 (t256, 36);
    t256 <- (BArray800.get256 a_4x 11);
    t256 <- (t256 `^` de);
    a_4x <- (BArray800.set256 a_4x 11 t256);
    bmi <@ __rol_4u64 (t256, 10);
    t256 <- (VPANDN_256 bme bmi);
    t256 <- (t256 `^` bma);
    e_4x <- (BArray800.set256 e_4x 15 t256);
    ca <- (ca `^` t256);
    t256 <- (BArray800.get256 a_4x 17);
    t256 <- (t256 `^` di);
    a_4x <- (BArray800.set256 a_4x 17 t256);
    bmo <@ __rol_4u64 (t256, 15);
    t256 <- (VPANDN_256 bmi bmo);
    t256 <- (t256 `^` bme);
    e_4x <- (BArray800.set256 e_4x 16 t256);
    ce <- (ce `^` t256);
    t256 <- (BArray800.get256 a_4x 23);
    t256 <- (t256 `^` do_0);
    a_4x <- (BArray800.set256 a_4x 23 t256);
    bmu <@ __rol_4u64_rho56 (t256);
    t256 <- (VPANDN_256 bmo bmu);
    t256 <- (t256 `^` bmi);
    e_4x <- (BArray800.set256 e_4x 17 t256);
    ci <- (ci `^` t256);
    t256 <- (VPANDN_256 bmu bma);
    t256 <- (t256 `^` bmo);
    e_4x <- (BArray800.set256 e_4x 18 t256);
    co <- (co `^` t256);
    t256 <- (VPANDN_256 bma bme);
    t256 <- (t256 `^` bmu);
    e_4x <- (BArray800.set256 e_4x 19 t256);
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __sixth_odd (a_4x:BArray800.t, e_4x:BArray800.t, ca:W256.t, ce:W256.t,
                    ci:W256.t, co:W256.t, cu:W256.t, da:W256.t, de:W256.t,
                    di:W256.t, do_0:W256.t, du:W256.t) : BArray800.t *
                                                         BArray800.t *
                                                         W256.t * W256.t *
                                                         W256.t * W256.t *
                                                         W256.t = {
    var t256:W256.t;
    var bsa:W256.t;
    var bse:W256.t;
    var bsi:W256.t;
    var bso:W256.t;
    var bsu:W256.t;
    t256 <- (BArray800.get256 a_4x 2);
    t256 <- (t256 `^` di);
    a_4x <- (BArray800.set256 a_4x 2 t256);
    bsa <@ __rol_4u64 (t256, 62);
    t256 <- (BArray800.get256 a_4x 8);
    t256 <- (t256 `^` do_0);
    a_4x <- (BArray800.set256 a_4x 8 t256);
    bse <@ __rol_4u64 (t256, 55);
    t256 <- (BArray800.get256 a_4x 14);
    t256 <- (t256 `^` du);
    a_4x <- (BArray800.set256 a_4x 14 t256);
    bsi <@ __rol_4u64 (t256, 39);
    t256 <- (VPANDN_256 bse bsi);
    t256 <- (t256 `^` bsa);
    e_4x <- (BArray800.set256 e_4x 20 t256);
    ca <- (ca `^` t256);
    t256 <- (BArray800.get256 a_4x 15);
    t256 <- (t256 `^` da);
    a_4x <- (BArray800.set256 a_4x 15 t256);
    bso <@ __rol_4u64 (t256, 41);
    t256 <- (VPANDN_256 bsi bso);
    t256 <- (t256 `^` bse);
    e_4x <- (BArray800.set256 e_4x 21 t256);
    ce <- (ce `^` t256);
    t256 <- (BArray800.get256 a_4x 21);
    t256 <- (t256 `^` de);
    a_4x <- (BArray800.set256 a_4x 21 t256);
    bsu <@ __rol_4u64 (t256, 2);
    t256 <- (VPANDN_256 bso bsu);
    t256 <- (t256 `^` bsi);
    e_4x <- (BArray800.set256 e_4x 22 t256);
    ci <- (ci `^` t256);
    t256 <- (VPANDN_256 bsu bsa);
    t256 <- (t256 `^` bso);
    e_4x <- (BArray800.set256 e_4x 23 t256);
    co <- (co `^` t256);
    t256 <- (VPANDN_256 bsa bse);
    t256 <- (t256 `^` bsu);
    e_4x <- (BArray800.set256 e_4x 24 t256);
    cu <- (cu `^` t256);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __second_last (a_4x:BArray800.t, e_4x:BArray800.t, index:int,
                      da:W256.t, de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  BArray800.t * BArray800.t = {
    var t256:W256.t;
    var bba:W256.t;
    var bbe:W256.t;
    var bbi:W256.t;
    var bbo:W256.t;
    var bbu:W256.t;
    t256 <- (BArray800.get256 a_4x 0);
    t256 <- (t256 `^` da);
    a_4x <- (BArray800.set256 a_4x 0 t256);
    bba <- t256;
    t256 <- (BArray800.get256 a_4x 6);
    t256 <- (t256 `^` de);
    a_4x <- (BArray800.set256 a_4x 6 t256);
    bbe <@ __rol_4u64 (t256, 44);
    t256 <- (BArray800.get256 a_4x 12);
    t256 <- (t256 `^` di);
    a_4x <- (BArray800.set256 a_4x 12 t256);
    bbi <@ __rol_4u64 (t256, 43);
    t256 <- (VPANDN_256 bbe bbi);
    t256 <- (t256 `^` bba);
    t256 <- (t256 `^` (BArray768.get256 keccakF1600RoundConstants index));
    e_4x <- (BArray800.set256 e_4x 0 t256);
    t256 <- (BArray800.get256 a_4x 18);
    t256 <- (t256 `^` do_0);
    a_4x <- (BArray800.set256 a_4x 18 t256);
    bbo <@ __rol_4u64 (t256, 21);
    t256 <- (VPANDN_256 bbi bbo);
    t256 <- (t256 `^` bbe);
    e_4x <- (BArray800.set256 e_4x 1 t256);
    t256 <- (BArray800.get256 a_4x 24);
    t256 <- (t256 `^` du);
    a_4x <- (BArray800.set256 a_4x 24 t256);
    bbu <@ __rol_4u64 (t256, 14);
    t256 <- (VPANDN_256 bbo bbu);
    t256 <- (t256 `^` bbi);
    e_4x <- (BArray800.set256 e_4x 2 t256);
    t256 <- (VPANDN_256 bbu bba);
    t256 <- (t256 `^` bbo);
    e_4x <- (BArray800.set256 e_4x 3 t256);
    t256 <- (VPANDN_256 bba bbe);
    t256 <- (t256 `^` bbu);
    e_4x <- (BArray800.set256 e_4x 4 t256);
    return (a_4x, e_4x);
  }
  proc __third_last (a_4x:BArray800.t, e_4x:BArray800.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  BArray800.t * BArray800.t = {
    var t256:W256.t;
    var bga:W256.t;
    var bge:W256.t;
    var bgi:W256.t;
    var bgo:W256.t;
    var bgu:W256.t;
    t256 <- (BArray800.get256 a_4x 3);
    t256 <- (t256 `^` do_0);
    a_4x <- (BArray800.set256 a_4x 3 t256);
    bga <@ __rol_4u64 (t256, 28);
    t256 <- (BArray800.get256 a_4x 9);
    t256 <- (t256 `^` du);
    a_4x <- (BArray800.set256 a_4x 9 t256);
    bge <@ __rol_4u64 (t256, 20);
    t256 <- (BArray800.get256 a_4x 10);
    t256 <- (t256 `^` da);
    a_4x <- (BArray800.set256 a_4x 10 t256);
    bgi <@ __rol_4u64 (t256, 3);
    t256 <- (VPANDN_256 bge bgi);
    t256 <- (t256 `^` bga);
    e_4x <- (BArray800.set256 e_4x 5 t256);
    t256 <- (BArray800.get256 a_4x 16);
    t256 <- (t256 `^` de);
    a_4x <- (BArray800.set256 a_4x 16 t256);
    bgo <@ __rol_4u64 (t256, 45);
    t256 <- (VPANDN_256 bgi bgo);
    t256 <- (t256 `^` bge);
    e_4x <- (BArray800.set256 e_4x 6 t256);
    t256 <- (BArray800.get256 a_4x 22);
    t256 <- (t256 `^` di);
    a_4x <- (BArray800.set256 a_4x 22 t256);
    bgu <@ __rol_4u64 (t256, 61);
    t256 <- (VPANDN_256 bgo bgu);
    t256 <- (t256 `^` bgi);
    e_4x <- (BArray800.set256 e_4x 7 t256);
    t256 <- (VPANDN_256 bgu bga);
    t256 <- (t256 `^` bgo);
    e_4x <- (BArray800.set256 e_4x 8 t256);
    t256 <- (VPANDN_256 bga bge);
    t256 <- (t256 `^` bgu);
    e_4x <- (BArray800.set256 e_4x 9 t256);
    return (a_4x, e_4x);
  }
  proc __fourth_last (a_4x:BArray800.t, e_4x:BArray800.t, da:W256.t,
                      de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  BArray800.t * BArray800.t = {
    var t256:W256.t;
    var bka:W256.t;
    var bke:W256.t;
    var bki:W256.t;
    var bko:W256.t;
    var bku:W256.t;
    t256 <- (BArray800.get256 a_4x 1);
    t256 <- (t256 `^` de);
    a_4x <- (BArray800.set256 a_4x 1 t256);
    bka <@ __rol_4u64 (t256, 1);
    t256 <- (BArray800.get256 a_4x 7);
    t256 <- (t256 `^` di);
    a_4x <- (BArray800.set256 a_4x 7 t256);
    bke <@ __rol_4u64 (t256, 6);
    t256 <- (BArray800.get256 a_4x 13);
    t256 <- (t256 `^` do_0);
    a_4x <- (BArray800.set256 a_4x 13 t256);
    bki <@ __rol_4u64 (t256, 25);
    t256 <- (VPANDN_256 bke bki);
    t256 <- (t256 `^` bka);
    e_4x <- (BArray800.set256 e_4x 10 t256);
    t256 <- (BArray800.get256 a_4x 19);
    t256 <- (t256 `^` du);
    a_4x <- (BArray800.set256 a_4x 19 t256);
    bko <@ __rol_4u64_rho8 (t256);
    t256 <- (VPANDN_256 bki bko);
    t256 <- (t256 `^` bke);
    e_4x <- (BArray800.set256 e_4x 11 t256);
    t256 <- (BArray800.get256 a_4x 20);
    t256 <- (t256 `^` da);
    a_4x <- (BArray800.set256 a_4x 20 t256);
    bku <@ __rol_4u64 (t256, 18);
    t256 <- (VPANDN_256 bko bku);
    t256 <- (t256 `^` bki);
    e_4x <- (BArray800.set256 e_4x 12 t256);
    t256 <- (VPANDN_256 bku bka);
    t256 <- (t256 `^` bko);
    e_4x <- (BArray800.set256 e_4x 13 t256);
    t256 <- (VPANDN_256 bka bke);
    t256 <- (t256 `^` bku);
    e_4x <- (BArray800.set256 e_4x 14 t256);
    return (a_4x, e_4x);
  }
  proc __fifth_last (a_4x:BArray800.t, e_4x:BArray800.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  BArray800.t * BArray800.t = {
    var t256:W256.t;
    var bma:W256.t;
    var bme:W256.t;
    var bmi:W256.t;
    var bmo:W256.t;
    var bmu:W256.t;
    t256 <- (BArray800.get256 a_4x 4);
    t256 <- (t256 `^` du);
    a_4x <- (BArray800.set256 a_4x 4 t256);
    bma <@ __rol_4u64 (t256, 27);
    t256 <- (BArray800.get256 a_4x 5);
    t256 <- (t256 `^` da);
    a_4x <- (BArray800.set256 a_4x 5 t256);
    bme <@ __rol_4u64 (t256, 36);
    t256 <- (BArray800.get256 a_4x 11);
    t256 <- (t256 `^` de);
    a_4x <- (BArray800.set256 a_4x 11 t256);
    bmi <@ __rol_4u64 (t256, 10);
    t256 <- (VPANDN_256 bme bmi);
    t256 <- (t256 `^` bma);
    e_4x <- (BArray800.set256 e_4x 15 t256);
    t256 <- (BArray800.get256 a_4x 17);
    t256 <- (t256 `^` di);
    a_4x <- (BArray800.set256 a_4x 17 t256);
    bmo <@ __rol_4u64 (t256, 15);
    t256 <- (VPANDN_256 bmi bmo);
    t256 <- (t256 `^` bme);
    e_4x <- (BArray800.set256 e_4x 16 t256);
    t256 <- (BArray800.get256 a_4x 23);
    t256 <- (t256 `^` do_0);
    a_4x <- (BArray800.set256 a_4x 23 t256);
    bmu <@ __rol_4u64_rho56 (t256);
    t256 <- (VPANDN_256 bmo bmu);
    t256 <- (t256 `^` bmi);
    e_4x <- (BArray800.set256 e_4x 17 t256);
    t256 <- (VPANDN_256 bmu bma);
    t256 <- (t256 `^` bmo);
    e_4x <- (BArray800.set256 e_4x 18 t256);
    t256 <- (VPANDN_256 bma bme);
    t256 <- (t256 `^` bmu);
    e_4x <- (BArray800.set256 e_4x 19 t256);
    return (a_4x, e_4x);
  }
  proc __sixth_last (a_4x:BArray800.t, e_4x:BArray800.t, da:W256.t,
                     de:W256.t, di:W256.t, do_0:W256.t, du:W256.t) : 
  BArray800.t * BArray800.t = {
    var t256:W256.t;
    var bsa:W256.t;
    var bse:W256.t;
    var bsi:W256.t;
    var bso:W256.t;
    var bsu:W256.t;
    t256 <- (BArray800.get256 a_4x 2);
    t256 <- (t256 `^` di);
    a_4x <- (BArray800.set256 a_4x 2 t256);
    bsa <@ __rol_4u64 (t256, 62);
    t256 <- (BArray800.get256 a_4x 8);
    t256 <- (t256 `^` do_0);
    a_4x <- (BArray800.set256 a_4x 8 t256);
    bse <@ __rol_4u64 (t256, 55);
    t256 <- (BArray800.get256 a_4x 14);
    t256 <- (t256 `^` du);
    a_4x <- (BArray800.set256 a_4x 14 t256);
    bsi <@ __rol_4u64 (t256, 39);
    t256 <- (VPANDN_256 bse bsi);
    t256 <- (t256 `^` bsa);
    e_4x <- (BArray800.set256 e_4x 20 t256);
    t256 <- (BArray800.get256 a_4x 15);
    t256 <- (t256 `^` da);
    a_4x <- (BArray800.set256 a_4x 15 t256);
    bso <@ __rol_4u64 (t256, 41);
    t256 <- (VPANDN_256 bsi bso);
    t256 <- (t256 `^` bse);
    e_4x <- (BArray800.set256 e_4x 21 t256);
    t256 <- (BArray800.get256 a_4x 21);
    t256 <- (t256 `^` de);
    a_4x <- (BArray800.set256 a_4x 21 t256);
    bsu <@ __rol_4u64 (t256, 2);
    t256 <- (VPANDN_256 bso bsu);
    t256 <- (t256 `^` bsi);
    e_4x <- (BArray800.set256 e_4x 22 t256);
    t256 <- (VPANDN_256 bsu bsa);
    t256 <- (t256 `^` bso);
    e_4x <- (BArray800.set256 e_4x 23 t256);
    t256 <- (VPANDN_256 bsa bse);
    t256 <- (t256 `^` bsu);
    e_4x <- (BArray800.set256 e_4x 24 t256);
    return (a_4x, e_4x);
  }
  proc __theta_rho_pi_chi_iota_prepare_theta_even (a_4x:BArray800.t,
                                                   e_4x:BArray800.t,
                                                   index:int, ca:W256.t,
                                                   ce:W256.t, ci:W256.t,
                                                   co:W256.t, cu:W256.t) : 
  BArray800.t * BArray800.t * W256.t * W256.t * W256.t * W256.t * W256.t = {
    var da:W256.t;
    var de:W256.t;
    var di:W256.t;
    var do_0:W256.t;
    var du:W256.t;
    (da, de, di, do_0, du) <@ __first (ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __second_even (a_4x, e_4x, index, 
    ca, ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __third_even (a_4x, e_4x, ca, 
    ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __fourth_even (a_4x, e_4x, ca, 
    ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __fifth_even (a_4x, e_4x, ca, 
    ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __sixth_even (a_4x, e_4x, ca, 
    ce, ci, co, cu, da, de, di, do_0, du);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __theta_rho_pi_chi_iota_prepare_theta_odd (a_4x:BArray800.t,
                                                  e_4x:BArray800.t,
                                                  index:int, ca:W256.t,
                                                  ce:W256.t, ci:W256.t,
                                                  co:W256.t, cu:W256.t) : 
  BArray800.t * BArray800.t * W256.t * W256.t * W256.t * W256.t * W256.t = {
    var da:W256.t;
    var de:W256.t;
    var di:W256.t;
    var do_0:W256.t;
    var du:W256.t;
    (da, de, di, do_0, du) <@ __first (ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __second_odd (a_4x, e_4x, index, 
    ca, ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __third_odd (a_4x, e_4x, ca, 
    ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __fourth_odd (a_4x, e_4x, ca, 
    ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __fifth_odd (a_4x, e_4x, ca, 
    ce, ci, co, cu, da, de, di, do_0, du);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __sixth_odd (a_4x, e_4x, ca, 
    ce, ci, co, cu, da, de, di, do_0, du);
    return (a_4x, e_4x, ca, ce, ci, co, cu);
  }
  proc __theta_rho_pi_chi_iota (a_4x:BArray800.t, e_4x:BArray800.t,
                                index:int, ca:W256.t, ce:W256.t, ci:W256.t,
                                co:W256.t, cu:W256.t) : BArray800.t *
                                                        BArray800.t = {
    var da:W256.t;
    var de:W256.t;
    var di:W256.t;
    var do_0:W256.t;
    var du:W256.t;
    (da, de, di, do_0, du) <@ __first (ca, ce, ci, co, cu);
    (a_4x, e_4x) <@ __second_last (a_4x, e_4x, index, da, de, di, do_0, du);
    (a_4x, e_4x) <@ __third_last (a_4x, e_4x, da, de, di, do_0, du);
    (a_4x, e_4x) <@ __fourth_last (a_4x, e_4x, da, de, di, do_0, du);
    (a_4x, e_4x) <@ __fifth_last (a_4x, e_4x, da, de, di, do_0, du);
    (a_4x, e_4x) <@ __sixth_last (a_4x, e_4x, da, de, di, do_0, du);
    return (a_4x, e_4x);
  }
  proc _KeccakF1600_StatePermute4x (a_4x:BArray800.t, ms:W64.t) : BArray800.t *
                                                                  W64.t = {
    var ca:W256.t;
    var ce:W256.t;
    var ci:W256.t;
    var co:W256.t;
    var cu:W256.t;
    var e_4x:BArray800.t;
    var  _0:BArray800.t;
     _0 <- witness;
    e_4x <- witness;
    (ca, ce, ci, co, cu) <@ __prepare_theta (a_4x);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, 0, ca, ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, 1, ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, 2, ca, ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, 3, ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, 4, ca, ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, 5, ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, 6, ca, ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, 7, ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, 8, ca, ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, 9, ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, 10, ca, ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, 11, ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, 12, ca, ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, 13, ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, 14, ca, ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, 15, ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, 16, ca, ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, 17, ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, 18, ca, ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, 19, ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, 20, ca, ce, ci, co, cu);
    (e_4x, a_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_odd (
    e_4x, a_4x, 21, ca, ce, ci, co, cu);
    (a_4x, e_4x, ca, ce, ci, co, cu) <@ __theta_rho_pi_chi_iota_prepare_theta_even (
    a_4x, e_4x, 22, ca, ce, ci, co, cu);
    ( _0, a_4x) <@ __theta_rho_pi_chi_iota (e_4x, a_4x, 23, ca, ce, ci, 
    co, cu);
    return (a_4x, ms);
  }
  proc shake256_add_rate_bit (st:BArray224.t) : BArray224.t = {
    var t64:W64.t;
    var t128:W128.t;
    var t256:W256.t;
    t64 <- (W64.of_int 1);
    t64 <- (t64 `<<` (W8.of_int (((8 * 136) - 1) %% 64)));
    t128 <- (zeroextu128 t64);
    t256 <- (set0_256);
    t256 <- (VINSERTI128 t256 t128 (W8.of_int 0));
    st <- (BArray224.set256 st 3 ((BArray224.get256 st 3) `^` t256));
    return st;
  }
  proc shake256_absorb_block (state:BArray224.t, block:BArray136.t) : 
  BArray224.t = {
    var t64:W64.t;
    var t128_0:W128.t;
    var r0:W256.t;
    var r1:W256.t;
    var t128_1:W128.t;
    var r3:W256.t;
    var r4:W256.t;
    var r5:W256.t;
    var r2:W256.t;
    var r6:W256.t;
    t64 <- (BArray136.get64d block 0);
    t128_0 <- (zeroextu128 t64);
    r0 <- (VPBROADCAST_4u64 (truncateu64 t128_0));
    state <- (BArray224.set256 state 0 ((BArray224.get256 state 0) `^` r0));
    r1 <- (BArray136.get256d block 8);
    state <- (BArray224.set256 state 1 ((BArray224.get256 state 1) `^` r1));
    t64 <- (BArray136.get64d block 40);
    t128_1 <- (zeroextu128 t64);
    r3 <- (BArray136.get256d block 48);
    t64 <- (BArray136.get64d block 80);
    t128_0 <- (zeroextu128 t64);
    r4 <- (BArray136.get256d block 88);
    t64 <- (BArray136.get64d block 120);
    t128_1 <- (VPINSR_2u64 t128_1 t64 (W8.of_int 1));
    t64 <- (BArray136.get64d block 128);
    r5 <- (zeroextu256 (VMOV_64 t64));
    t64 <- (W64.of_int 0);
    t128_0 <- (VPINSR_2u64 t128_0 t64 (W8.of_int 1));
    r2 <-
    (W256.of_int
    (((W128.to_uint t128_0) %% (2 ^ 128)) +
    ((2 ^ 128) * (W128.to_uint t128_1))));
    state <- (BArray224.set256 state 2 ((BArray224.get256 state 2) `^` r2));
    r6 <- (set0_256);
    state <@ __addstate_r3456_avx2 (state, r3, r4, r5, r6);
    state <@ _keccakf1600_avx2 (state);
    return state;
  }
  proc shake256_squeeze_block (block:BArray136.t, state:BArray224.t) : 
  BArray136.t = {
    var t128_0:W128.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
    var t128_1:W128.t;
    var t256_4:W256.t;
    t128_0 <- (truncateu128 (BArray224.get256 state 0));
    block <- (BArray136.set64d block 0 (truncateu64 t128_0));
    block <- (BArray136.set256d block (1 * 8) (BArray224.get256 state 1));
    t256_0 <-
    (VPBLEND_8u32 (BArray224.get256 state 3) (BArray224.get256 state 4)
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_1 <-
    (VPBLEND_8u32 (BArray224.get256 state 4) (BArray224.get256 state 3)
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_2 <-
    (VPBLEND_8u32 (BArray224.get256 state 5) (BArray224.get256 state 6)
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_3 <-
    (VPBLEND_8u32 (BArray224.get256 state 6) (BArray224.get256 state 5)
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t128_1 <- (VEXTRACTI128 (BArray224.get256 state 2) (W8.of_int 1));
    block <- (BArray136.set64d block 40 (truncateu64 t128_1));
    t256_4 <-
    (VPBLEND_8u32 t256_0 t256_3
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    block <- (BArray136.set256d block 48 t256_4);
    t128_0 <- (truncateu128 (BArray224.get256 state 2));
    block <- (BArray136.set64d block 80 (truncateu64 t128_0));
    t256_4 <-
    (VPBLEND_8u32 t256_3 t256_1
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    block <- (BArray136.set256d block 88 t256_4);
    block <- (BArray136.set64d block 120 (VPEXTR_64 t128_1 (W8.of_int 1)));
    t256_4 <-
    (VPBLEND_8u32 t256_2 t256_0
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t128_0 <- (truncateu128 t256_4);
    block <- (BArray136.set64d block 128 (truncateu64 t128_0));
    return block;
  }
  proc squeeze_64_bytes (array:BArray64.t, state:BArray224.t) : BArray64.t = {
    var t128:W128.t;
    var t256:W256.t;
    t128 <- (truncateu128 (BArray224.get256 state 0));
    array <- (BArray64.set64d array 0 (truncateu64 t128));
    array <- (BArray64.set256d array 8 (BArray224.get256 state 1));
    t256 <-
    (VPBLEND_8u32 (BArray224.get256 state 6) (BArray224.get256 state 3)
    (W8.of_int 12));
    t128 <- (VEXTRACTI128 (BArray224.get256 state 2) (W8.of_int 1));
    array <- (BArray64.set64d array 40 (truncateu64 t128));
    t128 <- (truncateu128 t256);
    array <- (BArray64.set128d array 48 t128);
    return array;
  }
  proc __shake256_consider_permute (state:BArray200.t, offset:W64.t) : 
  BArray200.t * W64.t = {
    
    if (((W64.of_int 136) \ule offset)) {
      state <@ _keccakf1600_ref1 (state);
      offset <- (W64.of_int 0);
    } else {
      
    }
    return (state, offset);
  }
  proc __derive_message_representative (verification_key_hash:BArray64.t,
                                        context_message_pointers:BArray16.t,
                                        context_message_sizes:BArray16.t) : 
  BArray64.t = {
    var message_representative:BArray64.t;
    var state:BArray200.t;
    var copied_32_bytes:W256.t;
    var context_offset:W64.t;
    var context:W64.t;
    var context_size:W64.t;
    var state_offset:W64.t;
    var byte:W8.t;
    var message_offset:W64.t;
    var message:W64.t;
    var message_size:W64.t;
    var  _0:W64.t;
    message_representative <- witness;
    state <- witness;
    (* Erased call to spill *)
    state <@ __keccak_init_ref1 (state);
    copied_32_bytes <- (BArray64.get256d verification_key_hash 0);
    state <- (BArray200.set256d state 0 copied_32_bytes);
    copied_32_bytes <- (BArray64.get256d verification_key_hash 32);
    state <- (BArray200.set256d state 32 copied_32_bytes);
    context_offset <- (W64.of_int 0);
    (* Erased call to unspill *)
    context <- (BArray16.get64 context_message_pointers 0);
    (* Erased call to unspill *)
    context_size <- (BArray16.get64 context_message_sizes 0);
    state <- (BArray200.set8d state 64 (W8.of_int 0));
    state <- (BArray200.set8d state 65 (truncateu8 context_size));
    state_offset <- (W64.of_int 66);
    while ((context_offset \ult context_size)) {
      if (((W64.of_int 136) \ule state_offset)) {
        (* Erased call to spill *)
        state <@ _keccakf1600_ref1 (state);
        (* Erased call to unspill *)
        state_offset <- (W64.of_int 0);
      } else {
        
      }
      byte <- (loadW8 Glob.mem (W64.to_uint (context + context_offset)));
      context_offset <- (context_offset + (W64.of_int 1));
      state <-
      (BArray200.set8 state (W64.to_uint state_offset)
      ((BArray200.get8 state (W64.to_uint state_offset)) `^` byte));
      state_offset <- (state_offset + (W64.of_int 1));
    }
    message_offset <- (W64.of_int 0);
    (* Erased call to unspill *)
    message <- (BArray16.get64 context_message_pointers 1);
    (* Erased call to unspill *)
    message_size <- (BArray16.get64 context_message_sizes 1);
    while ((message_offset \ult message_size)) {
      if (((W64.of_int 136) \ule state_offset)) {
        (* Erased call to spill *)
        state <@ _keccakf1600_ref1 (state);
        (* Erased call to unspill *)
        state_offset <- (W64.of_int 0);
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
    (state,  _0) <@ __shake256_consider_permute (state, state_offset);
    state <-
    (BArray200.set8 state (136 - 1)
    ((BArray200.get8 state (136 - 1)) `^` (W8.of_int 128)));
    state <@ _keccakf1600_ref1 (state);
    copied_32_bytes <- (BArray200.get256d state 0);
    message_representative <-
    (BArray64.set256d message_representative 0 copied_32_bytes);
    copied_32_bytes <- (BArray200.get256d state 32);
    message_representative <-
    (BArray64.set256d message_representative 32 copied_32_bytes);
    return message_representative;
  }
  proc shake128_squeezeblock4x (state:BArray800.t, h0:BArray168.t,
                                h1:BArray168.t, h2:BArray168.t,
                                h3:BArray168.t) : BArray800.t * BArray168.t *
                                                  BArray168.t * BArray168.t *
                                                  BArray168.t = {
    var inc:int;
    var msf:W64.t;
    var i:int;
    var t256:W256.t;
    var t128:W128.t;
    msf <- (init_msf);
    (state, msf) <@ _KeccakF1600_StatePermute4x (state, msf);
    inc <- (168 %/ 8);
    i <- 0;
    while ((i < inc)) {
      t256 <- (BArray800.get256 state i);
      t128 <- (truncateu128 t256);
      h0 <- (BArray168.set64 h0 i (VMOVLPD t128));
      h1 <- (BArray168.set64 h1 i (VMOVHPD t128));
      t128 <- (VEXTRACTI128 t256 (W8.of_int 1));
      h2 <- (BArray168.set64 h2 i (VMOVLPD t128));
      h3 <- (BArray168.set64 h3 i (VMOVHPD t128));
      i <- (i + 1);
    }
    return (state, h0, h1, h2, h3);
  }
  proc shake256_squeezeblock4x (state:BArray800.t, h0:BArray136.t,
                                h1:BArray136.t, h2:BArray136.t,
                                h3:BArray136.t) : BArray800.t * BArray136.t *
                                                  BArray136.t * BArray136.t *
                                                  BArray136.t = {
    var inc:int;
    var msf:W64.t;
    var i:int;
    var t256:W256.t;
    var output_bytes:BArray32.t;
    output_bytes <- witness;
    msf <- (init_msf);
    (state, msf) <@ _KeccakF1600_StatePermute4x (state, msf);
    inc <- (136 %/ 8);
    i <- 0;
    while ((i < inc)) {
      t256 <- (BArray800.get256 state i);
      output_bytes <- (BArray32.set256d output_bytes 0 t256);
      h0 <- (BArray136.set64 h0 i (BArray32.get64 output_bytes 0));
      h1 <- (BArray136.set64 h1 i (BArray32.get64 output_bytes 1));
      h2 <- (BArray136.set64 h2 i (BArray32.get64 output_bytes 2));
      h3 <- (BArray136.set64 h3 i (BArray32.get64 output_bytes 3));
      i <- (i + 1);
    }
    return (state, h0, h1, h2, h3);
  }
  proc matrix_A____bytestream_to_potential_coefficients (bytestream:W256.t) : 
  W256.t = {
    var coefficients:W256.t;
    var constants:W256.t;
    constants <- (BArray96.get256 matrix_A__DECODING_TABLE 0);
    coefficients <- (VPERMD constants bytestream);
    constants <- (BArray96.get256 matrix_A__DECODING_TABLE 1);
    coefficients <- (VPSHUFB_256 coefficients constants);
    constants <- (BArray96.get256 matrix_A__DECODING_TABLE 2);
    coefficients <- (VPAND_256 coefficients constants);
    return coefficients;
  }
  proc matrix_A__rejection_sample_multiple_blocks (polynomial:BArray1024.t,
                                                   randombytes:BArray848.t) : 
  BArray1024.t * W64.t = {
    var filled:W64.t;
    var shuffle_table_pointer:BArray256.t;
    var bytes_filled:W64.t;
    var input_offset:W64.t;
    var modulus:W256.t;
    var stop_sampling:W64.t;
    var potential_coefficients:W256.t;
    var compare_with_field_modulus:W256.t;
    var good:W64.t;
    var lower_coefficients:W128.t;
    var good_lower:W64.t;
    var shuffle_table_idx:W64.t;
    var shuffles:W128.t;
    var upper_coefficients:W128.t;
    var good_upper:W64.t;
    var byte0:W32.t;
    var byte1:W32.t;
    var byte2:W32.t;
    var coeff:W32.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    var  _5:bool;
    var  _6:bool;
    var  _7:bool;
    var  _8:bool;
    var  _9:bool;
    shuffle_table_pointer <- witness;
    shuffle_table_pointer <- matrix_A__SHUFFLE_TABLE;
    bytes_filled <- (W64.of_int 0);
    input_offset <- (W64.of_int 0);
    modulus <- mODULUS_VECTOR;
    stop_sampling <- (W64.of_int 0);
    while ((stop_sampling <> (W64.of_int 1))) {
      potential_coefficients <-
      (BArray848.get256d randombytes (W64.to_uint input_offset));
      potential_coefficients <@ matrix_A____bytestream_to_potential_coefficients (
      potential_coefficients);
      input_offset <- (input_offset + (W64.of_int 24));
      compare_with_field_modulus <-
      (VPCMPGT_8u32 modulus potential_coefficients);
      good <- (zeroextu64 (MOVEMASK_8u32 compare_with_field_modulus));
      lower_coefficients <-
      (VEXTRACTI128 potential_coefficients (W8.of_int 0));
      good_lower <- good;
      good_lower <- (good_lower `&` (W64.of_int 15));
      shuffle_table_idx <- good_lower;
      shuffle_table_idx <- (shuffle_table_idx `<<` (W8.of_int 4));
      shuffles <-
      (BArray256.get128d shuffle_table_pointer
      (W64.to_uint shuffle_table_idx));
      lower_coefficients <- (VPSHUFB_128 lower_coefficients shuffles);
      polynomial <-
      (BArray1024.set128d polynomial (W64.to_uint bytes_filled)
      lower_coefficients);
      ( _0,  _1,  _2,  _3,  _4, good_lower) <- (POPCNT_64 good_lower);
      good_lower <- (good_lower `<<` (W8.of_int 2));
      bytes_filled <- (bytes_filled + good_lower);
      upper_coefficients <-
      (VEXTRACTI128 potential_coefficients (W8.of_int 1));
      good_upper <- good;
      good_upper <- (good_upper `>>` (W8.of_int 4));
      shuffle_table_idx <- good_upper;
      shuffle_table_idx <- (shuffle_table_idx `<<` (W8.of_int 4));
      shuffles <-
      (BArray256.get128d shuffle_table_pointer
      (W64.to_uint shuffle_table_idx));
      upper_coefficients <- (VPSHUFB_128 upper_coefficients shuffles);
      polynomial <-
      (BArray1024.set128d polynomial (W64.to_uint bytes_filled)
      upper_coefficients);
      ( _5,  _6,  _7,  _8,  _9, good_upper) <- (POPCNT_64 good_upper);
      good_upper <- (good_upper `<<` (W8.of_int 2));
      bytes_filled <- (bytes_filled + good_upper);
      stop_sampling <- (W64.of_int 0);
      if (((W64.of_int (((256 * 32) %/ 8) - 32)) \ule bytes_filled)) {
        stop_sampling <- (W64.of_int 1);
      } else {
        if (((W64.of_int (5 * 168)) \ule input_offset)) {
          stop_sampling <- (W64.of_int 1);
        } else {
          
        }
      }
    }
    filled <- bytes_filled;
    filled <- (filled `>>` (W8.of_int 2));
    stop_sampling <- (W64.of_int 1);
    if ((filled \ult (W64.of_int 256))) {
      if ((input_offset \ult (W64.of_int ((5 * 168) - 3)))) {
        stop_sampling <- (W64.of_int 0);
      } else {
        
      }
    } else {
      
    }
    while ((stop_sampling <> (W64.of_int 1))) {
      byte0 <-
      (zeroextu32 (BArray848.get8 randombytes (W64.to_uint input_offset)));
      input_offset <- (input_offset + (W64.of_int 1));
      byte1 <-
      (zeroextu32 (BArray848.get8 randombytes (W64.to_uint input_offset)));
      input_offset <- (input_offset + (W64.of_int 1));
      byte2 <-
      (zeroextu32 (BArray848.get8 randombytes (W64.to_uint input_offset)));
      input_offset <- (input_offset + (W64.of_int 1));
      coeff <- byte0;
      byte1 <- (byte1 `<<` (W8.of_int 8));
      coeff <- (coeff `|` byte1);
      byte2 <- (byte2 `<<` (W8.of_int 16));
      coeff <- (coeff `|` byte2);
      coeff <- (coeff `&` (W32.of_int 8388607));
      if ((coeff \ult (W32.of_int 8380417))) {
        polynomial <-
        (BArray1024.set32 polynomial (W64.to_uint filled) coeff);
        filled <- (filled + (W64.of_int 1));
      } else {
        
      }
      stop_sampling <- (W64.of_int 0);
      if (((W64.of_int 256) \ule filled)) {
        stop_sampling <- (W64.of_int 1);
      } else {
        if (((W64.of_int ((5 * 168) - 3)) \ule input_offset)) {
          stop_sampling <- (W64.of_int 1);
        } else {
          
        }
      }
    }
    return (polynomial, filled);
  }
  proc matrix_A__rejection_sample_one_block (polynomial:BArray1024.t,
                                             filled:W64.t, block:BArray168.t) : 
  BArray1024.t * W64.t = {
    var block_offset:W64.t;
    var stop_sampling:W8.t;
    var byte0:W32.t;
    var byte1:W32.t;
    var byte2:W32.t;
    var coeff:W32.t;
    block_offset <- (W64.of_int 0);
    stop_sampling <- (W8.of_int 0);
    if (((W64.of_int 256) \ule filled)) {
      stop_sampling <- (W8.of_int 1);
    } else {
      
    }
    while ((stop_sampling <> (W8.of_int 1))) {
      byte0 <-
      (zeroextu32 (BArray168.get8 block (W64.to_uint block_offset)));
      block_offset <- (block_offset + (W64.of_int 1));
      byte1 <-
      (zeroextu32 (BArray168.get8 block (W64.to_uint block_offset)));
      block_offset <- (block_offset + (W64.of_int 1));
      byte2 <-
      (zeroextu32 (BArray168.get8 block (W64.to_uint block_offset)));
      block_offset <- (block_offset + (W64.of_int 1));
      coeff <- byte0;
      byte1 <- (byte1 `<<` (W8.of_int 8));
      coeff <- (coeff `|` byte1);
      byte2 <- (byte2 `<<` (W8.of_int 16));
      coeff <- (coeff `|` byte2);
      coeff <- (coeff `&` (W32.of_int 8388607));
      if ((coeff \ult (W32.of_int 8380417))) {
        polynomial <-
        (BArray1024.set32 polynomial (W64.to_uint filled) coeff);
        filled <- (filled + (W64.of_int 1));
      } else {
        
      }
      stop_sampling <- (W8.of_int 0);
      if (((W64.of_int 256) \ule filled)) {
        stop_sampling <- (W8.of_int 1);
      } else {
        if (((W64.of_int 168) \ule block_offset)) {
          stop_sampling <- (W8.of_int 1);
        } else {
          
        }
      }
    }
    return (polynomial, filled);
  }
  proc matrix_A__shake128_absorb_34_4x (state:BArray800.t, rho:BArray32.t,
                                        domain_separators:BArray8.t) : 
  BArray800.t = {
    var t0:W256.t;
    var i:int;
    var t64:W64.t;
    var t16:W16.t;
    var t1:W256.t;
    t0 <- (set0_256);
    i <- 0;
    while ((i < 25)) {
      state <- (BArray800.set256 state i t0);
      i <- (i + 1);
    }
    i <- 0;
    while ((i < 4)) {
      t64 <- (BArray32.get64 rho i);
      state <-
      (BArray800.set64 state (4 * i)
      ((BArray800.get64 state (4 * i)) `^` t64));
      t64 <- (BArray32.get64 rho i);
      state <-
      (BArray800.set64 state ((4 * i) + 1)
      ((BArray800.get64 state ((4 * i) + 1)) `^` t64));
      t64 <- (BArray32.get64 rho i);
      state <-
      (BArray800.set64 state ((4 * i) + 2)
      ((BArray800.get64 state ((4 * i) + 2)) `^` t64));
      t64 <- (BArray32.get64 rho i);
      state <-
      (BArray800.set64 state ((4 * i) + 3)
      ((BArray800.get64 state ((4 * i) + 3)) `^` t64));
      i <- (i + 1);
    }
    t16 <- (BArray8.get16 domain_separators 0);
    state <- (BArray800.set16 state 64 ((BArray800.get16 state 64) `^` t16));
    state <-
    (BArray800.set8 state 130 ((BArray800.get8 state 130) `^` (W8.of_int 31))
    );
    t16 <- (BArray8.get16 domain_separators 1);
    state <- (BArray800.set16 state 68 ((BArray800.get16 state 68) `^` t16));
    state <-
    (BArray800.set8 state 138 ((BArray800.get8 state 138) `^` (W8.of_int 31))
    );
    t16 <- (BArray8.get16 domain_separators 2);
    state <- (BArray800.set16 state 72 ((BArray800.get16 state 72) `^` t16));
    state <-
    (BArray800.set8 state 146 ((BArray800.get8 state 146) `^` (W8.of_int 31))
    );
    t16 <- (BArray8.get16 domain_separators 3);
    state <- (BArray800.set16 state 76 ((BArray800.get16 state 76) `^` t16));
    state <-
    (BArray800.set8 state 154 ((BArray800.get8 state 154) `^` (W8.of_int 31))
    );
    t0 <- (BArray32.get256 shake_sep 0);
    t1 <- (BArray800.get256 state ((168 %/ 8) - 1));
    t0 <- (t0 `^` t1);
    state <- (BArray800.set256 state ((168 %/ 8) - 1) t0);
    return state;
  }
  proc matrix_A____shake128_squeeze_multiple_blocks_4x (state:BArray800.t,
                                                        b0:BArray848.t,
                                                        b1:BArray848.t,
                                                        b2:BArray848.t,
                                                        b3:BArray848.t) : 
  BArray800.t * BArray848.t * BArray848.t * BArray848.t * BArray848.t = {
    var aux_0:BArray168.t;
    var aux_1:BArray168.t;
    var aux_2:BArray168.t;
    var aux_3:BArray168.t;
    var aux:BArray800.t;
    var i:int;
    i <- 0;
    while ((i < 5)) {
      (aux, aux_0, aux_1, aux_2, aux_3) <@ shake128_squeezeblock4x (state,
      (SBArray848_168.get_sub8 b0 (i * 168)),
      (SBArray848_168.get_sub8 b1 (i * 168)),
      (SBArray848_168.get_sub8 b2 (i * 168)),
      (SBArray848_168.get_sub8 b3 (i * 168)));
      state <- aux;
      b0 <- (SBArray848_168.set_sub8 b0 (i * 168) aux_0);
      b1 <- (SBArray848_168.set_sub8 b1 (i * 168) aux_1);
      b2 <- (SBArray848_168.set_sub8 b2 (i * 168) aux_2);
      b3 <- (SBArray848_168.set_sub8 b3 (i * 168) aux_3);
      i <- (i + 1);
    }
    return (state, b0, b1, b2, b3);
  }
  proc matrix_A____sample_4_polynomials (rho:BArray32.t,
                                         domain_separators:BArray8.t) : 
  BArray1024.t * BArray1024.t * BArray1024.t * BArray1024.t = {
    var aux_0:BArray168.t;
    var aux_1:BArray168.t;
    var aux_2:BArray168.t;
    var aux_3:BArray168.t;
    var aux:BArray800.t;
    var polynomial0:BArray1024.t;
    var polynomial1:BArray1024.t;
    var polynomial2:BArray1024.t;
    var polynomial3:BArray1024.t;
    var xof_state:BArray800.t;
    var buf0:BArray848.t;
    var buf1:BArray848.t;
    var buf2:BArray848.t;
    var buf3:BArray848.t;
    var filled:W64.t;
    var filled0:W64.t;
    var filled1:W64.t;
    var filled2:W64.t;
    var filled3:W64.t;
    var stop_sampling:W32.t;
    buf0 <- witness;
    buf1 <- witness;
    buf2 <- witness;
    buf3 <- witness;
    polynomial0 <- witness;
    polynomial1 <- witness;
    polynomial2 <- witness;
    polynomial3 <- witness;
    xof_state <- witness;
    xof_state <@ matrix_A__shake128_absorb_34_4x (xof_state, rho,
    domain_separators);
    (xof_state, buf0, buf1, buf2, buf3) <@ matrix_A____shake128_squeeze_multiple_blocks_4x (
    xof_state, buf0, buf1, buf2, buf3);
    (polynomial0, filled) <@ matrix_A__rejection_sample_multiple_blocks (
    polynomial0, buf0);
    filled0 <- filled;
    (polynomial1, filled) <@ matrix_A__rejection_sample_multiple_blocks (
    polynomial1, buf1);
    filled1 <- filled;
    (polynomial2, filled) <@ matrix_A__rejection_sample_multiple_blocks (
    polynomial2, buf2);
    filled2 <- filled;
    (polynomial3, filled) <@ matrix_A__rejection_sample_multiple_blocks (
    polynomial3, buf3);
    filled3 <- filled;
    stop_sampling <- (W32.of_int 1);
    if ((filled0 \ult (W64.of_int 256))) {
      stop_sampling <- (W32.of_int 0);
    } else {
      if ((filled1 \ult (W64.of_int 256))) {
        stop_sampling <- (W32.of_int 0);
      } else {
        if ((filled2 \ult (W64.of_int 256))) {
          stop_sampling <- (W32.of_int 0);
        } else {
          if ((filled3 \ult (W64.of_int 256))) {
            stop_sampling <- (W32.of_int 0);
          } else {
            
          }
        }
      }
    }
    while ((stop_sampling <> (W32.of_int 1))) {
      (aux, aux_0, aux_1, aux_2, aux_3) <@ shake128_squeezeblock4x (xof_state,
      (SBArray848_168.get_sub8 buf0 0), (SBArray848_168.get_sub8 buf1 0),
      (SBArray848_168.get_sub8 buf2 0), (SBArray848_168.get_sub8 buf3 0));
      xof_state <- aux;
      buf0 <- (SBArray848_168.set_sub8 buf0 0 aux_0);
      buf1 <- (SBArray848_168.set_sub8 buf1 0 aux_1);
      buf2 <- (SBArray848_168.set_sub8 buf2 0 aux_2);
      buf3 <- (SBArray848_168.set_sub8 buf3 0 aux_3);
      filled <- filled0;
      (polynomial0, filled) <@ matrix_A__rejection_sample_one_block (
      polynomial0, filled, (SBArray848_168.get_sub8 buf0 0));
      filled0 <- filled;
      filled <- filled1;
      (polynomial1, filled) <@ matrix_A__rejection_sample_one_block (
      polynomial1, filled, (SBArray848_168.get_sub8 buf1 0));
      filled1 <- filled;
      filled <- filled2;
      (polynomial2, filled) <@ matrix_A__rejection_sample_one_block (
      polynomial2, filled, (SBArray848_168.get_sub8 buf2 0));
      filled2 <- filled;
      filled <- filled3;
      (polynomial3, filled) <@ matrix_A__rejection_sample_one_block (
      polynomial3, filled, (SBArray848_168.get_sub8 buf3 0));
      filled3 <- filled;
      stop_sampling <- (W32.of_int 1);
      if ((filled0 \ult (W64.of_int 256))) {
        stop_sampling <- (W32.of_int 0);
      } else {
        if ((filled1 \ult (W64.of_int 256))) {
          stop_sampling <- (W32.of_int 0);
        } else {
          if ((filled2 \ult (W64.of_int 256))) {
            stop_sampling <- (W32.of_int 0);
          } else {
            if ((filled3 \ult (W64.of_int 256))) {
              stop_sampling <- (W32.of_int 0);
            } else {
              
            }
          }
        }
      }
    }
    return (polynomial0, polynomial1, polynomial2, polynomial3);
  }
  proc sample____initialize_xof (commitment_hash:BArray48.t) : BArray224.t = {
    var state:BArray224.t;
    var zero_256:W256.t;
    var i:W64.t;
    var initial_block:BArray136.t;
    var copied_16_bytes:W128.t;
    initial_block <- witness;
    state <- witness;
    zero_256 <- (set0_256);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 128))) {
      initial_block <-
      (BArray136.set256d initial_block (W64.to_uint i) zero_256);
      i <- (i + (W64.of_int 32));
    }
    initial_block <- (BArray136.set64d initial_block 128 (W64.of_int 0));
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 48))) {
      copied_16_bytes <- (BArray48.get128d commitment_hash (W64.to_uint i));
      initial_block <-
      (BArray136.set128d initial_block (W64.to_uint i) copied_16_bytes);
      i <- (i + (W64.of_int 16));
    }
    initial_block <- (BArray136.set8d initial_block 48 (W8.of_int 31));
    initial_block <-
    (BArray136.set8d initial_block (136 - 1) (W8.of_int 128));
    state <@ __state_init_avx2 ();
    state <@ shake256_absorb_block (state, initial_block);
    return state;
  }
  proc sample____challenge (output_challenge:BArray1024.t, seed:BArray48.t) : 
  BArray1024.t = {
    var zeros_256:W256.t;
    var state:BArray224.t;
    var xof_block:BArray136.t;
    var signs:W64.t;
    var xof_offset:W64.t;
    var i:W64.t;
    var sample_at:W64.t;
    var coefficient:W32.t;
    var shift:W32.t;
    state <- witness;
    xof_block <- witness;
    zeros_256 <- (set0_256);
    state <@ sample____initialize_xof (seed);
    xof_block <@ shake256_squeeze_block (xof_block, state);
    signs <- (BArray136.get64d xof_block 0);
    xof_offset <- (W64.of_int 8);
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int ((256 * 32) %/ 8)))) {
      output_challenge <-
      (BArray1024.set256d output_challenge (W64.to_uint i) zeros_256);
      i <- (i + (W64.of_int 32));
    }
    i <- (W64.of_int (256 - 49));
    while ((i \ult (W64.of_int 256))) {
      if (((W64.of_int 136) \ule xof_offset)) {
        state <@ _keccakf1600_avx2 (state);
        xof_block <@ shake256_squeeze_block (xof_block, state);
        xof_offset <- (W64.of_int 0);
      } else {
        
      }
      sample_at <-
      (zeroextu64 (BArray136.get8 xof_block (W64.to_uint xof_offset)));
      xof_offset <- (xof_offset + (W64.of_int 1));
      while ((i \ult sample_at)) {
        if (((W64.of_int 136) \ule xof_offset)) {
          state <@ _keccakf1600_avx2 (state);
          xof_block <@ shake256_squeeze_block (xof_block, state);
          xof_offset <- (W64.of_int 0);
        } else {
          
        }
        sample_at <-
        (zeroextu64 (BArray136.get8 xof_block (W64.to_uint xof_offset)));
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
  proc __setup_state_to_generate_mask (rho_prime:BArray64.t,
                                       domain_separator:W16.t) : BArray224.t = {
    var state:BArray224.t;
    var zero_256:W256.t;
    var copied_32_bytes:W256.t;
    var initial_block:BArray136.t;
    initial_block <- witness;
    state <- witness;
    state <@ __state_init_avx2 ();
    zero_256 <- (set0_256);
    copied_32_bytes <- (BArray64.get256d rho_prime 0);
    initial_block <- (BArray136.set256d initial_block 0 copied_32_bytes);
    copied_32_bytes <- (BArray64.get256d rho_prime 32);
    initial_block <- (BArray136.set256d initial_block 32 copied_32_bytes);
    initial_block <- (BArray136.set16d initial_block 64 domain_separator);
    initial_block <- (BArray136.set8d initial_block 66 (W8.of_int 31));
    initial_block <- (BArray136.set256d initial_block 67 zero_256);
    initial_block <- (BArray136.set256d initial_block 99 zero_256);
    initial_block <- (BArray136.set32d initial_block 131 (W32.of_int 0));
    initial_block <-
    (BArray136.set8d initial_block (136 - 1) (W8.of_int 128));
    state <@ shake256_absorb_block (state, initial_block);
    return state;
  }
  proc __sample_mask_polynomial_1x (mask:BArray1024.t, rho_prime:BArray64.t,
                                    domain_separator:W16.t) : BArray1024.t = {
    var aux:BArray136.t;
    var inc:int;
    var state:BArray224.t;
    var i:int;
    var mask_encoded:BArray680.t;
    mask_encoded <- witness;
    state <- witness;
    state <@ __setup_state_to_generate_mask (rho_prime, domain_separator);
    inc <- (((((20 * 256) %/ 8) + 136) - 1) %/ 136);
    i <- 0;
    while ((i < inc)) {
      aux <@ shake256_squeeze_block ((SBArray680_136.get_sub8 mask_encoded
                                     (i * 136)),
      state);
      mask_encoded <- (SBArray680_136.set_sub8 mask_encoded (i * 136) aux);
      state <@ _keccakf1600_avx2 (state);
      i <- (i + 1);
    }
    mask <@ gamma1____decode_to_polynomial (mask,
    (SBArray680_640.get_sub8 mask_encoded 0));
    return mask;
  }
  proc absorb_for_shake256_4x (state:BArray800.t, rho_prime:BArray64.t,
                               starting_domain_separator:W16.t) : BArray800.t = {
    var zeros:W256.t;
    var i:int;
    var t64:W64.t;
    var t256:W256.t;
    var lane:int;
    zeros <- (set0_256);
    i <- 0;
    while ((i < 25)) {
      state <- (BArray800.set256 state i zeros);
      i <- (i + 1);
    }
    i <- 0;
    while ((i < 8)) {
      t64 <- (BArray64.get64d rho_prime (8 * i));
      t256 <- (zeroextu256 t64);
      t256 <- (VPBROADCAST_4u64 (truncateu64 t256));
      state <- (BArray800.set256 state i t256);
      i <- (i + 1);
    }
    lane <- 0;
    while ((lane < 4)) {
      t64 <- (zeroextu64 starting_domain_separator);
      t64 <- (LEA_64 ((W64.of_int 2031616) + t64));
      t256 <- (zeroextu256 t64);
      t256 <- (VPBROADCAST_4u64 (truncateu64 t256));
      t256 <- (VPADD_4u64 t256 cONST_0123);
      state <- (BArray800.set256 state 8 t256);
      lane <- (lane + 1);
    }
    t64 <- (W64.of_int 9223372036854775808);
    t256 <- (zeroextu256 t64);
    t256 <- (VPBROADCAST_4u64 (truncateu64 t256));
    state <- (BArray800.set256 state 16 t256);
    return state;
  }
  proc shake256_squeeze_multiple_blocks_4x (state:BArray800.t,
                                            b0:BArray680.t, b1:BArray680.t,
                                            b2:BArray680.t, b3:BArray680.t) : 
  BArray800.t * BArray680.t * BArray680.t * BArray680.t * BArray680.t = {
    var aux_0:BArray136.t;
    var aux_1:BArray136.t;
    var aux_2:BArray136.t;
    var aux_3:BArray136.t;
    var aux:BArray800.t;
    var inc:int;
    var i:int;
    inc <- (((((20 * 256) %/ 8) + 136) - 1) %/ 136);
    i <- 0;
    while ((i < inc)) {
      (aux, aux_0, aux_1, aux_2, aux_3) <@ shake256_squeezeblock4x (state,
      (SBArray680_136.get_sub8 b0 (i * 136)),
      (SBArray680_136.get_sub8 b1 (i * 136)),
      (SBArray680_136.get_sub8 b2 (i * 136)),
      (SBArray680_136.get_sub8 b3 (i * 136)));
      state <- aux;
      b0 <- (SBArray680_136.set_sub8 b0 (i * 136) aux_0);
      b1 <- (SBArray680_136.set_sub8 b1 (i * 136) aux_1);
      b2 <- (SBArray680_136.set_sub8 b2 (i * 136) aux_2);
      b3 <- (SBArray680_136.set_sub8 b3 (i * 136) aux_3);
      i <- (i + 1);
    }
    return (state, b0, b1, b2, b3);
  }
  proc __sample_mask_polynomial_4x (rho_prime:BArray64.t,
                                    starting_domain_separator:W16.t) : 
  BArray1024.t * BArray1024.t * BArray1024.t * BArray1024.t = {
    var mask0:BArray1024.t;
    var mask1:BArray1024.t;
    var mask2:BArray1024.t;
    var mask3:BArray1024.t;
    var xof_state:BArray800.t;
    var mask_encoded0:BArray680.t;
    var mask_encoded1:BArray680.t;
    var mask_encoded2:BArray680.t;
    var mask_encoded3:BArray680.t;
    var  _0:BArray800.t;
     _0 <- witness;
    mask0 <- witness;
    mask1 <- witness;
    mask2 <- witness;
    mask3 <- witness;
    mask_encoded0 <- witness;
    mask_encoded1 <- witness;
    mask_encoded2 <- witness;
    mask_encoded3 <- witness;
    xof_state <- witness;
    xof_state <@ absorb_for_shake256_4x (xof_state, rho_prime,
    starting_domain_separator);
    ( _0, mask_encoded0, mask_encoded1, mask_encoded2, mask_encoded3) <@ 
    shake256_squeeze_multiple_blocks_4x (xof_state, mask_encoded0,
    mask_encoded1, mask_encoded2, mask_encoded3);
    mask0 <@ gamma1____decode_to_polynomial (mask0,
    (SBArray680_640.get_sub8 mask_encoded0 0));
    mask1 <@ gamma1____decode_to_polynomial (mask1,
    (SBArray680_640.get_sub8 mask_encoded1 0));
    mask2 <@ gamma1____decode_to_polynomial (mask2,
    (SBArray680_640.get_sub8 mask_encoded2 0));
    mask3 <@ gamma1____decode_to_polynomial (mask3,
    (SBArray680_640.get_sub8 mask_encoded3 0));
    return (mask0, mask1, mask2, mask3);
  }
  proc polynomial__add (sum_pointer:BArray1024.t, lhs_pointer:BArray1024.t,
                        rhs_pointer:BArray1024.t) : BArray1024.t = {
    var offset:W64.t;
    var lhs:W256.t;
    var rhs:W256.t;
    var sum:W256.t;
    offset <- (W64.of_int 0);
    while ((offset \ult (W64.of_int ((256 * 32) %/ 8)))) {
      lhs <- (BArray1024.get256d lhs_pointer (W64.to_uint offset));
      rhs <- (BArray1024.get256d rhs_pointer (W64.to_uint offset));
      sum <- (VPADD_8u32 lhs rhs);
      sum_pointer <-
      (BArray1024.set256d sum_pointer (W64.to_uint offset) sum);
      offset <- (offset + (W64.of_int 32));
    }
    return sum_pointer;
  }
  proc polynomial__subtract (difference_pointer:BArray1024.t,
                             lhs_pointer:BArray1024.t,
                             rhs_pointer:BArray1024.t) : BArray1024.t = {
    var offset:W64.t;
    var lhs:W256.t;
    var rhs:W256.t;
    var difference:W256.t;
    offset <- (W64.of_int 0);
    while ((offset \ult (W64.of_int ((256 * 32) %/ 8)))) {
      lhs <- (BArray1024.get256d lhs_pointer (W64.to_uint offset));
      rhs <- (BArray1024.get256d rhs_pointer (W64.to_uint offset));
      difference <- (VPSUB_8u32 lhs rhs);
      difference_pointer <-
      (BArray1024.set256d difference_pointer (W64.to_uint offset) difference);
      offset <- (offset + (W64.of_int 32));
    }
    return difference_pointer;
  }
  proc polynomial____pointwise_add_to_total (total:BArray1024.t,
                                             polynomial:BArray1024.t) : 
  BArray1024.t = {
    var offset:W64.t;
    var lhs:W256.t;
    var rhs:W256.t;
    var sum:W256.t;
    offset <- (W64.of_int 0);
    while ((offset \ult (W64.of_int ((256 * 32) %/ 8)))) {
      lhs <- (BArray1024.get256d polynomial (W64.to_uint offset));
      rhs <- (BArray1024.get256d total (W64.to_uint offset));
      sum <- (VPADD_8u32 lhs rhs);
      total <- (BArray1024.set256d total (W64.to_uint offset) sum);
      offset <- (offset + (W64.of_int 32));
    }
    return total;
  }
  proc polynomial____zero (polynomial:BArray1024.t) : BArray1024.t = {
    var zero_u256:W256.t;
    var offset:W64.t;
    zero_u256 <- (set0_256);
    offset <- (W64.of_int 0);
    while ((offset \ult (W64.of_int ((256 * 32) %/ 8)))) {
      polynomial <-
      (BArray1024.set256d polynomial (W64.to_uint offset) zero_u256);
      offset <- (offset + (W64.of_int 32));
    }
    return polynomial;
  }
  proc polynomial____check_infinity_norm (polynomial:BArray1024.t,
                                          threshold:int) : W8.t = {
    var result:W8.t;
    var temp:W64.t;
    var threshold_vector:W256.t;
    var exceeds_any:W256.t;
    var offset:W64.t;
    var coefficients:W256.t;
    var exceeds:W256.t;
    var msb_mask:W32.t;
    var zf:bool;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    temp <- (W64.of_int (threshold - 1));
    threshold_vector <- (zeroextu256 (VMOV_64 temp));
    threshold_vector <- (VPBROADCAST_8u32 (truncateu32 threshold_vector));
    exceeds_any <- (set0_256);
    offset <- (W64.of_int 0);
    while ((offset \ult (W64.of_int ((256 * 32) %/ 8)))) {
      coefficients <- (BArray1024.get256d polynomial (W64.to_uint offset));
      coefficients <- (VPABS_8u32 coefficients);
      exceeds <- (VPCMPGT_8u32 coefficients threshold_vector);
      exceeds_any <- (VPOR_256 exceeds_any exceeds);
      offset <- (offset + (W64.of_int 32));
    }
    exceeds_any <- exceeds_any;
    msb_mask <- (MOVEMASK_8u32 exceeds_any);
    ( _0,  _1,  _2,  _3, zf) <- (TEST_32 msb_mask msb_mask);
    result <- (SETcc (! zf));
    return result;
  }
  proc polynomial____shift_coefficients_left (polynomial:BArray1024.t) : 
  BArray1024.t = {
    var offset:W64.t;
    var coefficients:W256.t;
    offset <- (W64.of_int 0);
    while ((offset \ult (W64.of_int ((256 * 32) %/ 8)))) {
      coefficients <- (BArray1024.get256d polynomial (W64.to_uint offset));
      coefficients <- (VPSLL_8u32 coefficients (W128.of_int 13));
      polynomial <-
      (BArray1024.set256d polynomial (W64.to_uint offset) coefficients);
      offset <- (offset + (W64.of_int 32));
    }
    return polynomial;
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
      product <@ polynomial__pointwise_montgomery_multiply_and_reduce (
      product, (SBArray5120_1024.get_sub32 lhs (256 * i)),
      (SBArray5120_1024.get_sub32 rhs (256 * i)));
      (* Erased call to unspill *)
      output <@ polynomial____pointwise_add_to_total (output, product);
      (* Erased call to spill *)
      i <- (i + 1);
    }
    return output;
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
  proc column_vector____power2round (vector:BArray6144.t) : BArray6144.t *
                                                            BArray6144.t = {
    var aux:BArray1024.t;
    var aux_0:BArray1024.t;
    var t1:BArray6144.t;
    var t0:BArray6144.t;
    var i:int;
    t0 <- witness;
    t1 <- witness;
    i <- 0;
    while ((i < 6)) {
      (aux, aux_0) <@ polynomial____power2round ((SBArray6144_1024.get_sub32
                                                 t1 (i * 256)),
      (SBArray6144_1024.get_sub32 t0 (i * 256)),
      (SBArray6144_1024.get_sub32 vector (i * 256)));
      t1 <- (SBArray6144_1024.set_sub32 t1 (i * 256) aux);
      t0 <- (SBArray6144_1024.set_sub32 t0 (i * 256) aux_0);
      i <- (i + 1);
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
    var aux:BArray1024.t;
    var aux_0:BArray1024.t;
    var low:BArray6144.t;
    var high:BArray6144.t;
    var i:int;
    high <- witness;
    low <- witness;
    i <- 0;
    while ((i < 6)) {
      (aux, aux_0) <@ polynomial__decompose ((SBArray6144_1024.get_sub32 
                                             low (i * 256)),
      (SBArray6144_1024.get_sub32 high (i * 256)),
      (SBArray6144_1024.get_sub32 vector (i * 256)));
      low <- (SBArray6144_1024.set_sub32 low (i * 256) aux);
      high <- (SBArray6144_1024.set_sub32 high (i * 256) aux_0);
      i <- (i + 1);
    }
    return (low, high);
  }
  proc t0__coefficients_to_bytestream (coefficients:W256.t) : W128.t = {
    var bytestream:W128.t;
    var shifts:W256.t;
    var _bytestream:W256.t;
    var second_4:W256.t;
    shifts <- hALF_OF_BITS_IN_T0_VECTOR;
    coefficients <- (VPSUB_8u32 shifts coefficients);
    shifts <- (BArray128.get256 t0__ENCODING_SHIFTS_TABLE 0);
    _bytestream <- (VPSLLV_8u32 coefficients shifts);
    _bytestream <- (VPSRL_4u64 _bytestream (W128.of_int 19));
    shifts <- (BArray128.get256 t0__ENCODING_SHIFTS_TABLE 1);
    _bytestream <- (VPERMD shifts _bytestream);
    shifts <- (BArray128.get256 t0__ENCODING_SHIFTS_TABLE 2);
    _bytestream <- (VPSLLV_8u32 _bytestream shifts);
    _bytestream <- (VPSRL_4u64 _bytestream (W128.of_int 6));
    second_4 <- (VPSRLDQ_256 _bytestream (W8.of_int 8));
    second_4 <- (VPSLL_4u64 second_4 (W128.of_int 52));
    _bytestream <- (VPADD_4u64 _bytestream second_4);
    shifts <- (BArray128.get256 t0__ENCODING_SHIFTS_TABLE 3);
    _bytestream <- (VPSRLV_4u64 _bytestream shifts);
    bytestream <- (VEXTRACTI128 _bytestream (W8.of_int 0));
    return bytestream;
  }
  proc t0__encode_polynomial (t0_encoded:BArray416.t, t0:BArray1024.t) : 
  BArray416.t = {
    var input_offset:W64.t;
    var output_offset:W64.t;
    var coefficients:W256.t;
    var bytestream:W128.t;
    var final_encoded_output:BArray16.t;
    var i:int;
    final_encoded_output <- witness;
    input_offset <- (W64.of_int 0);
    output_offset <- (W64.of_int 0);
    while ((input_offset \ult (W64.of_int (((256 * 32) %/ 8) - 32)))) {
      coefficients <- (BArray1024.get256d t0 (W64.to_uint input_offset));
      input_offset <- (input_offset + (W64.of_int 32));
      bytestream <@ t0__coefficients_to_bytestream (coefficients);
      t0_encoded <-
      (BArray416.set128d t0_encoded (W64.to_uint output_offset) bytestream);
      output_offset <- (output_offset + (W64.of_int 13));
    }
    coefficients <- (BArray1024.get256d t0 (W64.to_uint input_offset));
    bytestream <@ t0__coefficients_to_bytestream (coefficients);
    final_encoded_output <-
    (BArray16.set128d final_encoded_output 0 bytestream);
    i <- 0;
    while ((i < 13)) {
      t0_encoded <-
      (BArray416.set8 t0_encoded
      (W64.to_uint (output_offset + (W64.of_int i)))
      (BArray16.get8 final_encoded_output i));
      i <- (i + 1);
    }
    return t0_encoded;
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
  proc t0__bytestream_to_coefficients (bytestream:W128.t) : W256.t = {
    var coefficients:W256.t;
    var shifts:W256.t;
    var mask:W256.t;
    coefficients <- (set0_256);
    coefficients <- (VINSERTI128 coefficients bytestream (W8.of_int 0));
    coefficients <- (VINSERTI128 coefficients bytestream (W8.of_int 1));
    shifts <- (BArray96.get256 t0__DECODING_TABLE 0);
    coefficients <- (VPSHUFB_256 coefficients shifts);
    shifts <- (BArray96.get256 t0__DECODING_TABLE 1);
    coefficients <- (VPSRLV_8u32 coefficients shifts);
    mask <- (BArray96.get256 t0__DECODING_TABLE 2);
    coefficients <- (VPAND_256 coefficients mask);
    shifts <- hALF_OF_BITS_IN_T0_VECTOR;
    coefficients <- (VPSUB_8u32 shifts coefficients);
    return coefficients;
  }
  proc t0____decode_polynomial (t0:BArray1024.t, t0_encoded:BArray416.t) : 
  BArray1024.t = {
    var input_offset:W64.t;
    var output_offset:W64.t;
    var bytestream:W128.t;
    var coefficients:W256.t;
    input_offset <- (W64.of_int 0);
    output_offset <- (W64.of_int 0);
    while ((input_offset \ult (W64.of_int (((13 * 256) %/ 8) - 13)))) {
      bytestream <-
      (BArray416.get128d t0_encoded (W64.to_uint input_offset));
      input_offset <- (input_offset + (W64.of_int 13));
      coefficients <@ t0__bytestream_to_coefficients (bytestream);
      t0 <- (BArray1024.set256d t0 (W64.to_uint output_offset) coefficients);
      output_offset <- (output_offset + (W64.of_int 32));
    }
    bytestream <- (BArray416.get128d t0_encoded (((13 * 256) %/ 8) - 16));
    bytestream <- (VPSRLDQ_128 bytestream (W8.of_int 3));
    coefficients <@ t0__bytestream_to_coefficients (bytestream);
    t0 <- (BArray1024.set256d t0 (W64.to_uint output_offset) coefficients);
    return t0;
  }
  proc t0__decode (t0:BArray6144.t, encoded:BArray2496.t) : BArray6144.t = {
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
  proc t1__coefficients_to_bytestream (coefficients:W256.t) : W128.t = {
    var bytestream:W128.t;
    var shifts:W256.t;
    var _bytestream:W256.t;
    var shifts_128:W128.t;
    shifts <- (BArray96.get256 t1__ENCODING_SHIFTS_TABLE 0);
    _bytestream <- (VPSLLV_8u32 coefficients shifts);
    _bytestream <- (VPSRL_4u64 _bytestream (W128.of_int 22));
    shifts <- (BArray96.get256 t1__ENCODING_SHIFTS_TABLE 1);
    _bytestream <- (VPERMD shifts _bytestream);
    shifts <- (BArray96.get256 t1__ENCODING_SHIFTS_TABLE 2);
    _bytestream <- (VPSLLV_8u32 _bytestream shifts);
    _bytestream <- (VPSRL_4u64 _bytestream (W128.of_int 12));
    _bytestream <- (VPERMQ _bytestream (W8.of_int 8));
    bytestream <- (VEXTRACTI128 _bytestream (W8.of_int 0));
    shifts_128 <- t1__SHUFFLE_TO_GROUP;
    bytestream <- (VPSHUFB_128 bytestream shifts_128);
    return bytestream;
  }
  proc t1__encode_polynomial (t1_encoded:BArray320.t, t1:BArray1024.t) : 
  BArray320.t = {
    var input_offset:W64.t;
    var output_offset:W64.t;
    var coefficients:W256.t;
    var bytestream:W128.t;
    var final_encoded_output:BArray16.t;
    var i:int;
    final_encoded_output <- witness;
    input_offset <- (W64.of_int 0);
    output_offset <- (W64.of_int 0);
    while ((input_offset \ult (W64.of_int (((256 * 32) %/ 8) - 32)))) {
      coefficients <- (BArray1024.get256d t1 (W64.to_uint input_offset));
      input_offset <- (input_offset + (W64.of_int 32));
      bytestream <@ t1__coefficients_to_bytestream (coefficients);
      t1_encoded <-
      (BArray320.set128d t1_encoded (W64.to_uint output_offset) bytestream);
      output_offset <- (output_offset + (W64.of_int 10));
    }
    coefficients <- (BArray1024.get256d t1 (W64.to_uint input_offset));
    bytestream <@ t1__coefficients_to_bytestream (coefficients);
    final_encoded_output <-
    (BArray16.set128d final_encoded_output 0 bytestream);
    i <- 0;
    while ((i < 10)) {
      t1_encoded <-
      (BArray320.set8 t1_encoded
      (W64.to_uint (output_offset + (W64.of_int i)))
      (BArray16.get8 final_encoded_output i));
      i <- (i + 1);
    }
    return t1_encoded;
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
  proc t1__decode_polynomial (t1:BArray1024.t, t1_encoded:BArray320.t) : 
  BArray1024.t = {
    var coefficients:W256.t;
    var input_offset:W64.t;
    var output_offset:W64.t;
    var bytestream:W128.t;
    var shifts:W256.t;
    coefficients <- (set0_256);
    input_offset <- (W64.of_int 0);
    output_offset <- (W64.of_int 0);
    while ((input_offset \ult (W64.of_int ((((23 - 13) * 256) %/ 8) - 10)))) {
      bytestream <-
      (BArray320.get128d t1_encoded (W64.to_uint input_offset));
      input_offset <- (input_offset + (W64.of_int 10));
      coefficients <- (VINSERTI128 coefficients bytestream (W8.of_int 0));
      coefficients <- (VINSERTI128 coefficients bytestream (W8.of_int 1));
      shifts <- (BArray64.get256 t1__DECODING_TABLE 0);
      coefficients <- (VPSHUFB_256 coefficients shifts);
      shifts <- (BArray64.get256 t1__DECODING_TABLE 1);
      coefficients <- (VPSRLV_8u32 coefficients shifts);
      coefficients <- (VPAND_256 coefficients t1__mask);
      t1 <- (BArray1024.set256d t1 (W64.to_uint output_offset) coefficients);
      output_offset <- (output_offset + (W64.of_int 32));
    }
    bytestream <-
    (BArray320.get128d t1_encoded ((((23 - 13) * 256) %/ 8) - 16));
    bytestream <- (VPSRLDQ_128 bytestream (W8.of_int 6));
    coefficients <- (VINSERTI128 coefficients bytestream (W8.of_int 0));
    coefficients <- (VINSERTI128 coefficients bytestream (W8.of_int 1));
    shifts <- (BArray64.get256 t1__DECODING_TABLE 0);
    coefficients <- (VPSHUFB_256 coefficients shifts);
    shifts <- (BArray64.get256 t1__DECODING_TABLE 1);
    coefficients <- (VPSRLV_8u32 coefficients shifts);
    coefficients <- (VPAND_256 coefficients t1__mask);
    t1 <- (BArray1024.set256d t1 (W64.to_uint output_offset) coefficients);
    return t1;
  }
  proc signature____encode (signature:BArray3309.t,
                            commitment_hash:BArray48.t,
                            signer_response:BArray5120.t, hint_0:BArray6144.t) : 
  BArray3309.t = {
    var aux:BArray640.t;
    var i:W64.t;
    var bytes:W128.t;
    var k:int;
    var offset:int;
    var hints_written:W64.t;
    var j:W64.t;
    var hint_offset:W64.t;
    var hint_coefficient:W32.t;
    var condition:bool;
    i <- (W64.of_int 0);
    while ((i \ult (W64.of_int 48))) {
      bytes <- (BArray48.get128d commitment_hash (W64.to_uint i));
      signature <- (BArray3309.set128d signature (W64.to_uint i) bytes);
      i <- (i + (W64.of_int 16));
    }
    k <- 0;
    while ((k < 5)) {
      offset <- (48 + (k * ((20 * 256) %/ 8)));
      aux <@ gamma1____encode_polynomial ((SBArray3309_640.get_sub8 signature
                                          offset),
      (SBArray5120_1024.get_sub32 signer_response (k * 256)));
      signature <- (SBArray3309_640.set_sub8 signature offset aux);
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
    hints_written <- (W64.of_int 0);
    i <- (W64.of_int 0);
    condition <- (i \ult (W64.of_int 6));
    while (condition) {
      j <- (W64.of_int 0);
      condition <- (j \ult (W64.of_int 256));
      while (condition) {
        hint_offset <- i;
        hint_offset <- (hint_offset `<<` (W8.of_int 8));
        hint_offset <- (hint_offset + j);
        hint_coefficient <-
        (BArray6144.get32 hint_0 (W64.to_uint hint_offset));
        if ((hint_coefficient <> (W32.of_int 0))) {
          signature <-
          (BArray3309.set8 signature
          (W64.to_uint
          ((W64.of_int (48 + (5 * ((20 * 256) %/ 8)))) + hints_written))
          (truncateu8 j));
          hints_written <- (hints_written + (W64.of_int 1));
        } else {
          
        }
        j <- (j + (W64.of_int 1));
        condition <- (j \ult (W64.of_int 256));
      }
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
            if ((previous_true_hints_seen \ult j)) {
              hint_at_j_minus_one <-
              (zeroextu64
              (BArray61.get8 hint_encoded (W64.to_uint (j - (W64.of_int 1))))
              );
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
  proc hash_verification_key (verification_key_hash:BArray64.t,
                              verification_key:BArray1952.t) : BArray64.t = {
    var state:BArray224.t;
    var verification_key_offset:W64.t;
    var block:BArray48.t;
    var t64:W64.t;
    var t128_0:W128.t;
    var r0:W256.t;
    var r1:W256.t;
    var t128_1:W128.t;
    var r2:W256.t;
    block <- witness;
    state <- witness;
    state <@ __state_init_avx2 ();
    verification_key_offset <- (W64.of_int 0);
    while ((verification_key_offset \ult
           (W64.of_int (((32 + (6 * (((23 - 13) * 256) %/ 8))) %/ 136) * 136)
           ))) {
      state <@ shake256_absorb_block (state,
      (SBArray1952_136.get_sub8 verification_key
      (W64.to_uint verification_key_offset)));
      verification_key_offset <-
      (verification_key_offset + (W64.of_int 136));
    }
    block <-
    (SBArray1952_48.get_sub8 verification_key
    (W64.to_uint verification_key_offset));
    t64 <- (BArray48.get64d block 0);
    t128_0 <- (zeroextu128 t64);
    r0 <- (VPBROADCAST_4u64 (truncateu64 t128_0));
    state <- (BArray224.set256 state 0 ((BArray224.get256 state 0) `^` r0));
    r1 <- (BArray48.get256d block 8);
    state <- (BArray224.set256 state 1 ((BArray224.get256 state 1) `^` r1));
    t64 <- (BArray48.get64d block 40);
    t128_1 <- (zeroextu128 t64);
    t128_0 <- (set0_128);
    t64 <- (W64.of_int 0);
    t128_1 <- (VPINSR_2u64 t128_1 t64 (W8.of_int 1));
    r2 <-
    (W256.of_int
    (((W128.to_uint t128_0) %% (2 ^ 128)) +
    ((2 ^ 128) * (W128.to_uint t128_1))));
    state <- (BArray224.set256 state 2 ((BArray224.get256 state 2) `^` r2));
    t64 <- (W64.of_int 31);
    r2 <- (zeroextu256 (VMOV_64 t64));
    state <- (BArray224.set256 state 6 ((BArray224.get256 state 6) `^` r2));
    state <@ shake256_add_rate_bit (state);
    state <@ _keccakf1600_avx2 (state);
    verification_key_hash <@ squeeze_64_bytes (verification_key_hash, state);
    return verification_key_hash;
  }
  proc __derive_commitment_hash (message_representative:BArray64.t,
                                 encoded_commitment:BArray768.t) : BArray48.t = {
    var commitment_hash:BArray48.t;
    var copied_32_bytes:W256.t;
    var initial_block:BArray136.t;
    var copied_8_bytes:W64.t;
    var state:BArray224.t;
    var encoded_commitment_offset:W64.t;
    var block:BArray16.t;
    var t64:W64.t;
    var t128:W128.t;
    var r0:W256.t;
    block <- witness;
    commitment_hash <- witness;
    initial_block <- witness;
    state <- witness;
    copied_32_bytes <- (BArray64.get256d message_representative 0);
    initial_block <- (BArray136.set256d initial_block 0 copied_32_bytes);
    copied_32_bytes <- (BArray64.get256d message_representative 32);
    initial_block <- (BArray136.set256d initial_block 32 copied_32_bytes);
    copied_32_bytes <- (BArray768.get256d encoded_commitment 0);
    initial_block <- (BArray136.set256d initial_block 64 copied_32_bytes);
    copied_32_bytes <- (BArray768.get256d encoded_commitment 32);
    initial_block <- (BArray136.set256d initial_block 96 copied_32_bytes);
    copied_8_bytes <- (BArray768.get64d encoded_commitment 64);
    initial_block <- (BArray136.set64d initial_block 128 copied_8_bytes);
    state <@ __state_init_avx2 ();
    state <@ shake256_absorb_block (state, initial_block);
    encoded_commitment_offset <- (W64.of_int 72);
    while ((encoded_commitment_offset \ult
           (W64.of_int ((((((4 * 256) %/ 8) * 6) - 72) %/ 136) * 136)))) {
      state <@ shake256_absorb_block (state,
      (SBArray768_136.get_sub8 encoded_commitment
      (W64.to_uint encoded_commitment_offset)));
      encoded_commitment_offset <-
      (encoded_commitment_offset + (W64.of_int 136));
    }
    block <-
    (SBArray768_16.get_sub8 encoded_commitment
    (W64.to_uint encoded_commitment_offset));
    t64 <- (BArray16.get64d block 0);
    t128 <- (zeroextu128 t64);
    r0 <- (VPBROADCAST_4u64 (truncateu64 t128));
    state <- (BArray224.set256 state 0 ((BArray224.get256 state 0) `^` r0));
    t64 <- (BArray16.get64d block 8);
    t128 <- (VMOV_64 t64);
    t64 <- (W64.of_int 31);
    t128 <- (VPINSR_2u64 t128 t64 (W8.of_int 1));
    r0 <- (set0_256);
    r0 <- (VINSERTI128 r0 t128 (W8.of_int 0));
    state <- (BArray224.set256 state 1 ((BArray224.get256 state 1) `^` r0));
    state <@ shake256_add_rate_bit (state);
    state <@ _keccakf1600_avx2 (state);
    t128 <- (truncateu128 (BArray224.get256 state 0));
    commitment_hash <-
    (BArray48.set64d commitment_hash 0 (truncateu64 t128));
    commitment_hash <-
    (BArray48.set256d commitment_hash 8 (BArray224.get256 state 1));
    t128 <- (VEXTRACTI128 (BArray224.get256 state 2) (W8.of_int 1));
    commitment_hash <-
    (BArray48.set64d commitment_hash 40 (truncateu64 t128));
    return commitment_hash;
  }
  proc error_4x____bytestream_to_coefficients (bytestream:W128.t) : W256.t = {
    var coefficients:W256.t;
    var temp:W64.t;
    var mask:W256.t;
    var odd_coefficients:W256.t;
    temp <- (W64.of_int ((1 `<<` 4) - 1));
    mask <- (zeroextu256 (VMOV_64 temp));
    mask <- (VPBROADCAST_32u8 (truncateu8 mask));
    coefficients <- (VPMOVZX_16u8_16u16 bytestream);
    odd_coefficients <- (VPSLL_16u16 coefficients (W128.of_int 4));
    coefficients <- (VPOR_256 coefficients odd_coefficients);
    coefficients <- (VPAND_256 coefficients mask);
    return coefficients;
  }
  proc error_4x____write_out_8_coefficients (error:BArray1024.t,
                                             bytes_filled:W64.t,
                                             good_overall:W64.t,
                                             coefficient_block:W128.t) : 
  BArray1024.t * W64.t * W64.t = {
    var good:W64.t;
    var shuffle_table_pointer:BArray2048.t;
    var shuffle_table_idx:W64.t;
    var shuffles:W128.t;
    var error_coefficients_128:W128.t;
    var error_coefficients:W256.t;
    var  _0:bool;
    var  _1:bool;
    var  _2:bool;
    var  _3:bool;
    var  _4:bool;
    shuffle_table_pointer <- witness;
    good <- good_overall;
    good <- (good `&` (W64.of_int 255));
    good_overall <- (good_overall `>>` (W8.of_int 8));
    shuffle_table_pointer <- eRROR_VECTOR_SHUFFLE_TABLE;
    shuffle_table_idx <- good;
    shuffle_table_idx <- (shuffle_table_idx `<<` (W8.of_int 3));
    shuffles <-
    (zeroextu128
    (BArray2048.get64d shuffle_table_pointer (W64.to_uint shuffle_table_idx))
    );
    error_coefficients_128 <- (VPSHUFB_128 coefficient_block shuffles);
    error_coefficients <-
    (VPMOVSX_8u8_8u32 (truncateu64 error_coefficients_128));
    error <-
    (BArray1024.set256d error (W64.to_uint bytes_filled) error_coefficients);
    ( _0,  _1,  _2,  _3,  _4, good) <- (POPCNT_64 good);
    good <- (good `<<` (W8.of_int 2));
    bytes_filled <- (bytes_filled + good);
    return (error, bytes_filled, good_overall);
  }
  proc error_4x__rejection_sample_multiple_blocks (error:BArray1024.t,
                                                   randombytes:BArray272.t) : 
  BArray1024.t * W64.t = {
    var filled:W64.t;
    var temp:W64.t;
    var eta_0:W256.t;
    var bound:W256.t;
    var bytes_filled:W64.t;
    var xof_offset:W64.t;
    var stop_sampling:W64.t;
    var bytestream:W128.t;
    var coefficients:W256.t;
    var comparisons:W256.t;
    var good_overall:W64.t;
    var coefficient_block:W128.t;
    var coefficient:W32.t;
    var  _0:W64.t;
    temp <- (W64.of_int 4);
    eta_0 <- (zeroextu256 (VMOV_64 temp));
    eta_0 <- (VPBROADCAST_32u8 (truncateu8 eta_0));
    temp <- (W64.of_int 9);
    bound <- (zeroextu256 (VMOV_64 temp));
    bound <- (VPBROADCAST_32u8 (truncateu8 bound));
    bytes_filled <- (W64.of_int 0);
    xof_offset <- (W64.of_int 0);
    stop_sampling <- (W64.of_int 0);
    while ((stop_sampling <> (W64.of_int 1))) {
      bytestream <- (BArray272.get128d randombytes (W64.to_uint xof_offset));
      coefficients <@ error_4x____bytestream_to_coefficients (bytestream);
      comparisons <- (VPSUB_32u8 coefficients bound);
      good_overall <- (zeroextu64 (MOVEMASK_32u8 comparisons));
      coefficients <- (VPSUB_32u8 eta_0 coefficients);
      coefficient_block <- (VEXTRACTI128 coefficients (W8.of_int 0));
      good_overall <- good_overall;
      (error, bytes_filled, good_overall) <@ error_4x____write_out_8_coefficients (
      error, bytes_filled, good_overall, coefficient_block);
      xof_offset <- (xof_offset + (W64.of_int 4));
      if ((bytes_filled \ult (W64.of_int (((256 * 32) %/ 8) - 32)))) {
        coefficient_block <- (VPSRLDQ_128 coefficient_block (W8.of_int 8));
        (error, bytes_filled, good_overall) <@ error_4x____write_out_8_coefficients (
        error, bytes_filled, good_overall, coefficient_block);
        xof_offset <- (xof_offset + (W64.of_int 4));
        if ((bytes_filled \ult (W64.of_int (((256 * 32) %/ 8) - 32)))) {
          coefficient_block <- (VEXTRACTI128 coefficients (W8.of_int 1));
          (error, bytes_filled, good_overall) <@ error_4x____write_out_8_coefficients (
          error, bytes_filled, good_overall, coefficient_block);
          xof_offset <- (xof_offset + (W64.of_int 4));
          if ((bytes_filled \ult (W64.of_int (((256 * 32) %/ 8) - 32)))) {
            coefficient_block <-
            (VPSRLDQ_128 coefficient_block (W8.of_int 8));
            (error, bytes_filled,  _0) <@ error_4x____write_out_8_coefficients (
            error, bytes_filled, good_overall, coefficient_block);
            xof_offset <- (xof_offset + (W64.of_int 4));
          } else {
            
          }
        } else {
          
        }
      } else {
        
      }
      if (((W64.of_int (((256 * 32) %/ 8) - 32)) \ule bytes_filled)) {
        stop_sampling <- (W64.of_int 1);
      } else {
        if (((W64.of_int ((2 * 136) - 16)) \ule xof_offset)) {
          stop_sampling <- (W64.of_int 1);
        } else {
          
        }
      }
    }
    filled <- bytes_filled;
    filled <- (filled `>>` (W8.of_int 2));
    if ((filled \ult (W64.of_int 256))) {
      if ((xof_offset \ult (W64.of_int (2 * 136)))) {
        stop_sampling <- (W64.of_int 0);
      } else {
        
      }
    } else {
      
    }
    while ((stop_sampling <> (W64.of_int 1))) {
      coefficient <-
      (zeroextu32 (BArray272.get8 randombytes (W64.to_uint xof_offset)));
      coefficient <- (coefficient `&` (W32.of_int 15));
      if ((coefficient \ult (W32.of_int 9))) {
        coefficient <- (coefficient - (W32.of_int 4));
        coefficient <- (- coefficient);
        error <- (BArray1024.set32 error (W64.to_uint filled) coefficient);
        filled <- (filled + (W64.of_int 1));
      } else {
        
      }
      if ((filled \ult (W64.of_int 256))) {
        coefficient <-
        (zeroextu32 (BArray272.get8 randombytes (W64.to_uint xof_offset)));
        coefficient <- (coefficient `>>` (W8.of_int 4));
        if ((coefficient \ult (W32.of_int 9))) {
          coefficient <- (coefficient - (W32.of_int 4));
          coefficient <- (- coefficient);
          error <- (BArray1024.set32 error (W64.to_uint filled) coefficient);
          filled <- (filled + (W64.of_int 1));
        } else {
          
        }
      } else {
        
      }
      xof_offset <- (xof_offset + (W64.of_int 1));
      if (((W64.of_int (2 * 136)) \ule xof_offset)) {
        stop_sampling <- (W64.of_int 1);
      } else {
        if (((W64.of_int 256) \ule filled)) {
          stop_sampling <- (W64.of_int 1);
        } else {
          
        }
      }
    }
    return (error, filled);
  }
  proc error_4x__rejection_sample_one_block (error:BArray1024.t,
                                             filled:W64.t,
                                             randombytes:BArray136.t) : 
  BArray1024.t * W64.t = {
    var xof_offset:W64.t;
    var stop_sampling:W64.t;
    var coefficient:W32.t;
    xof_offset <- (W64.of_int 0);
    stop_sampling <- (W64.of_int 0);
    while ((stop_sampling <> (W64.of_int 1))) {
      coefficient <-
      (zeroextu32 (BArray136.get8 randombytes (W64.to_uint xof_offset)));
      coefficient <- (coefficient `&` (W32.of_int 15));
      if ((coefficient \ult (W32.of_int 9))) {
        coefficient <- (coefficient - (W32.of_int 4));
        coefficient <- (- coefficient);
        error <- (BArray1024.set32 error (W64.to_uint filled) coefficient);
        filled <- (filled + (W64.of_int 1));
      } else {
        
      }
      if ((filled \ult (W64.of_int 256))) {
        coefficient <-
        (zeroextu32 (BArray136.get8 randombytes (W64.to_uint xof_offset)));
        coefficient <- (coefficient `>>` (W8.of_int 4));
        if ((coefficient \ult (W32.of_int 9))) {
          coefficient <- (coefficient - (W32.of_int 4));
          coefficient <- (- coefficient);
          error <- (BArray1024.set32 error (W64.to_uint filled) coefficient);
          filled <- (filled + (W64.of_int 1));
        } else {
          
        }
      } else {
        
      }
      xof_offset <- (xof_offset + (W64.of_int 1));
      if (((W64.of_int 136) \ule xof_offset)) {
        stop_sampling <- (W64.of_int 1);
      } else {
        if (((W64.of_int 256) \ule filled)) {
          stop_sampling <- (W64.of_int 1);
        } else {
          
        }
      }
    }
    return (error, filled);
  }
  proc error_4x__shake256_init (state:BArray800.t, rho_prime:BArray64.t,
                                starting_domain_separator:W16.t) : BArray800.t = {
    var zeros:W256.t;
    var i:int;
    var t64:W64.t;
    var t256:W256.t;
    var lane:int;
    zeros <- (set0_256);
    i <- 0;
    while ((i < 25)) {
      state <- (BArray800.set256 state i zeros);
      i <- (i + 1);
    }
    i <- 0;
    while ((i < 8)) {
      t64 <- (BArray64.get64d rho_prime (8 * i));
      t256 <- (zeroextu256 t64);
      t256 <- (VPBROADCAST_4u64 (truncateu64 t256));
      state <- (BArray800.set256 state i t256);
      i <- (i + 1);
    }
    lane <- 0;
    while ((lane < 4)) {
      t64 <- (zeroextu64 starting_domain_separator);
      t64 <- (LEA_64 ((W64.of_int 2031616) + t64));
      t256 <- (zeroextu256 t64);
      t256 <- (VPBROADCAST_4u64 (truncateu64 t256));
      t256 <- (VPADD_4u64 t256 cONST_0123);
      state <- (BArray800.set256 state 8 t256);
      lane <- (lane + 1);
    }
    t64 <- (W64.of_int 9223372036854775808);
    t256 <- (zeroextu256 t64);
    t256 <- (VPBROADCAST_4u64 (truncateu64 t256));
    state <- (BArray800.set256 state 16 t256);
    return state;
  }
  proc error_4x____shake256_squeeze_multiple_blocks_4x (state:BArray800.t,
                                                        b0:BArray272.t,
                                                        b1:BArray272.t,
                                                        b2:BArray272.t,
                                                        b3:BArray272.t) : 
  BArray800.t * BArray272.t * BArray272.t * BArray272.t * BArray272.t = {
    var aux_0:BArray136.t;
    var aux_1:BArray136.t;
    var aux_2:BArray136.t;
    var aux_3:BArray136.t;
    var aux:BArray800.t;
    var i:int;
    i <- 0;
    while ((i < 2)) {
      (aux, aux_0, aux_1, aux_2, aux_3) <@ shake256_squeezeblock4x (state,
      (SBArray272_136.get_sub8 b0 (i * 136)),
      (SBArray272_136.get_sub8 b1 (i * 136)),
      (SBArray272_136.get_sub8 b2 (i * 136)),
      (SBArray272_136.get_sub8 b3 (i * 136)));
      state <- aux;
      b0 <- (SBArray272_136.set_sub8 b0 (i * 136) aux_0);
      b1 <- (SBArray272_136.set_sub8 b1 (i * 136) aux_1);
      b2 <- (SBArray272_136.set_sub8 b2 (i * 136) aux_2);
      b3 <- (SBArray272_136.set_sub8 b3 (i * 136) aux_3);
      i <- (i + 1);
    }
    return (state, b0, b1, b2, b3);
  }
  proc error_4x____sample_polynomials (rho_prime:BArray64.t,
                                       starting_domain_separator:W16.t) : 
  BArray1024.t * BArray1024.t * BArray1024.t * BArray1024.t = {
    var aux_0:BArray136.t;
    var aux_1:BArray136.t;
    var aux_2:BArray136.t;
    var aux_3:BArray136.t;
    var aux:BArray800.t;
    var polynomial0:BArray1024.t;
    var polynomial1:BArray1024.t;
    var polynomial2:BArray1024.t;
    var polynomial3:BArray1024.t;
    var xof_state:BArray800.t;
    var buf0:BArray272.t;
    var buf1:BArray272.t;
    var buf2:BArray272.t;
    var buf3:BArray272.t;
    var filled:W64.t;
    var filled0:W64.t;
    var filled1:W64.t;
    var filled2:W64.t;
    var filled3:W64.t;
    var stop_sampling:W64.t;
    buf0 <- witness;
    buf1 <- witness;
    buf2 <- witness;
    buf3 <- witness;
    polynomial0 <- witness;
    polynomial1 <- witness;
    polynomial2 <- witness;
    polynomial3 <- witness;
    xof_state <- witness;
    xof_state <@ error_4x__shake256_init (xof_state, rho_prime,
    starting_domain_separator);
    (xof_state, buf0, buf1, buf2, buf3) <@ error_4x____shake256_squeeze_multiple_blocks_4x (
    xof_state, buf0, buf1, buf2, buf3);
    (polynomial0, filled) <@ error_4x__rejection_sample_multiple_blocks (
    polynomial0, buf0);
    filled0 <- filled;
    (polynomial1, filled) <@ error_4x__rejection_sample_multiple_blocks (
    polynomial1, buf1);
    filled1 <- filled;
    (polynomial2, filled) <@ error_4x__rejection_sample_multiple_blocks (
    polynomial2, buf2);
    filled2 <- filled;
    (polynomial3, filled) <@ error_4x__rejection_sample_multiple_blocks (
    polynomial3, buf3);
    filled3 <- filled;
    stop_sampling <- (W64.of_int 1);
    if ((filled0 \ult (W64.of_int 256))) {
      stop_sampling <- (W64.of_int 0);
    } else {
      if ((filled1 \ult (W64.of_int 256))) {
        stop_sampling <- (W64.of_int 0);
      } else {
        if ((filled2 \ult (W64.of_int 256))) {
          stop_sampling <- (W64.of_int 0);
        } else {
          if ((filled3 \ult (W64.of_int 256))) {
            stop_sampling <- (W64.of_int 0);
          } else {
            
          }
        }
      }
    }
    while ((stop_sampling <> (W64.of_int 1))) {
      (aux, aux_0, aux_1, aux_2, aux_3) <@ shake256_squeezeblock4x (xof_state,
      (SBArray272_136.get_sub8 buf0 0), (SBArray272_136.get_sub8 buf1 0),
      (SBArray272_136.get_sub8 buf2 0), (SBArray272_136.get_sub8 buf3 0));
      xof_state <- aux;
      buf0 <- (SBArray272_136.set_sub8 buf0 0 aux_0);
      buf1 <- (SBArray272_136.set_sub8 buf1 0 aux_1);
      buf2 <- (SBArray272_136.set_sub8 buf2 0 aux_2);
      buf3 <- (SBArray272_136.set_sub8 buf3 0 aux_3);
      if ((filled0 \ult (W64.of_int 256))) {
        filled <- filled0;
        (polynomial0, filled) <@ error_4x__rejection_sample_one_block (
        polynomial0, filled, (SBArray272_136.get_sub8 buf0 0));
        filled0 <- filled;
      } else {
        
      }
      if ((filled1 \ult (W64.of_int 256))) {
        filled <- filled1;
        (polynomial1, filled) <@ error_4x__rejection_sample_one_block (
        polynomial1, filled, (SBArray272_136.get_sub8 buf1 0));
        filled1 <- filled;
      } else {
        
      }
      if ((filled2 \ult (W64.of_int 256))) {
        filled <- filled2;
        (polynomial2, filled) <@ error_4x__rejection_sample_one_block (
        polynomial2, filled, (SBArray272_136.get_sub8 buf2 0));
        filled2 <- filled;
      } else {
        
      }
      if ((filled3 \ult (W64.of_int 256))) {
        filled <- filled3;
        (polynomial3, filled) <@ error_4x__rejection_sample_one_block (
        polynomial3, filled, (SBArray272_136.get_sub8 buf3 0));
        filled3 <- filled;
      } else {
        
      }
      stop_sampling <- (W64.of_int 1);
      if ((filled0 \ult (W64.of_int 256))) {
        stop_sampling <- (W64.of_int 0);
      } else {
        if ((filled1 \ult (W64.of_int 256))) {
          stop_sampling <- (W64.of_int 0);
        } else {
          if ((filled2 \ult (W64.of_int 256))) {
            stop_sampling <- (W64.of_int 0);
          } else {
            if ((filled3 \ult (W64.of_int 256))) {
              stop_sampling <- (W64.of_int 0);
            } else {
              
            }
          }
        }
      }
    }
    return (polynomial0, polynomial1, polynomial2, polynomial3);
  }
  proc sample____error_vectors (rho_prime:BArray64.t) : BArray5120.t *
                                                        BArray6144.t = {
    var aux:BArray1024.t;
    var aux_0:BArray1024.t;
    var aux_1:BArray1024.t;
    var aux_2:BArray1024.t;
    var s1:BArray5120.t;
    var s2:BArray6144.t;
    var  _0:BArray1024.t;
     _0 <- witness;
    s1 <- witness;
    s2 <- witness;
    (aux, aux_0, aux_1, aux_2) <@ error_4x____sample_polynomials (rho_prime,
    (W16.of_int 0));
    s1 <- (SBArray5120_1024.set_sub32 s1 (256 * 0) aux);
    s1 <- (SBArray5120_1024.set_sub32 s1 (256 * 1) aux_0);
    s1 <- (SBArray5120_1024.set_sub32 s1 (256 * 2) aux_1);
    s1 <- (SBArray5120_1024.set_sub32 s1 (256 * 3) aux_2);
    (aux, aux_0, aux_1, aux_2) <@ error_4x____sample_polynomials (rho_prime,
    (W16.of_int 4));
    s1 <- (SBArray5120_1024.set_sub32 s1 (256 * 4) aux);
    s2 <- (SBArray6144_1024.set_sub32 s2 (256 * 0) aux_0);
    s2 <- (SBArray6144_1024.set_sub32 s2 (256 * 1) aux_1);
    s2 <- (SBArray6144_1024.set_sub32 s2 (256 * 2) aux_2);
    (aux, aux_0, aux_1, aux_2) <@ error_4x____sample_polynomials (rho_prime,
    (W16.of_int 8));
    s2 <- (SBArray6144_1024.set_sub32 s2 (256 * 3) aux);
    s2 <- (SBArray6144_1024.set_sub32 s2 (256 * 4) aux_0);
    s2 <- (SBArray6144_1024.set_sub32 s2 (256 * 5) aux_1);
     _0 <- aux_2;
    return (s1, s2);
  }
  proc sample____matrix_A (rho:BArray32.t) : BArray30720.t = {
    var aux:BArray1024.t;
    var aux_0:BArray1024.t;
    var aux_1:BArray1024.t;
    var aux_2:BArray1024.t;
    var inc:int;
    var matrix_A:BArray30720.t;
    var chunk:int;
    var index:int;
    var lane:int;
    var row:int;
    var column:int;
    var domain_separators:BArray8.t;
    var  _0:BArray1024.t;
    var  _1:BArray1024.t;
     _0 <- witness;
     _1 <- witness;
    domain_separators <- witness;
    matrix_A <- witness;
    inc <- ((6 * 5) %/ 4);
    chunk <- 0;
    while ((chunk < inc)) {
      index <- (4 * chunk);
      lane <- 0;
      while ((lane < 4)) {
        row <- ((index + lane) %/ 5);
        column <- ((index + lane) %% 5);
        domain_separators <-
        (BArray8.set16 domain_separators lane
        (truncateu16 ((W256.of_int (row `<<` 8)) `|` (W256.of_int column))));
        lane <- (lane + 1);
      }
      (aux, aux_0, aux_1, aux_2) <@ matrix_A____sample_4_polynomials (
      rho, domain_separators);
      matrix_A <-
      (SBArray30720_1024.set_sub32 matrix_A ((index + 0) * 256) aux);
      matrix_A <-
      (SBArray30720_1024.set_sub32 matrix_A ((index + 1) * 256) aux_0);
      matrix_A <-
      (SBArray30720_1024.set_sub32 matrix_A ((index + 2) * 256) aux_1);
      matrix_A <-
      (SBArray30720_1024.set_sub32 matrix_A ((index + 3) * 256) aux_2);
      chunk <- (chunk + 1);
    }
    index <- 28;
    lane <- 0;
    while ((lane < 2)) {
      row <- ((index + lane) %/ 5);
      column <- ((index + lane) %% 5);
      domain_separators <-
      (BArray8.set16 domain_separators lane
      (truncateu16 ((W256.of_int (row `<<` 8)) `|` (W256.of_int column))));
      lane <- (lane + 1);
    }
    (aux, aux_0, aux_1, aux_2) <@ matrix_A____sample_4_polynomials (rho,
    domain_separators);
    matrix_A <-
    (SBArray30720_1024.set_sub32 matrix_A ((index + 0) * 256) aux);
    matrix_A <-
    (SBArray30720_1024.set_sub32 matrix_A ((index + 1) * 256) aux_0);
     _0 <- aux_1;
     _1 <- aux_2;
    return matrix_A;
  }
  proc __initialize_xof (randomness:BArray32.t, number_of_rows:W8.t,
                         number_of_columns:W8.t) : BArray224.t = {
    var state:BArray224.t;
    var zero_256:W256.t;
    var copied_32_bytes:W256.t;
    var initial_block:BArray136.t;
    initial_block <- witness;
    state <- witness;
    zero_256 <- (set0_256);
    copied_32_bytes <- (BArray32.get256d randomness 0);
    initial_block <- (BArray136.set256d initial_block 0 copied_32_bytes);
    initial_block <- (BArray136.set8d initial_block 32 number_of_rows);
    initial_block <- (BArray136.set8d initial_block 33 number_of_columns);
    initial_block <- (BArray136.set8d initial_block 34 (W8.of_int 31));
    initial_block <- (BArray136.set256d initial_block 35 zero_256);
    initial_block <- (BArray136.set256d initial_block 67 zero_256);
    initial_block <- (BArray136.set256d initial_block 99 zero_256);
    initial_block <- (BArray136.set32d initial_block 131 (W32.of_int 0));
    initial_block <-
    (BArray136.set8d initial_block (136 - 1) (W8.of_int 128));
    state <@ __state_init_avx2 ();
    state <@ shake256_absorb_block (state, initial_block);
    return state;
  }
  proc squeeze_128_bytes (array:BArray128.t, state:BArray224.t) : BArray128.t = {
    var t128_0:W128.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_3:W256.t;
    var t128_1:W128.t;
    var t256_4:W256.t;
    t128_0 <- (truncateu128 (BArray224.get256 state 0));
    array <- (BArray128.set64d array 0 (truncateu64 t128_0));
    array <- (BArray128.set256d array 8 (BArray224.get256 state 1));
    t256_0 <-
    (VPBLEND_8u32 (BArray224.get256 state 3) (BArray224.get256 state 4)
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_1 <-
    (VPBLEND_8u32 (BArray224.get256 state 4) (BArray224.get256 state 3)
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t256_3 <-
    (VPBLEND_8u32 (BArray224.get256 state 6) (BArray224.get256 state 5)
    (W8.of_int
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    t128_1 <- (VEXTRACTI128 (BArray224.get256 state 2) (W8.of_int 1));
    array <- (BArray128.set64d array 40 (truncateu64 t128_1));
    t256_4 <-
    (VPBLEND_8u32 t256_0 t256_3
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    array <- (BArray128.set256d array 48 t256_4);
    t128_0 <- (truncateu128 (BArray224.get256 state 2));
    array <- (BArray128.set64d array 80 (truncateu64 t128_0));
    t256_4 <-
    (VPBLEND_8u32 t256_3 t256_1
    (W8.of_int
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((1 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) +
    ((2 ^ 1) *
    ((0 %% (2 ^ 1)) + ((2 ^ 1) * ((1 %% (2 ^ 1)) + ((2 ^ 1) * 1))))))))))))))
    ));
    array <- (BArray128.set256d array 88 t256_4);
    array <- (BArray128.set64d array 120 (VPEXTR_64 t128_1 (W8.of_int 1)));
    return array;
  }
  proc __keygen_internal (verification_key:BArray1952.t,
                          signing_key:BArray4032.t, randomness:BArray32.t) : 
  BArray1952.t * BArray4032.t = {
    var aux_1:BArray1920.t;
    var aux_2:BArray2496.t;
    var aux:BArray640.t;
    var aux_0:BArray768.t;
    var state:BArray224.t;
    var prf_output:BArray128.t;
    var seed_for_matrix_A:BArray32.t;
    var matrix_A:BArray30720.t;
    var seed_for_error_vectors:BArray64.t;
    var seed_for_signing:BArray32.t;
    var s1:BArray5120.t;
    var s2:BArray6144.t;
    var copied_32_bytes:W256.t;
    var t:BArray6144.t;
    var t1:BArray6144.t;
    var t0:BArray6144.t;
    var verification_key_pointer_copy:BArray1952.t;
    var verification_key_hash:BArray64.t;
    matrix_A <- witness;
    prf_output <- witness;
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
    state <@ __initialize_xof (randomness, (W8.of_int 6), (W8.of_int 5));
    prf_output <@ squeeze_128_bytes (prf_output, state);
    seed_for_matrix_A <- (SBArray128_32.get_sub8 prf_output 0);
    matrix_A <@ sample____matrix_A (seed_for_matrix_A);
    seed_for_error_vectors <- (SBArray128_64.get_sub8 prf_output 32);
    seed_for_signing <- (SBArray128_32.get_sub8 prf_output (32 + 64));
    (s1, s2) <@ sample____error_vectors (seed_for_error_vectors);
    (* Erased call to unspill *)
    copied_32_bytes <- (BArray32.get256d seed_for_matrix_A 0);
    signing_key <- (BArray4032.set256d signing_key 0 copied_32_bytes);
    verification_key <-
    (BArray1952.set256d verification_key 0 copied_32_bytes);
    copied_32_bytes <- (BArray32.get256d seed_for_signing 0);
    signing_key <- (BArray4032.set256d signing_key 32 copied_32_bytes);
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
    t <@ row_vector____multiply_with_matrix_A (matrix_A, s1);
    t <@ column_vector__reduce32 (t);
    t <@ column_vector__invert_ntt_montgomery (t);
    t <@ column_vector____add (t, s2);
    t <@ column_vector____conditionally_add_modulus (t);
    (t1, t0) <@ column_vector____power2round (t);
    aux_1 <@ t1____encode ((SBArray1952_1920.get_sub8 verification_key 32),
    t1);
    verification_key <-
    (SBArray1952_1920.set_sub8 verification_key 32 aux_1);
    verification_key <- verification_key;
    verification_key_pointer_copy <- verification_key;
    verification_key_hash <- (SBArray4032_64.get_sub8 signing_key 64);
    verification_key_hash <@ hash_verification_key (verification_key_hash,
    verification_key_pointer_copy);
    signing_key <-
    (SBArray4032_64.set_sub8 signing_key 64 verification_key_hash);
    aux_2 <@ t0____encode ((SBArray4032_2496.get_sub8 signing_key
                           ((((32 + 32) + 64) + (5 * 128)) + (6 * 128))),
    t0);
    signing_key <-
    (SBArray4032_2496.set_sub8 signing_key
    ((((32 + 32) + 64) + (5 * 128)) + (6 * 128)) aux_2);
    return (verification_key, signing_key);
  }
  proc sample____mask (rho_prime:BArray64.t, domain_separator:W16.t) : 
  BArray5120.t * W16.t = {
    var aux:BArray1024.t;
    var aux_0:BArray1024.t;
    var aux_1:BArray1024.t;
    var aux_2:BArray1024.t;
    var mask:BArray5120.t;
    mask <- witness;
    (aux, aux_0, aux_1, aux_2) <@ __sample_mask_polynomial_4x (rho_prime,
    domain_separator);
    mask <- (SBArray5120_1024.set_sub32 mask (256 * 0) aux);
    mask <- (SBArray5120_1024.set_sub32 mask (256 * 1) aux_0);
    mask <- (SBArray5120_1024.set_sub32 mask (256 * 2) aux_1);
    mask <- (SBArray5120_1024.set_sub32 mask (256 * 3) aux_2);
    domain_separator <- (domain_separator + (W16.of_int 4));
    aux <@ __sample_mask_polynomial_1x ((SBArray5120_1024.get_sub32 mask
                                        ((256 * 32) %/ 8)),
    rho_prime, domain_separator);
    mask <- (SBArray5120_1024.set_sub32 mask ((256 * 32) %/ 8) aux);
    domain_separator <- (domain_separator + (W16.of_int 1));
    return (mask, domain_separator);
  }
  proc commitment____encode_polynomial (encoded:BArray128.t,
                                        commitment:BArray1024.t) : BArray128.t = {
    var temp:W64.t;
    var shift:W256.t;
    var encoding_shuffles:W256.t;
    var input_offset:W64.t;
    var output_offset:W64.t;
    var c0:W256.t;
    var c1:W256.t;
    var c2:W256.t;
    var c3:W256.t;
    var c4:W256.t;
    var c5:W256.t;
    var c6:W256.t;
    var c7:W256.t;
    temp <- (W64.of_int ((16 `<<` 8) + 1));
    shift <- (zeroextu256 (VMOV_64 temp));
    shift <- (VPBROADCAST_16u16 (truncateu16 shift));
    encoding_shuffles <- commitment__ENCODING_SHUFFLES;
    input_offset <- (W64.of_int 0);
    output_offset <- (W64.of_int 0);
    while ((input_offset \ult (W64.of_int ((256 * 32) %/ 8)))) {
      c0 <- (BArray1024.get256d commitment (W64.to_uint input_offset));
      input_offset <- (input_offset + (W64.of_int 32));
      c1 <- (BArray1024.get256d commitment (W64.to_uint input_offset));
      input_offset <- (input_offset + (W64.of_int 32));
      c2 <- (BArray1024.get256d commitment (W64.to_uint input_offset));
      input_offset <- (input_offset + (W64.of_int 32));
      c3 <- (BArray1024.get256d commitment (W64.to_uint input_offset));
      input_offset <- (input_offset + (W64.of_int 32));
      c4 <- (BArray1024.get256d commitment (W64.to_uint input_offset));
      input_offset <- (input_offset + (W64.of_int 32));
      c5 <- (BArray1024.get256d commitment (W64.to_uint input_offset));
      input_offset <- (input_offset + (W64.of_int 32));
      c6 <- (BArray1024.get256d commitment (W64.to_uint input_offset));
      input_offset <- (input_offset + (W64.of_int 32));
      c7 <- (BArray1024.get256d commitment (W64.to_uint input_offset));
      input_offset <- (input_offset + (W64.of_int 32));
      c0 <- (VPACKUS_8u32 c0 c1);
      c1 <- (VPACKUS_8u32 c2 c3);
      c2 <- (VPACKUS_8u32 c4 c5);
      c3 <- (VPACKUS_8u32 c6 c7);
      c0 <- (VPACKUS_16u16 c0 c1);
      c1 <- (VPACKUS_16u16 c2 c3);
      c0 <- (VPMADDUBSW_256 c0 shift);
      c1 <- (VPMADDUBSW_256 c1 shift);
      c0 <- (VPACKUS_16u16 c0 c1);
      c0 <- (VPERMQ c0 (W8.of_int 216));
      c0 <- (VPSHUFB_256 c0 encoding_shuffles);
      encoded <- (BArray128.set256d encoded (W64.to_uint output_offset) c0);
      output_offset <- (output_offset + (W64.of_int 32));
    }
    return encoded;
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
    var copied_32_bytes:W256.t;
    var block:BArray136.t;
    var state:BArray224.t;
    block <- witness;
    state <- witness;
    copied_32_bytes <- (BArray32.get256d k 0);
    block <- (BArray136.set256d block 0 copied_32_bytes);
    copied_32_bytes <- (BArray32.get256d randomness 0);
    block <- (BArray136.set256d block 32 copied_32_bytes);
    copied_32_bytes <- (BArray64.get256d message_representative 0);
    block <- (BArray136.set256d block 64 copied_32_bytes);
    copied_32_bytes <- (BArray64.get256d message_representative 32);
    block <- (BArray136.set256d block 96 copied_32_bytes);
    block <- (BArray136.set64d block 128 (W64.of_int 0));
    block <- (BArray136.set8d block 128 (W8.of_int 31));
    block <- (BArray136.set8d block (136 - 1) (W8.of_int 128));
    state <@ __state_init_avx2 ();
    state <@ shake256_absorb_block (state, block);
    seed_for_mask <@ squeeze_64_bytes (seed_for_mask, state);
    return seed_for_mask;
  }
  proc __compute_signer_response_element (s1_element:BArray1024.t,
                                          verifier_challenge:BArray1024.t,
                                          mask_element:BArray1024.t,
                                          signer_response_element:BArray1024.t) : 
  BArray1024.t = {
    var cs1:BArray1024.t;
    cs1 <- witness;
    cs1 <@ polynomial__pointwise_montgomery_multiply_and_reduce (cs1,
    s1_element, verifier_challenge);
    cs1 <@ polynomial__invert_ntt_montgomery (cs1);
    signer_response_element <@ polynomial__add (signer_response_element, 
    cs1, mask_element);
    signer_response_element <@ polynomial__reduce32 (signer_response_element);
    return signer_response_element;
  }
  proc __sign_internal (signature:BArray3309.t, signing_key:BArray4032.t,
                        context_message_pointers:BArray16.t,
                        context_message_sizes:BArray16.t,
                        randomness:BArray32.t) : BArray3309.t = {
    var aux:BArray1024.t;
    var seed_for_matrix_A:BArray32.t;
    var matrix_A:BArray30720.t;
    var message_representative:BArray64.t;
    var seed_for_mask:BArray64.t;
    var s1:BArray5120.t;
    var s2:BArray6144.t;
    var t0:BArray6144.t;
    var domain_separator_for_mask:W16.t;
    var exit_rejection_sampling_loop:W8.t;
    var mask:BArray5120.t;
    var j:W64.t;
    var copied_32_bytes:W256.t;
    var mask_as_ntt:BArray5120.t;
    var w:BArray6144.t;
    var w0:BArray6144.t;
    var w1:BArray6144.t;
    var commitment_encoded:BArray768.t;
    var commitment_hash:BArray48.t;
    var verifier_challenge:BArray1024.t;
    var infinity_norm_check_result:W8.t;
    var i:int;
    var signer_response:BArray5120.t;
    var total_ones_in_hint:W64.t;
    var hint_elements_processed:W64.t;
    var s2_element:BArray1024.t;
    var cs2:BArray1024.t;
    var w0_minus_cs2:BArray1024.t;
    var t0_element:BArray1024.t;
    var ct0:BArray1024.t;
    var w0_minus_cs2_plus_ct0:BArray1024.t;
    var hint_0:BArray6144.t;
    var hint_element:BArray1024.t;
    var ones_in_hint:W64.t;
    commitment_encoded <- witness;
    commitment_hash <- witness;
    cs2 <- witness;
    ct0 <- witness;
    hint_0 <- witness;
    hint_element <- witness;
    mask <- witness;
    mask_as_ntt <- witness;
    matrix_A <- witness;
    message_representative <- witness;
    s1 <- witness;
    s2 <- witness;
    s2_element <- witness;
    seed_for_mask <- witness;
    seed_for_matrix_A <- witness;
    signer_response <- witness;
    t0 <- witness;
    t0_element <- witness;
    verifier_challenge <- witness;
    w <- witness;
    w0 <- witness;
    w0_minus_cs2 <- witness;
    w0_minus_cs2_plus_ct0 <- witness;
    w1 <- witness;
    (* Erased call to spill *)
    seed_for_matrix_A <- (SBArray4032_32.get_sub8 signing_key 0);
    matrix_A <@ sample____matrix_A (seed_for_matrix_A);
    (* Erased call to unspill *)
    message_representative <@ __derive_message_representative ((
                                                               SBArray4032_64.get_sub8
                                                               signing_key 64
                                                               ),
    context_message_pointers, context_message_sizes);
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
    t0 <@ t0__decode (t0,
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
      j <- (W64.of_int 0);
      while ((j \ult (W64.of_int (5 * ((256 * 32) %/ 8))))) {
        copied_32_bytes <- (BArray5120.get256d mask (W64.to_uint j));
        mask_as_ntt <-
        (BArray5120.set256d mask_as_ntt (W64.to_uint j) copied_32_bytes);
        j <- (j + (W64.of_int 32));
      }
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
      infinity_norm_check_result <- (W8.of_int 0);
      i <- 0;
      while ((i < 5)) {
        infinity_norm_check_result <- infinity_norm_check_result;
        if ((infinity_norm_check_result = (W8.of_int 0))) {
          aux <@ __compute_signer_response_element ((
                                                    SBArray5120_1024.get_sub32
                                                    s1 (i * 256)),
          verifier_challenge, (SBArray5120_1024.get_sub32 mask (i * 256)),
          (SBArray5120_1024.get_sub32 signer_response (i * 256)));
          signer_response <-
          (SBArray5120_1024.set_sub32 signer_response (i * 256) aux);
          infinity_norm_check_result <@ polynomial____check_infinity_norm (
          (SBArray5120_1024.get_sub32 signer_response (i * 256)),
          ((1 `<<` 19) - (49 * 4)));
        } else {
          
        }
        i <- (i + 1);
      }
      total_ones_in_hint <- (W64.of_int 0);
      hint_elements_processed <- (W64.of_int 0);
      i <- 0;
      while ((i < 6)) {
        infinity_norm_check_result <- infinity_norm_check_result;
        if ((infinity_norm_check_result = (W8.of_int 0))) {
          s2_element <- (SBArray6144_1024.get_sub32 s2 (i * 256));
          cs2 <@ polynomial__pointwise_montgomery_multiply_and_reduce (
          cs2, s2_element, verifier_challenge);
          cs2 <@ polynomial__invert_ntt_montgomery (cs2);
          w0_minus_cs2 <@ polynomial__subtract (w0_minus_cs2,
          (SBArray6144_1024.get_sub32 w0 (i * 256)), cs2);
          w0_minus_cs2 <@ polynomial__reduce32 (w0_minus_cs2);
          infinity_norm_check_result <@ polynomial____check_infinity_norm (
          w0_minus_cs2, (((8380417 - 1) %/ 32) - (49 * 4)));
          infinity_norm_check_result <- infinity_norm_check_result;
          if ((infinity_norm_check_result = (W8.of_int 0))) {
            t0_element <- (SBArray6144_1024.get_sub32 t0 (i * 256));
            ct0 <@ polynomial__pointwise_montgomery_multiply_and_reduce (
            ct0, t0_element, verifier_challenge);
            ct0 <@ polynomial__invert_ntt_montgomery (ct0);
            ct0 <@ polynomial__reduce32 (ct0);
            infinity_norm_check_result <@ polynomial____check_infinity_norm (
            ct0, ((8380417 - 1) %/ 32));
            infinity_norm_check_result <- infinity_norm_check_result;
            if ((infinity_norm_check_result = (W8.of_int 0))) {
              total_ones_in_hint <- total_ones_in_hint;
              if ((total_ones_in_hint \ule (W64.of_int 55))) {
                w0_minus_cs2_plus_ct0 <@ polynomial__add (w0_minus_cs2_plus_ct0,
                w0_minus_cs2, ct0);
                hint_element <-
                (SBArray6144_1024.get_sub32 hint_0 (i * 256));
                (hint_element, ones_in_hint) <@ polynomial____make_hint (
                hint_element, w0_minus_cs2_plus_ct0,
                (SBArray6144_1024.get_sub32 w1 (i * 256)));
                hint_0 <-
                (SBArray6144_1024.set_sub32 hint_0 (i * 256) hint_element);
                total_ones_in_hint <- (total_ones_in_hint + ones_in_hint);
                hint_elements_processed <-
                (hint_elements_processed + (W64.of_int 1));
              } else {
                
              }
            } else {
              
            }
          } else {
            
          }
        } else {
          
        }
        i <- (i + 1);
      }
      if ((hint_elements_processed = (W64.of_int 6))) {
        if ((total_ones_in_hint \ule (W64.of_int 55))) {
          exit_rejection_sampling_loop <- (W8.of_int 1);
        } else {
          exit_rejection_sampling_loop <- (W8.of_int 0);
        }
      } else {
        exit_rejection_sampling_loop <- (W8.of_int 0);
      }
    }
    (* Erased call to unspill *)
    hint_0 <- hint_0;
    commitment_hash <- commitment_hash;
    signer_response <- signer_response;
    signature <@ signature____encode (signature, commitment_hash,
    signer_response, hint_0);
    return signature;
  }
  proc __compare_commitment_hashes (lhs:BArray48.t, rhs:BArray48.t) : W64.t = {
    var result:W64.t;
    var offset:W64.t;
    var lhs_bytes:W128.t;
    var rhs_bytes:W128.t;
    var result_vec:W128.t;
    var temp:W128.t;
    offset <- (W64.of_int 0);
    lhs_bytes <- (BArray48.get128d lhs (W64.to_uint offset));
    rhs_bytes <- (BArray48.get128d rhs (W64.to_uint offset));
    result_vec <- (VPCMPEQ_16u8 lhs_bytes rhs_bytes);
    offset <- (offset + (W64.of_int 16));
    while ((offset \ult (W64.of_int 48))) {
      lhs_bytes <- (BArray48.get128d lhs (W64.to_uint offset));
      rhs_bytes <- (BArray48.get128d rhs (W64.to_uint offset));
      temp <- (VPCMPEQ_16u8 lhs_bytes rhs_bytes);
      result_vec <- (VPAND_128 result_vec temp);
      offset <- (offset + (W64.of_int 16));
    }
    result <- (zeroextu64 (MOVEMASK_16u8 result_vec));
    result <- result;
    if ((result = (W64.of_int 65535))) {
      result <- (W64.of_int 0);
    } else {
      result <- (W64.of_int (- 1));
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
    var hints_element:BArray1024.t;
    az_element <- witness;
    c_times_t1 <- witness;
    commitment <- witness;
    commitment_element <- witness;
    commitment_encoded <- witness;
    hints_element <- witness;
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
      c_times_t1 <@ polynomial__pointwise_montgomery_multiply_and_reduce (
      c_times_t1, challenge_as_ntt, t1_element);
      commitment_element <-
      (SBArray6144_1024.get_sub32 commitment (i * 256));
      commitment_element <@ polynomial__subtract (commitment_element,
      az_element, c_times_t1);
      commitment_element <@ polynomial__reduce32 (commitment_element);
      commitment_element <@ polynomial__invert_ntt_montgomery (commitment_element);
      commitment_element <@ polynomial__conditionally_add_modulus (commitment_element);
      hints_element <- (SBArray6144_1024.get_sub32 hints (i * 256));
      commitment_element <@ polynomial__use_hints (commitment_element,
      hints_element);
      commitment <-
      (SBArray6144_1024.set_sub32 commitment (i * 256) commitment_element);
      i <- (i + 1);
    }
    commitment_encoded <@ commitment____encode (commitment);
    return commitment_encoded;
  }
  proc __verify_internal (verification_key:BArray1952.t,
                          context_message_pointers:BArray16.t,
                          context_message_sizes:BArray16.t,
                          signature_encoded:BArray3309.t) : W64.t = {
    var result:W64.t;
    var signer_response:BArray5120.t;
    var hints:BArray6144.t;
    var matrix_A:BArray30720.t;
    var a_times_signer_response:BArray6144.t;
    var challenge:BArray1024.t;
    var reconstructed_signer_commitment:BArray768.t;
    var verification_key_hash:BArray64.t;
    var message_representative:BArray64.t;
    var expected_commitment_hash:BArray48.t;
    a_times_signer_response <- witness;
    challenge <- witness;
    expected_commitment_hash <- witness;
    hints <- witness;
    matrix_A <- witness;
    message_representative <- witness;
    reconstructed_signer_commitment <- witness;
    signer_response <- witness;
    verification_key_hash <- witness;
    signer_response <@ gamma1____decode (signer_response,
    (SBArray3309_3200.get_sub8 signature_encoded 48));
    (hints, result) <@ signature____decode_hint (hints,
    (SBArray3309_61.get_sub8 signature_encoded (48 + (5 * ((20 * 256) %/ 8)))
    ));
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
      verification_key_hash <@ hash_verification_key (verification_key_hash,
      verification_key);
      (* Erased call to unspill *)
      message_representative <@ __derive_message_representative (verification_key_hash,
      context_message_pointers, context_message_sizes);
      expected_commitment_hash <@ __derive_commitment_hash (message_representative,
      reconstructed_signer_commitment);
      (* Erased call to unspill *)
      result <@ __compare_commitment_hashes (expected_commitment_hash,
      (SBArray3309_48.get_sub8 signature_encoded 0));
    } else {
      
    }
    return result;
  }
  proc ml_dsa_65_keygen (verification_key:BArray1952.t,
                         signing_key:BArray4032.t, randomness:BArray32.t) : 
  BArray1952.t * BArray4032.t = {
    
    (* Erased call to spill *)
    (verification_key, signing_key) <@ __keygen_internal (verification_key,
    signing_key, randomness);
    return (verification_key, signing_key);
  }
  proc ml_dsa_65_sign (signature:BArray3309.t, signing_key:BArray4032.t,
                       context_message_pointers:BArray16.t,
                       context_message_sizes:BArray16.t,
                       randomness:BArray32.t) : BArray3309.t * W64.t = {
    var result:W64.t;
    var context_size:W64.t;
    context_size <- (BArray16.get64 context_message_sizes 0);
    if ((context_size \ule (W64.of_int 255))) {
      signature <@ __sign_internal (signature, signing_key,
      context_message_pointers, context_message_sizes, randomness);
      result <- (W64.of_int 0);
    } else {
      result <- (W64.of_int (- 1));
    }
    return (signature, result);
  }
  proc ml_dsa_65_verify (verification_key:BArray1952.t,
                         context_message_pointers:BArray16.t,
                         context_message_sizes:BArray16.t,
                         signature:BArray3309.t) : W64.t = {
    var verification_result:W64.t;
    var context_size:W64.t;
    context_size <- (BArray16.get64 context_message_sizes 0);
    if ((context_size \ule (W64.of_int 255))) {
      verification_result <@ __verify_internal (verification_key,
      context_message_pointers, context_message_sizes, signature);
    } else {
      verification_result <- (W64.of_int (- 1));
    }
    return verification_result;
  }
}.
