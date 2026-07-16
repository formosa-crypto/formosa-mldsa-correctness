from Jasmin require import JArray.

require import Array256 Array7680.

clone export SubArray as SubArray256_7680  with op sizeS <- 256,
                                                op sizeB <- 7680,
                                                theory ArrayS <= Array256,
                                                theory ArrayB <= Array7680.
