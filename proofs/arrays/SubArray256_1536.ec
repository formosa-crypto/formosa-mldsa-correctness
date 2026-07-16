from Jasmin require import JArray.

require import Array256 Array1536.

clone export SubArray as SubArray256_1536  with op sizeS <- 256,
                                                op sizeB <- 1536,
                                                theory ArrayS <= Array256,
                                                theory ArrayB <= Array1536.
