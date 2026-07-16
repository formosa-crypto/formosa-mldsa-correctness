from Jasmin require import JArray.

require import Array256 Array1280.

clone export SubArray as SubArray256_1280  with op sizeS <- 256,
                                                op sizeB <- 1280,
                                                theory ArrayS <= Array256,
                                                theory ArrayB <= Array1280.
