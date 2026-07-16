from Jasmin require import JArray.

require import Array32 Array128.

clone export SubArray as SubArray32_128  with op sizeS <- 32,
                                              op sizeB <- 128,
                                              theory ArrayS <= Array32,
                                              theory ArrayB <= Array128.
