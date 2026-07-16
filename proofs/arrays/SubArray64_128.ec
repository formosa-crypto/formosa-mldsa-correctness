from Jasmin require import JArray.

require import Array64 Array128.

clone export SubArray as SubArray64_128  with op sizeS <- 64,
                                              op sizeB <- 128,
                                              theory ArrayS <= Array64,
                                              theory ArrayB <= Array128.
