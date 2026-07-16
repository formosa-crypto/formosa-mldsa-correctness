from Jasmin require import JArray.

require import Array128 Array768.

clone export SubArray as SubArray128_768  with op sizeS <- 128,
                                               op sizeB <- 768,
                                               theory ArrayS <= Array128,
                                               theory ArrayB <= Array768.
