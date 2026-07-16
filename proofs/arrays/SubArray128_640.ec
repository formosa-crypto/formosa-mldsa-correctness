from Jasmin require import JArray.

require import Array128 Array640.

clone export SubArray as SubArray128_640  with op sizeS <- 128,
                                               op sizeB <- 640,
                                               theory ArrayS <= Array128,
                                               theory ArrayB <= Array640.
