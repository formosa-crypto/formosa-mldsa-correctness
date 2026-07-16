from Jasmin require import JArray.

require import Array32 Array4032.

clone export SubArray as SubArray32_4032  with op sizeS <- 32,
                                               op sizeB <- 4032,
                                               theory ArrayS <= Array32,
                                               theory ArrayB <= Array4032.
