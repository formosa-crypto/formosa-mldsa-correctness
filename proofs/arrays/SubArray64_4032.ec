from Jasmin require import JArray.

require import Array64 Array4032.

clone export SubArray as SubArray64_4032  with op sizeS <- 64,
                                               op sizeB <- 4032,
                                               theory ArrayS <= Array64,
                                               theory ArrayB <= Array4032.
