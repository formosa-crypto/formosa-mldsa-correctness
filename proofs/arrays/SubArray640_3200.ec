from Jasmin require import JArray.

require import Array640 Array3200.

clone export SubArray as SubArray640_3200  with op sizeS <- 640,
                                                op sizeB <- 3200,
                                                theory ArrayS <= Array640,
                                                theory ArrayB <= Array3200.
