from Jasmin require import JWord JWord_array.

require import ArrayWords256W32.

clone export ArrayAccessCast as ArrayAccessCastW256_256W32  with op sizeWS <- 32,
                                                                 op sizeWB <- 4,
                                                                 op sizeB <- 256,
                                                                 theory WordS <- W256,
                                                                 theory WordB <- W32,
                                                                 theory ArrayWordsB <= ArrayWords256W32.
