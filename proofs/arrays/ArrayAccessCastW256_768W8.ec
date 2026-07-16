from Jasmin require import JWord JWord_array.

require import ArrayWords768W8.

clone export ArrayAccessCast as ArrayAccessCastW256_768W8  with op sizeWS <- 32,
                                                                op sizeWB <- 1,
                                                                op sizeB <- 768,
                                                                theory WordS <- W256,
                                                                theory WordB <- W8,
                                                                theory ArrayWordsB <= ArrayWords768W8.
