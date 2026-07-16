from Jasmin require import JWord JWord_array.

require import ArrayWords4032W8.

clone export ArrayAccessCast as ArrayAccessCastW256_4032W8  with op sizeWS <- 32,
                                                                 op sizeWB <- 1,
                                                                 op sizeB <- 4032,
                                                                 theory WordS <- W256,
                                                                 theory WordB <- W8,
                                                                 theory ArrayWordsB <= ArrayWords4032W8.
