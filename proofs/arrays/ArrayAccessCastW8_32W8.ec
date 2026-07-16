from Jasmin require import JWord JWord_array.

require import ArrayWords32W8.

clone export ArrayAccessCast as ArrayAccessCastW8_32W8  with op sizeWS <- 1,
                                                             op sizeWB <- 1,
                                                             op sizeB <- 32,
                                                             theory WordS <- W8,
                                                             theory WordB <- W8,
                                                             theory ArrayWordsB <= ArrayWords32W8.
