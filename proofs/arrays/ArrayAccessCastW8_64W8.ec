from Jasmin require import JWord JWord_array.

require import ArrayWords64W8.

clone export ArrayAccessCast as ArrayAccessCastW8_64W8  with op sizeWS <- 1,
                                                             op sizeWB <- 1,
                                                             op sizeB <- 64,
                                                             theory WordS <- W8,
                                                             theory WordB <- W8,
                                                             theory ArrayWordsB <= ArrayWords64W8.
