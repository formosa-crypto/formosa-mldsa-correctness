from Jasmin require import JWord JWord_array.

require import ArrayWords2W8.

clone export ArrayAccessCast as ArrayAccessCastW32_2W8  with op sizeWS <- 4,
                                                             op sizeWB <- 1,
                                                             op sizeB <- 2,
                                                             theory WordS <- W32,
                                                             theory WordB <- W8,
                                                             theory ArrayWordsB <= ArrayWords2W8.
