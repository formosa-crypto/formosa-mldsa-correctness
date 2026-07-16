from Jasmin require import JWord JWord_array.

require import ArrayWords32W8.

clone export ArrayAccessCast as ArrayAccessCastW32_32W8  with op sizeWS <- 4,
                                                              op sizeWB <- 1,
                                                              op sizeB <- 32,
                                                              theory WordS <- W32,
                                                              theory WordB <- W8,
                                                              theory ArrayWordsB <= ArrayWords32W8.
