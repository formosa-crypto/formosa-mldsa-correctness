from Jasmin require import JWord JWord_array.

require import ArrayWords48W8.

clone export ArrayAccessCast as ArrayAccessCastW32_48W8  with op sizeWS <- 4,
                                                              op sizeWB <- 1,
                                                              op sizeB <- 48,
                                                              theory WordS <- W32,
                                                              theory WordB <- W8,
                                                              theory ArrayWordsB <= ArrayWords48W8.
