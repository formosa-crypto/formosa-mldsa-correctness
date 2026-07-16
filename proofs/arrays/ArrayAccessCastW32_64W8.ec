from Jasmin require import JWord JWord_array.

require import ArrayWords64W8.

clone export ArrayAccessCast as ArrayAccessCastW32_64W8  with op sizeWS <- 4,
                                                              op sizeWB <- 1,
                                                              op sizeB <- 64,
                                                              theory WordS <- W32,
                                                              theory WordB <- W8,
                                                              theory ArrayWordsB <= ArrayWords64W8.
