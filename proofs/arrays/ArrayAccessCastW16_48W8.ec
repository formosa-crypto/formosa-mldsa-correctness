from Jasmin require import JWord JWord_array.

require import ArrayWords48W8.

clone export ArrayAccessCast as ArrayAccessCastW16_48W8  with op sizeWS <- 2,
                                                              op sizeWB <- 1,
                                                              op sizeB <- 48,
                                                              theory WordS <- W16,
                                                              theory WordB <- W8,
                                                              theory ArrayWordsB <= ArrayWords48W8.
