from Jasmin require import JWord JWord_array.

require import ArrayWords416W8.

clone export ArrayAccessCast as ArrayAccessCastW128_416W8  with op sizeWS <- 16,
                                                                op sizeWB <- 1,
                                                                op sizeB <- 416,
                                                                theory WordS <- W128,
                                                                theory WordB <- W8,
                                                                theory ArrayWordsB <= ArrayWords416W8.
