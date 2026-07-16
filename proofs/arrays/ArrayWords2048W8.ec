from Jasmin require import JWord JWord_array.

require import Array2048 WArray2048.

clone export ArrayWords as ArrayWords2048W8  with op sizeW <- 1,
                                                  op sizeA <- 2048,
                                                  theory Word <= W8,
                                                  theory ArrayN <= Array2048,
                                                  theory WArrayN <= WArray2048.
