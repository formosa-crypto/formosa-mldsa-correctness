from Jasmin require import JWord JWord_array.

require import Array4032 WArray4032.

clone export ArrayWords as ArrayWords4032W8  with op sizeW <- 1,
                                                  op sizeA <- 4032,
                                                  theory Word <= W8,
                                                  theory ArrayN <= Array4032,
                                                  theory WArrayN <= WArray4032.
