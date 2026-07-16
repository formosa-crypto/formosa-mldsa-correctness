from Jasmin require import JWord JWord_array.

require import Array256 WArray1024.

clone export ArrayWords as ArrayWords256W32  with op sizeW <- 4,
                                                  op sizeA <- 256,
                                                  theory Word <= W32,
                                                  theory ArrayN <= Array256,
                                                  theory WArrayN <= WArray1024.
