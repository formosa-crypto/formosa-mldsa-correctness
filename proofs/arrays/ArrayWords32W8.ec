from Jasmin require import JWord JWord_array.

require import Array32 WArray32.

clone export ArrayWords as ArrayWords32W8  with op sizeW <- 1,
                                                op sizeA <- 32,
                                                theory Word <= W8,
                                                theory ArrayN <= Array32,
                                                theory WArrayN <= WArray32.
