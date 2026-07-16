from Jasmin require import JWord JWord_array.

require import Array64 WArray64.

clone export ArrayWords as ArrayWords64W8  with op sizeW <- 1,
                                                op sizeA <- 64,
                                                theory Word <= W8,
                                                theory ArrayN <= Array64,
                                                theory WArrayN <= WArray64.
