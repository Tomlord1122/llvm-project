def VREVERSE_MTK : Instruction {
  bits<32> Inst;
  let Inst{6-0}   = 0b0101011;         // opcode (custom-1 space)
  let Inst{14-12} = 0b000;            // funct3 (choose an unused funct3)
  let Inst{31-25} = 0b1000010;        // funct7 (choose an unused pattern)
  bits<5> rd, rs1;
  bits<5> rs2 = 0b11111;             // use x31 (rs2=31 indicates no second source, a trick used in some custom encodings)
  let Inst{11-7}  = rd;
  let Inst{19-15} = rs1;
  let Inst{24-20} = rs2;
  let AsmString   = "vrev_mtk\t$rd, $rs1";
  let outs = (outs VR:$vd);          // output operand: vector dest
  let ins  = (ins VR:$vs1);
  let hasSideEffects = 0;
  let mayLoad = 0, mayStore = 0;
  // (Other flags like let Predicates = [HasRVV, HasExtVReverse] could be added to tie this to features)
}

// def : Pat
def : Pat < (VrevMTK VR:$vs1, $indices, $undef, $mask, $vl),
            (VREVERSE_MTK VR:$vs1) >;
