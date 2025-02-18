////////////////defined in /llvm-project/llvm/lib/Target/RISCV/RISCVInstrInfo.td
// //define 9-bit signed-immediate
// def simm9 : RISCVSImmLeafOp<9>;
//===----------------------------------------------------------------------===//
// Instruction class templates
//===----------------------------------------------------------------------===//
class RVInstVLU_custom<bits<3> nf, bit mew,
                bits<3> width, dag outs, dag ins, string opcodestr,
                string argstr>
    : RVInst<outs, ins, opcodestr, argstr, [], InstFormatI> {
  bits<9> simm9;
  bits<5> rs1;
  bits<5> vd;
  bit vm;

  let Inst{31-29} = nf;
  let Inst{28} = mew;
  let Inst{27-20} = simm9{8-1};
  let Inst{19-15} = rs1;
  let Inst{14-12} = width;
  let Inst{11-7} = vd;
  let Inst{6} = 0b0;
  let Inst{5} = simm9{0}; //stole from the bit that is used to distinguish custom-0 and custom-1 
  let Inst{4-0} = 0b01011;

  let Uses = [VTYPE, VL];
  let RVVConstraint = VMConstraint;
}

class RVInstVSU_custom<bits<3> nf, bit mew,
                bits<3> width, dag outs, dag ins, string opcodestr,
                string argstr>
    : RVInst<outs, ins, opcodestr, argstr, [], InstFormatI> {
  bits<9> simm9;
  bits<5> rs1;
  bits<5> vs3;
  bit vm;

  let Inst{31-29} = nf;
  let Inst{28} = mew;
  let Inst{27-20} = simm9{8-1};
  let Inst{19-15} = rs1;
  let Inst{14-12} = width;
  let Inst{11-7} = vs3;
  let Inst{6} = 0b0;
  let Inst{5} = simm9{0}; 
  let Inst{4-0} = 0b01011;

  let Uses = [VTYPE, VL];
}

//===----------------------------------------------------------------------===//
// Instruction class templates
//===----------------------------------------------------------------------===//
let hasSideEffects = 0, mayLoad = 1, mayStore = 0 in {
let RVVConstraint = NoConstraint in {

//Custom unit-stride whole register load vl<nf>ri.v vd, simm_9(rs1)
class VWholeLoad_I<bits<3> nf, RISCVWidth width, string opcodestr, RegisterClass VRC>
    : RVInstVLU_custom<nf, 1,
                width.Value{2-0}, (outs VRC:$vd), (ins GPRMem:$rs1, simm9:$simm9),
                opcodestr, "$vd, ${simm9}(${rs1})"> {
  let Uses = [];
}

} // vm = 1, RVVConstraint = NoConstraint
} // hasSideEffects = 0, mayLoad = 1, mayStore = 0

let hasSideEffects = 0, mayLoad = 0, mayStore = 1 in {

// vs<nf>r.v vs3, simm9(rs1)
class VWholeStore_I<bits<3> nf, string opcodestr, RegisterClass VRC>
    : RVInstVSU_custom<nf, 0,
                0b000, (outs), (ins VRC:$vs3, GPRMem:$rs1, simm9:$simm9),
                opcodestr, "$vs3, ${simm9}(${rs1})"> {
  let Uses = [];
}

}// hasSideEffects = 0, mayLoad = 0, mayStore = 1

//===----------------------------------------------------------------------===//
// Instruction multiclass templates
//===----------------------------------------------------------------------===//
multiclass VWholeLoadN_I<int l, bits<3> nf, string opcodestr, RegisterClass VRC> {
  defvar w = !cast<RISCVWidth>("LSWidth" # l);
  defvar s = !cast<SchedWrite>("WriteVLD" # !add(nf, 1) # "R");

  def E # l # _V : VWholeLoad_I<nf, w, opcodestr # "e" # l # "i.v", VRC>,
                   Sched<[s, ReadVLDX]>;
}


foreach eew = [8, 16, 32, 64] in {
  defvar w = !cast<RISCVWidth>("LSWidth" # eew);

  let Predicates = !if(!eq(eew, 64), [HasVInstructionsI64],
                                     [HasVInstructions]) in {
    
    //Vector Load Whole Register immediate Instructions
    defm VL1R_I_ : VWholeLoadN_I<eew, 0, "vl1r", VR>;
    defm VL2R_I_ : VWholeLoadN_I<eew, 1, "vl2r", VRM2>;
    defm VL4R_I_ : VWholeLoadN_I<eew, 3, "vl4r", VRM4>;
    defm VL8R_I_ : VWholeLoadN_I<eew, 7, "vl8r", VRM8>;
  }
}

let Predicates = [HasVInstructions] in {

//Vector store Whole Register with immediate as offset Instructions
def VS1R_I_V : VWholeStore_I<0, "vs1ri.v", VR>,
             Sched<[WriteVST1R, ReadVST1R, ReadVSTX]>;
def VS2R_I_V : VWholeStore_I<1, "vs2ri.v", VRM2>,
             Sched<[WriteVST2R, ReadVST2R, ReadVSTX]>;
def VS4R_I_V : VWholeStore_I<3, "vs4ri.v", VRM4>,
             Sched<[WriteVST4R, ReadVST4R, ReadVSTX]>;
def VS8R_I_V : VWholeStore_I<7, "vs8ri.v", VRM8>,
             Sched<[WriteVST8R, ReadVST8R, ReadVSTX]>;

} // Predicates = [HasVInstructions]

//===----------------------------------------------------------------------===//
// Helpers to define the SDNode patterns.
//===----------------------------------------------------------------------===//

multiclass VPatUSLoadStoreWholeVRSDNode_I<ValueType type,
                                        int log2sew,
                                        LMULInfo vlmul,
                                        VReg reg_class,
                                        int sew = !shl(1, log2sew)> {
  defvar load_instr =
    !cast<Instruction>("VL"#!substr(vlmul.MX, 1)#"R_I_E"#sew#"_V");
  defvar store_instr =
    !cast<Instruction>("VS"#!substr(vlmul.MX, 1)#"R_I_V");

  // Load
  def : Pat<(type (load (AddrRegImm_V (XLenVT GPR:$rs1), simm9:$simm9))),
            (load_instr GPR:$rs1, simm9:$simm9)>;
  // Store
  def : Pat<(store type:$rs2 , (AddrRegImm_V (XLenVT GPR:$rs1), simm9:$simm9)),
            (store_instr reg_class:$rs2, GPR:$rs1, simm9:$simm9)>;
}

//Load/Store with immediate as offest
foreach vti = [VI8M1, VI8M2, VI8M4, VI8M8, VI16M1, VI16M2, VI16M4, VI16M8, VI32M1, VI32M2, VI32M4, VI32M8, VI64M1, VI64M2, VI64M4, VI64M8] in 
  defm : VPatUSLoadStoreWholeVRSDNode_I<vti.Vector, vti.Log2SEW, vti.LMul, vti.RegClass>;

//===----------------------------------------------------------------------===//
// Instruction Scheduling 
//===----------------------------------------------------------------------===//
