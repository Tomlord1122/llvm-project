//===----------------------------------------------------------------------===// 
// try try VREV instructions
//===----------------------------------------------------------------------===//
// Define the base class for all reverse instructions
class RVInstV_MTK<bits<6> funct6, bits<5> vs1, RISCVVFormat opv, dag outs,
              dag ins, string opcodestr, string argstr>
    : RVInst<outs, ins, opcodestr, argstr, [], InstFormatR> {
  bits<5> vs2;
  bits<5> vd;
  bit vm = 0b1; 

  let Inst{31-26} = funct6;
  let Inst{25} = vm; // value 1 means don't use mask
  let Inst{24-20} = vs2;
  let Inst{19-15} = vs1;
  let Inst{14-12} = opv.Value; // 0b010 -> Defined in RISCVInstrFormatsV.td
  let Inst{11-7} = vd;
  let Inst{6-0} = OPC_OP_V_MTK.Value; // 0b0101011 -> Defined in RISCVInstrFormats.td

  let Uses = [VTYPE, VL];
  let RVVConstraint = VMConstraint;
}

// Inherit from the base class and add VRegClass parameter for register class flexibility

let hasSideEffects = 0, mayLoad = 0, mayStore = 0 in {
// op vd, vs2, 
class VALUVs2_MTK<bits<6> funct6, bits<5> vs1, RISCVVFormat opv, string opcodestr, RegisterClass VRegClass>
    : RVInstV_MTK<funct6, vs1, opv, (outs VRegClass:$vd),
               (ins VRegClass:$vs2),
               opcodestr, "$vd, $vs2">;
}


// vs1 -> 5bits 
multiclass VREVE_EEW<bits<2> eew_enc> {
    def M1  : VALUVs2_MTK<0b010010, {eew_enc, 0b000}, OPMVV,
              "vrev.v", VR>;
    def M2  : VALUVs2_MTK<0b010010, {eew_enc, 0b001}, OPMVV,
              "vrev.v", VR>;
    def M4  : VALUVs2_MTK<0b010010, {eew_enc, 0b010}, OPMVV,
              "vrev.v", VR>;
    def M8  : VALUVs2_MTK<0b010010, {eew_enc, 0b011}, OPMVV,
              "vrev.v", VRM8>;
}

// VREV_V_e8M1, VREV_V_e8M2, VREV_V_e8M4, VREV_V_e8M8 -> vrev8m1, vrev8m2, vrev8m4, vrev8m8
defm VREV_V_e8 : VREVE_EEW<0b00>;
defm VREV_V_e16 : VREVE_EEW<0b01>;
defm VREV_V_e32 : VREVE_EEW<0b10>;
defm VREV_V_e64 : VREVE_EEW<0b11>;

// Handle the remain cases that LMUL is fractional
def VREV_V_e8MF2 : VALUVs2_MTK<0b010010, {0b00, 0b111}, OPMVV,
              "vrev.v", VR>;
def VREV_V_e8MF4 : VALUVs2_MTK<0b010010, {0b00, 0b110}, OPMVV,
              "vrev.v", VR>;
def VREV_V_e8MF8 : VALUVs2_MTK<0b010010, {0b00, 0b101}, OPMVV,
              "vrev.v", VR>;

def VREV_V_e16MF4 : VALUVs2_MTK<0b010010, {0b01, 0b110}, OPMVV,
              "vrev.v", VR>;
def VREV_V_e16MF2 : VALUVs2_MTK<0b010010, {0b01, 0b111}, OPMVV,
              "vrev.v", VR>;
def VREV_V_e32MF2 : VALUVs2_MTK<0b010010, {0b10, 0b111}, OPMVV,
              "vrev.v", VR>;



//===----------------------------------------------------------------------===//
// try try Pseudo instructions
//===----------------------------------------------------------------------===//

multiclass VPseudoUnaryV_V_REV<LMULInfo m> {
  let VLMul = m.value in {
    foreach eew = [8, 16, 32, 64] in {
      def "_V_e"#eew#m.MX : VPseudoUnaryNoMask<m.vrclass, m.vrclass> {
        let Predicates = [HasVInstructions];
      }
      def "_V_e"#eew#m.MX#"_MASK" : VPseudoUnaryMask<m.vrclass, m.vrclass>, RISCVMaskedPseudo<MaskIdx=2> {
        let Predicates = [HasVInstructions];
      }
    } 
  } 
}

// Define a class to hold the Suffix string and LMULInfo object pair
class SuffixLmulPair<string suffix, LMULInfo lmul> {
  string Suffix = suffix;
  LMULInfo Lmul = lmul;
}

// Define the list using instances of the SuffixLmulPair class
defvar MF_PAIRS = [
  SuffixLmulPair<"_V_e8MF2", V_MF2>,
  SuffixLmulPair<"_V_e8MF4", V_MF4>,
  SuffixLmulPair<"_V_e8MF8", V_MF8>,
  SuffixLmulPair<"_V_e16MF4", V_MF4>,
  SuffixLmulPair<"_V_e16MF2", V_MF2>,
  SuffixLmulPair<"_V_e32MF2", V_MF2>
];

multiclass VPseudoUnaryV_V_REV_MF {
  let Predicates = [HasVInstructions] in {
    // Iterate over the list of SuffixLmulPair instances
    foreach pair = MF_PAIRS in {
      // Access the fields by their defined names
      defvar suffix_name = pair.Suffix;
      defvar lmul_info = pair.Lmul;

      // Define the unmasked pseudo instruction
      def suffix_name : VPseudoUnaryNoMask<VR, VR>, SchedUnary<"WriteVREV8V", "ReadVREV8V", lmul_info.MX, forceMergeOpRead=true>;

      // Define the masked pseudo instruction
      def suffix_name # "_MASK" : VPseudoUnaryMask<VR, VR>, RISCVMaskedPseudo<MaskIdx=2>, SchedUnary<"WriteVREV8V", "ReadVREV8V", lmul_info.MX, forceMergeOpRead=true>;
    }
  }
}



defvar MxList_REV = [V_M1, V_M2, V_M4, V_M8];

multiclass VPseudoVREV {
  foreach m = MxList_REV in {
    defm "" : VPseudoUnaryV_V_REV<m>, 
              SchedUnary<"WriteVREV8V", "ReadVREV8V", m.MX, forceMergeOpRead=true>;
  }
  defm "" : VPseudoUnaryV_V_REV_MF;
}

defm PseudoVREV : VPseudoVREV;

//===----------------------------------------------------------------------===//
// try try Pseudo instructions Pattern match
//===----------------------------------------------------------------------===//
// VPatUnarySDNode_V
// VPatUnaryVL_V
multiclass VPatUnarySDNode_V_REV<SDPatternOperator op, string instruction_name,
                             Predicate predicate = HasVInstructions> {
  foreach vti = [VI8MF8, VI8MF4, VI8MF2, VI8M1, VI8M2, VI8M4, VI8M8, VI16MF4, VI16MF2, VI16M1, VI16M2, VI16M4, VI16M8, VI32MF2, VI32M1, VI32M2, VI32M4, VI32M8, VI64M1, VI64M2, VI64M4, VI64M8,
  VF16MF4, VF16MF2, VF32MF2, VF16M1, VF32M1, VF64M1, VF16M2, VF16M4, VF16M8, VF32M2, VF32M4, VF32M8, VF64M2, VF64M4, VF64M8] in {
    let Predicates = !listconcat([predicate],
                                 GetVTypePredicates<vti>.Predicates) in {
      def : Pat<(vti.Vector (op (vti.Vector vti.RegClass:$vs2))),
                (!cast<Instruction>(instruction_name#"_V_e"#vti.SEW#vti.LMul.MX)
                  (vti.Vector (IMPLICIT_DEF)),
                   vti.RegClass:$vs2,
                   vti.AVL, vti.Log2SEW, TA_MA)>;
    }
  }
}
defm : VPatUnarySDNode_V_REV<riscv_vreversemtk_v_vl, "PseudoVREV", HasVInstructions>;


// Pseudo Instruction PseudoVREV_V_e32M2 -> VREV_V_e32M2