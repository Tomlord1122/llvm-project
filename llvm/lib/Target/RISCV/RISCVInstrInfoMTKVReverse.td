// Define the base class for all reverse instructions
class RVInstV_MTK<bits<6> funct6, bits<5> vs1, RISCVVFormat opv, dag outs,
              dag ins, string opcodestr, string argstr, bit vm>
    : RVInst<outs, ins, opcodestr, argstr, [], InstFormatR> {
  bits<5> vs2;
  bits<5> vd;

  let Inst{31-26} = funct6;
  let Inst{25} = vm;
  let Inst{24-20} = vs2;
  let Inst{19-15} = vs1;
  let Inst{14-12} = opv.Value; // 0b010
  let Inst{11-7} = vd;
  let Inst{6-0} = OPC_OP_V_MTK.Value; // 0b0101011

  let Uses = [VTYPE, VL];
  let RVVConstraint = VMConstraint;
}

// Inherit from the base class and add VRegClass parameter for register class flexibility
let hasSideEffects = 0, mayLoad = 1, mayStore = 0 in {
// op vd, vs2, 
class VALUVs2_MTK<bits<6> funct6, bits<5> vs1, RISCVVFormat opv, bit vm, string opcodestr, RegisterClass VRegClass>
    : RVInstV_MTK<funct6, vs1, opv, (outs VRegClass:$vd),
               (ins VRegClass:$vs2),
               opcodestr, "$vd, $vs2", vm>;
}


// vs1 -> 5bits 
multiclass VREVE_EEW<bits<3> eew_enc, int eew, bit vm> {
    def M1  : VALUVs2_MTK<0b010010, {eew_enc, 0b00}, OPMVV, vm, 
              "vrev"#eew#"m1_i", VR>;
    def M2  : VALUVs2_MTK<0b010010, {eew_enc, 0b01}, OPMVV, vm, 
              "vrev"#eew#"m2_i", VRM2>;
    def M4  : VALUVs2_MTK<0b010010, {eew_enc, 0b10}, OPMVV, vm, 
              "vrev"#eew#"m4_i", VRM4>;
    def M8  : VALUVs2_MTK<0b010010, {eew_enc, 0b11}, OPMVV, vm, 
              "vrev"#eew#"m8_i", VRM8>;
}

multiclass VREVE_EEW_F<bits<3> eew_enc, int eew, bit vm> {
    def M1  : VALUVs2_MTK<0b010010, {eew_enc, 0b00}, OPMVV, vm, 
              "vrev"#eew#"m1_f", VR>;
    def M2  : VALUVs2_MTK<0b010010, {eew_enc, 0b01}, OPMVV, vm, 
              "vrev"#eew#"m2_f", VRM2>;
    def M4  : VALUVs2_MTK<0b010010, {eew_enc, 0b10}, OPMVV, vm, 
              "vrev"#eew#"m4_f", VRM4>;
    def M8  : VALUVs2_MTK<0b010010, {eew_enc, 0b11}, OPMVV, vm, 
              "vrev"#eew#"m8_f", VRM8>;
}

// If the LMUL is fractional, we set vm = 1 to specify the fractional LMUL
multiclass VREVE_EEW_MF<bits<3> eew_enc, int eew, bit vm> {
  def F2  : VALUVs2_MTK<0b010010, {eew_enc, 0b11}, OPMVV, vm, 
              "vrev"#eew#"mf2_i", VR>;
  def F4  : VALUVs2_MTK<0b010010, {eew_enc, 0b10}, OPMVV, vm, 
              "vrev"#eew#"mf4_i", VR>;
  def F8  : VALUVs2_MTK<0b010010, {eew_enc, 0b01}, OPMVV, vm, 
              "vrev"#eew#"mf8_i", VR>;
}

// TODO: e8MF8, e8MF4, e8MF2, e16MF4, e16MF2, e32MF2
// TODO: e16fMF4, e16fMF2, e32fMF2

defm VREV_V_e8M : VREVE_EEW_MF<0b000, 8, 1>;

def VREV_V_e16MF4 : VALUVs2_MTK<0b010010, {0b001, 0b10}, OPMVV, 1, 
              "vrev16mf4_i", VR>;
def VREV_V_e16MF2 : VALUVs2_MTK<0b010010, {0b001, 0b11}, OPMVV, 1, 
              "vrev16mf2_i", VR>;
def VREV_V_e32MF2 : VALUVs2_MTK<0b010010, {0b010, 0b11}, OPMVV, 1, 
              "vrev32mf2_i", VR>;

def VREV_V_e16fMF4 : VALUVs2_MTK<0b010010, {0b101, 0b10}, OPMVV, 1, 
              "vrev16mf4_f", VR>;
def VREV_V_e16fMF2 : VALUVs2_MTK<0b010010, {0b101, 0b11}, OPMVV, 1, 
              "vrev16mf2_f", VR>;
def VREV_V_e32fMF2 : VALUVs2_MTK<0b010010, {0b110, 0b11}, OPMVV, 1, 
              "vrev32mf2_f", VR>;

// Assembly code may look like this: vrev8.v vd, vs2, vrev16.v vd, vs2, vrev32.v vd, vs2, vrev64.v vd, vs2,
defm VREV_V_e8 : VREVE_EEW<0b000, 8, 0>;
defm VREV_V_e16 : VREVE_EEW<0b001, 16, 0>;
defm VREV_V_e32 : VREVE_EEW<0b010, 32, 0>;
defm VREV_V_e64 : VREVE_EEW<0b011, 64, 0>;
defm VREV_V_e16f : VREVE_EEW_F<0b101, 16, 0>;
defm VREV_V_e32f : VREVE_EEW_F<0b110, 32, 0>;
defm VREV_V_e64f : VREVE_EEW_F<0b111, 64, 0>;

// When expand VREV_V_e8, VREV_V_e16, VREV_V_e32, VREV_V_e64, we will get the following instructions
// VREV_V_e8MF2, VREV_V_e8MF4, VREV_V_e8MF8, VREV_V_e16MF4, VREV_V_e16MF2, VREV_V_e32MF2, VREV_V_e16fMF4, VREV_V_e16fMF2, VREV_V_e32fMF2
// VREV_V_e8M1, VREV_V_e16M1, VREV_V_e32M1, VREV_V_e64M1
// VREV_V_e8M2, VREV_V_e16M2, VREV_V_e32M2, VREV_V_e64M2
// VREV_V_e8M4, VREV_V_e16M4, VREV_V_e32M4, VREV_V_e64M4
// VREV_V_e8M8, VREV_V_e16M8, VREV_V_e32M8, VREV_V_e64M8

//===----------------------------------------------------------------------===//
// try try Pseudo instructions
//===----------------------------------------------------------------------===//

multiclass VPseudoUnaryV_V_REV<LMULInfo m> {
  let VLMul = m.value in {
    foreach eew = [8, 16, 32, 64] in {
      def "_V_e"#eew#m.MX : VPseudoUnaryNoMask<m.vrclass, m.vrclass> {
        let Predicates = [HasVInstructions];
      }
    } 

    foreach eew = [16, 32, 64] in {
      def "_V_e"#eew#"f"#m.MX : VPseudoUnaryNoMask<m.vrclass, m.vrclass> {
        let Predicates = [HasVInstructions];
      }
    }
  } 
}


// VREV_V_e8MF2, VREV_V_e8MF4, VREV_V_e8MF8, VREV_V_e16MF4, VREV_V_e16MF2, VREV_V_e32MF2, VREV_V_e16fMF4, VREV_V_e16fMF2, VREV_V_e32fMF2
multiclass VPseudoUnaryV_V_REV_MF {
  def "_V_e8MF2" : VPseudoUnaryNoMask<VR, VR> {
    let Predicates = [HasVInstructions];
  }

  def "_V_e8MF4" : VPseudoUnaryNoMask<VR, VR> {
    let Predicates = [HasVInstructions];
  }

  def "_V_e8MF8" : VPseudoUnaryNoMask<VR, VR> {
    let Predicates = [HasVInstructions];
  }

  def "_V_e16MF4" : VPseudoUnaryNoMask<VR, VR> {
    let Predicates = [HasVInstructions];
  }

  def "_V_e16MF2" : VPseudoUnaryNoMask<VR, VR> {
    let Predicates = [HasVInstructions];
  }
  
  def "_V_e32MF2" : VPseudoUnaryNoMask<VR, VR> {
    let Predicates = [HasVInstructions];
  }

  def "_V_e16fMF4" : VPseudoUnaryNoMask<VR, VR> {
    let Predicates = [HasVInstructions];
  }

  def "_V_e16fMF2" : VPseudoUnaryNoMask<VR, VR> {
    let Predicates = [HasVInstructions];
  }

  def "_V_e32fMF2" : VPseudoUnaryNoMask<VR, VR> {
    let Predicates = [HasVInstructions];
  }
  
  
}

// defm "" : LMULSchedWrites<"WriteVREV">;
// defm "" : LMULSchedReads<"ReadVREV">;
defvar MxList_REV = [V_M1, V_M2, V_M4, V_M8];

multiclass VPseudoVREV {
  foreach m = MxList_REV in {
    defm "" : VPseudoUnaryV_V_REV<m>, 
              SchedUnary<"WriteVREV8V", "ReadVREV8V", m.MX, forceMergeOpRead=true>;
  }
}

defm PseudoVREV : VPseudoVREV, VPseudoUnaryV_V_REV_MF<>;

// When expand PseudoVREV, we will get the following instructions
// PseudoVREV_V_e8M1, PseudoVREV_V_e16M1, PseudoVREV_V_e32M1, PseudoVREV_V_e64M1
// PseudoVREV_V_e8M2, PseudoVREV_V_e16M2, PseudoVREV_V_e32M2, PseudoVREV_V_e64M2
// PseudoVREV_V_e8M4, PseudoVREV_V_e16M4, PseudoVREV_V_e32M4, PseudoVREV_V_e64M4
// PseudoVREV_V_e8M8, PseudoVREV_V_e16M8, PseudoVREV_V_e32M8, PseudoVREV_V_e64M8


//===----------------------------------------------------------------------===//
// try try Pseudo instructions Pattern match
//===----------------------------------------------------------------------===//

// Pattern match -> PseudoVREV_V_e8, PseudoVREV_V_e16, PseudoVREV_V_e32, PseudoVREV_V_e64

multiclass VPatUnarySDNode_V_REV<SDPatternOperator op, string instruction_name,
                             Predicate predicate = HasVInstructions> {
  foreach vti = [VI8MF8, VI8MF4, VI8MF2, VI8M1, VI8M2, VI8M4, VI8M8, VI16MF4, VI16MF2, VI16M1, VI16M2, VI16M4, VI16M8, VI32MF2, VI32M1, VI32M2, VI32M4, VI32M8, VI64M1, VI64M2, VI64M4, VI64M8] in {
    let Predicates = !listconcat([predicate],
                                 GetVTypePredicates<vti>.Predicates) in {
      def : Pat<(vti.Vector (op (vti.Vector vti.RegClass:$vs2))),
                (!cast<Instruction>(instruction_name#"_V_e"#vti.SEW#vti.LMul.MX)
                   (vti.Vector (IMPLICIT_DEF)),
                   vti.RegClass:$vs2,
                   vti.AVL, vti.Log2SEW, TA_MA)>;
    }
  }
  foreach vti = [VF16MF4, VF16MF2, VF32MF2, VF16M1, VF32M1, VF64M1, VF16M2, VF16M4, VF16M8, VF32M2, VF32M4, VF32M8, VF64M2, VF64M4, VF64M8] in {
    let Predicates = !listconcat([predicate],
                                GetVTypePredicates<vti>.Predicates) in {
      def : Pat<(vti.Vector (op (vti.Vector vti.RegClass:$vs2))),
                (!cast<Instruction>(instruction_name#"_V_e"#vti.SEW#"f"#vti.LMul.MX)
                  (vti.Vector (IMPLICIT_DEF)),
                  vti.RegClass:$vs2,
                  vti.AVL, vti.Log2SEW, TA_MA)>;
    }
  }
}



defm : VPatUnarySDNode_V_REV<riscv_vreversemtk_v_vl, "PseudoVREV", HasVInstructions>;



