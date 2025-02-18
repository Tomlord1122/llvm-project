// Define the base class for all reverse instructions
class RVInstV_MTK<bits<6> funct6, bits<5> vs1, RISCVVFormat opv, dag outs,
              dag ins, string opcodestr, string argstr>
    : RVInst<outs, ins, opcodestr, argstr, [], InstFormatR> {
  bits<5> vs2;
  bits<5> vd;
  // bit vm;

  let Inst{31-26} = funct6;
  let Inst{25} = 0;
  let Inst{24-20} = vs2;
  let Inst{19-15} = vs1;
  let Inst{14-12} = opv.Value;
  let Inst{11-7} = vd;
  let Inst{6-0} = OPC_OP_V_MTK.Value; 

  let Uses = [VTYPE, VL];
  let RVVConstraint = VMConstraint;
}

// Inherit from the base class and add VRegClass parameter for register class flexibility
let hasSideEffects = 0, mayLoad = 1, mayStore = 0 in {
// op vd, vs2, 
class VALUVs2_MTK<bits<6> funct6, bits<5> vs1, RISCVVFormat opv, string opcodestr, RegisterClass VRegClass>
    : RVInstV_MTK<funct6, vs1, opv, (outs VRegClass:$vd),
               (ins VRegClass:$vs2),
               opcodestr, "$vd, $vs2">;
}



multiclass VREVE_EEW<bits<2> eew_enc, int eew> {
    def M1  : VALUVs2_MTK<0b010010, {eew_enc, 0b000}, OPMVV, 
              "vrev"#eew#".v", VR>;
    def M2  : VALUVs2_MTK<0b010010, {eew_enc, 0b001}, OPMVV, 
              "vrev"#eew#".v", VRM2>;
    def M4  : VALUVs2_MTK<0b010010, {eew_enc, 0b010}, OPMVV, 
              "vrev"#eew#".v", VRM4>;
    def M8  : VALUVs2_MTK<0b010010, {eew_enc, 0b011}, OPMVV, 
              "vrev"#eew#".v", VRM8>;
}
// Assembly code may look like this: vrev8.v vd, vs2, vrev16.v vd, vs2, vrev32.v vd, vs2, vrev64.v vd, vs2,
defm VREV_V_e8 : VREVE_EEW<0b00, 8>;
defm VREV_V_e16 : VREVE_EEW<0b01, 16>;
defm VREV_V_e32 : VREVE_EEW<0b10, 32>;
defm VREV_V_e64 : VREVE_EEW<0b11, 64>;

// When expand VREV_V_e8, VREV_V_e16, VREV_V_e32, VREV_V_e64, we will get the following instructions
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
  } 
}

// defm "" : LMULSchedWrites<"WriteVREV8V">;
// defm "" : LMULSchedReads<"ReadVREV8V">;
defvar MxList_REV = [V_M1, V_M2, V_M4, V_M8];

multiclass VPseudoVREV {
  foreach m = MxList_REV in {
    defm "" : VPseudoUnaryV_V_REV<m>, 
  }
}

defm PseudoVREV : VPseudoVREV;

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
  foreach vti = [VI8M1, VI8M2, VI8M4, VI8M8, VI16M1, VI16M2, VI16M4, VI16M8, VI32M1, VI32M2, VI32M4, VI32M8, VI64M1, VI64M2, VI64M4, VI64M8] in {
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

