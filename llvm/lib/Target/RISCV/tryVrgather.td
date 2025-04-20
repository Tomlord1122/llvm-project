// In this file, I am gonna try to trace all the code related to vrgather

//===----------------------------------------------------------------------===//
// RISCVInstrFormats.td
//===----------------------------------------------------------------------===//
// vrgather: The destination vector register group cannot overlap with the
// source vector register groups.
def Vrgather     : RISCVVConstraint<!or(VS2Constraint.Value,
                                        VS1Constraint.Value,
                                        VMConstraint.Value)>;


//===----------------------------------------------------------------------===//
// RISCVInstrInfoV.td
//===----------------------------------------------------------------------===//
multiclass VGTR_IV_V_X_I<string opcodestr, bits<6> funct6> {
  def V  : VALUVV<funct6, OPIVV, opcodestr # ".vv">,
           SchedBinaryMC<"WriteVRGatherVV", "ReadVRGatherVV_data",
                         "ReadVRGatherVV_index">;
  def X  : VALUVX<funct6, OPIVX, opcodestr # ".vx">,
           SchedBinaryMC<"WriteVRGatherVX", "ReadVRGatherVX_data",
                         "ReadVRGatherVX_index">;
  def I  : VALUVI<funct6, opcodestr # ".vi", uimm5>,
           SchedUnaryMC<"WriteVRGatherVI", "ReadVRGatherVI_data">;
}


let Predicates = [HasVInstructions] in {
// Vector Register Gather Instruction
let Constraints = "@earlyclobber $vd", RVVConstraint = Vrgather in {
    defm VRGATHER_V : VGTR_IV_V_X_I<"vrgather", 0b001100>;
    def VRGATHEREI16_VV : VALUVV<0b001110, OPIVV, "vrgatherei16.vv">,
                        SchedBinaryMC<"WriteVRGatherEI16VV",
                                        "ReadVRGatherEI16VV_data",
                                        "ReadVRGatherEI16VV_index">;
} // Constraints = "@earlyclobber $vd", RVVConstraint = Vrgather
} // Predicates = [HasVInstructions]

//===----------------------------------------------------------------------===//
// RISCVInstrInfoVPseudos.td
//===----------------------------------------------------------------------===//
multiclass VPseudoVGTR_EI16_VV {
  defvar constraint = "@earlyclobber $rd";
  foreach m = MxList in {
    defvar mx = m.MX;
    foreach sew = EEWList in {
      defvar dataEMULOctuple = m.octuple;
      // emul = lmul * 16 / sew
      defvar idxEMULOctuple = !srl(!mul(dataEMULOctuple, 16), !logtwo(sew));
      if !and(!ge(idxEMULOctuple, 1), !le(idxEMULOctuple, 64)) then {
        defvar emulMX = octuple_to_str<idxEMULOctuple>.ret;
        defvar emul = !cast<LMULInfo>("V_" # emulMX);
        defvar sews = SchedSEWSet<mx>.val;
        foreach e = sews in {
          defm _VV
              : VPseudoBinaryEmul<m.vrclass, m.vrclass, emul.vrclass, m, emul,
                                  constraint, e>,
                SchedBinary<"WriteVRGatherEI16VV", "ReadVRGatherEI16VV_data",
                            "ReadVRGatherEI16VV_index", mx, e, forceMergeOpRead=true>;
        }
      }
    }
  }
}


multiclass VPseudoVGTR_VV_VX_VI {
  defvar constraint = "@earlyclobber $rd";
  // MxList is the possible LMUL values -> [V_MF8, V_MF4, V_MF2, V_M1, V_M2, V_M4, V_M8];
  foreach m = MxList in {
    defvar mx = m.MX; // mx is LMUL value (e.g. V_MF8 = 1/8, V_MF4 = 1/4, etc.)
    defm "" : VPseudoBinaryV_VX<m, constraint>,
              SchedBinary<"WriteVRGatherVX", "ReadVRGatherVX_data",
                          "ReadVRGatherVX_index", mx, forceMergeOpRead=true>;
    defm "" : VPseudoBinaryV_VI<uimm5, m, constraint>,
              SchedUnary<"WriteVRGatherVI", "ReadVRGatherVI_data", mx,
                         forceMergeOpRead=true>;

    defvar sews = SchedSEWSet<mx>.val;
    foreach e = sews in {
      defm "" : VPseudoBinaryV_VV<m, constraint, e>,
                SchedBinary<"WriteVRGatherVV", "ReadVRGatherVV_data",
                              "ReadVRGatherVV_index", mx, e, forceMergeOpRead=true>;
    }
  }
}

let Predicates = [HasVInstructions] in {
defm PseudoVRGATHER     : VPseudoVGTR_VV_VX_VI;
defm PseudoVRGATHEREI16 : VPseudoVGTR_EI16_VV;
} // Predicates = [HasVInstructions]


// Intrinsic Patterns
defm : VPatBinaryV_VV_VX_VI_INT<"int_riscv_vrgather", "PseudoVRGATHER",
                                AllIntegerVectors, uimm5>;
                                
defm : VPatBinaryV_VV_VX_VI_INT<"int_riscv_vrgather", "PseudoVRGATHER",
                                AllFloatVectors, uimm5>;

defm : VPatBinaryV_VV_INT_EEW<"int_riscv_vrgatherei16_vv", "PseudoVRGATHEREI16",
                              eew=16, vtilist=AllIntegerVectors>;


defm : VPatBinaryV_VV_INT_EEW<"int_riscv_vrgatherei16_vv", "PseudoVRGATHEREI16",
                              eew=16, vtilist=AllFloatVectors>;

//===----------------------------------------------------------------------===//
// RISCVInstrInfoVVLPatterns.td
//===----------------------------------------------------------------------===//
def riscv_vrgather_vx_vl : SDNode<"RISCVISD::VRGATHER_VX_VL",
                                  SDTypeProfile<1, 5, [SDTCisVec<0>,
                                                       SDTCisSameAs<0, 1>,
                                                       SDTCisVT<2, XLenVT>,
                                                       SDTCisSameAs<0, 3>,
                                                       SDTCVecEltisVT<4, i1>,
                                                       SDTCisSameNumEltsAs<0, 4>,
                                                       SDTCisVT<5, XLenVT>]>>;
def riscv_vrgather_vv_vl : SDNode<"RISCVISD::VRGATHER_VV_VL",
                                  SDTypeProfile<1, 5, [SDTCisVec<0>,
                                                       SDTCisSameAs<0, 1>,
                                                       SDTCisInt<2>,
                                                       SDTCisSameNumEltsAs<0, 2>,
                                                       SDTCisSameSizeAs<0, 2>,
                                                       SDTCisSameAs<0, 3>,
                                                       SDTCVecEltisVT<4, i1>,
                                                       SDTCisSameNumEltsAs<0, 4>,
                                                       SDTCisVT<5, XLenVT>]>>;
def riscv_vrgatherei16_vv_vl : SDNode<"RISCVISD::VRGATHEREI16_VV_VL",
                                      SDTypeProfile<1, 5, [SDTCisVec<0>,
                                                           SDTCisSameAs<0, 1>,
                                                           SDTCisInt<2>,
                                                           SDTCVecEltisVT<2, i16>,
                                                           SDTCisSameNumEltsAs<0, 2>,
                                                           SDTCisSameAs<0, 3>,
                                                           SDTCVecEltisVT<4, i1>,
                                                           SDTCisSameNumEltsAs<0, 4>,
                                                           SDTCisVT<5, XLenVT>]>>;


// 16.4. Vector Register Gather Instruction
// Integer Vector Gather Instruction
foreach vti = AllIntegerVectors in {
  let Predicates = GetVTypePredicates<vti>.Predicates in {
    def : Pat<(vti.Vector (riscv_vrgather_vv_vl vti.RegClass:$rs2,
                                                vti.RegClass:$rs1,
                                                vti.RegClass:$merge,
                                                (vti.Mask V0),
                                                VLOpFrag)),
              (!cast<Instruction>("PseudoVRGATHER_VV_"# vti.LMul.MX#"_E"# vti.SEW#"_MASK")
                   vti.RegClass:$merge, vti.RegClass:$rs2, vti.RegClass:$rs1,
                   (vti.Mask V0), GPR:$vl, vti.Log2SEW, TAIL_AGNOSTIC)>;
    def : Pat<(vti.Vector (riscv_vrgather_vx_vl vti.RegClass:$rs2, GPR:$rs1,
                                                vti.RegClass:$merge,
                                                (vti.Mask V0),
                                                VLOpFrag)),
              (!cast<Instruction>("PseudoVRGATHER_VX_"# vti.LMul.MX#"_MASK")
                   vti.RegClass:$merge, vti.RegClass:$rs2, GPR:$rs1,
                   (vti.Mask V0), GPR:$vl, vti.Log2SEW, TAIL_AGNOSTIC)>;
    def : Pat<(vti.Vector (riscv_vrgather_vx_vl vti.RegClass:$rs2,
                                                uimm5:$imm,
                                                vti.RegClass:$merge,
                                                (vti.Mask V0),
                                                VLOpFrag)),
              (!cast<Instruction>("PseudoVRGATHER_VI_"# vti.LMul.MX#"_MASK")
                   vti.RegClass:$merge, vti.RegClass:$rs2, uimm5:$imm,
                   (vti.Mask V0), GPR:$vl, vti.Log2SEW, TAIL_AGNOSTIC)>;
  }

  // emul = lmul * 16 / sew
  defvar vlmul = vti.LMul;
  defvar octuple_lmul = vlmul.octuple;
  defvar octuple_emul = !srl(!mul(octuple_lmul, 16), vti.Log2SEW);
  if !and(!ge(octuple_emul, 1), !le(octuple_emul, 64)) then {
    defvar emul_str = octuple_to_str<octuple_emul>.ret;
    defvar ivti = !cast<VTypeInfo>("VI16" # emul_str);
    defvar inst = "PseudoVRGATHEREI16_VV_" # vti.LMul.MX # "_E" # vti.SEW # "_" # emul_str;
    let Predicates = GetVTypePredicates<vti>.Predicates in
    def : Pat<(vti.Vector
               (riscv_vrgatherei16_vv_vl vti.RegClass:$rs2,
                                         (ivti.Vector ivti.RegClass:$rs1),
                                         vti.RegClass:$merge,
                                         (vti.Mask V0),
                                         VLOpFrag)),
              (!cast<Instruction>(inst#"_MASK")
                   vti.RegClass:$merge, vti.RegClass:$rs2, ivti.RegClass:$rs1,
                   (vti.Mask V0), GPR:$vl, vti.Log2SEW, TAIL_AGNOSTIC)>;
  }
}


// Floating Point Vector Gather Instruction
foreach vti = AllFloatVectors in {
  defvar ivti = GetIntVTypeInfo<vti>.Vti;
  let Predicates = GetVTypePredicates<ivti>.Predicates in {
    def : Pat<(vti.Vector
               (riscv_vrgather_vv_vl vti.RegClass:$rs2,
                                     (ivti.Vector vti.RegClass:$rs1),
                                     vti.RegClass:$merge,
                                     (vti.Mask V0),
                                     VLOpFrag)),
              (!cast<Instruction>("PseudoVRGATHER_VV_"# vti.LMul.MX#"_E"# vti.SEW#"_MASK")
                   vti.RegClass:$merge, vti.RegClass:$rs2, vti.RegClass:$rs1,
                   (vti.Mask V0), GPR:$vl, vti.Log2SEW, TAIL_AGNOSTIC)>;
    def : Pat<(vti.Vector (riscv_vrgather_vx_vl vti.RegClass:$rs2, GPR:$rs1,
                                                vti.RegClass:$merge,
                                                (vti.Mask V0),
                                                VLOpFrag)),
              (!cast<Instruction>("PseudoVRGATHER_VX_"# vti.LMul.MX#"_MASK")
                   vti.RegClass:$merge, vti.RegClass:$rs2, GPR:$rs1,
                   (vti.Mask V0), GPR:$vl, vti.Log2SEW, TAIL_AGNOSTIC)>;
    def : Pat<(vti.Vector
               (riscv_vrgather_vx_vl vti.RegClass:$rs2,
                                     uimm5:$imm,
                                     vti.RegClass:$merge,
                                     (vti.Mask V0),
                                     VLOpFrag)),
              (!cast<Instruction>("PseudoVRGATHER_VI_"# vti.LMul.MX#"_MASK")
                   vti.RegClass:$merge, vti.RegClass:$rs2, uimm5:$imm,
                   (vti.Mask V0), GPR:$vl, vti.Log2SEW, TAIL_AGNOSTIC)>;
  }

  defvar vlmul = vti.LMul;
  defvar octuple_lmul = vlmul.octuple;
  defvar octuple_emul = !srl(!mul(octuple_lmul, 16), vti.Log2SEW);
  if !and(!ge(octuple_emul, 1), !le(octuple_emul, 64)) then {
    defvar emul_str = octuple_to_str<octuple_emul>.ret;
    defvar ivti = !cast<VTypeInfo>("VI16" # emul_str);
    defvar inst = "PseudoVRGATHEREI16_VV_" # vti.LMul.MX # "_E" # vti.SEW # "_" # emul_str;
    let Predicates = !listconcat(GetVTypePredicates<vti>.Predicates,
                                 GetVTypePredicates<ivti>.Predicates) in
    def : Pat<(vti.Vector
               (riscv_vrgatherei16_vv_vl vti.RegClass:$rs2,
                                         (ivti.Vector ivti.RegClass:$rs1),
                                         vti.RegClass:$merge,
                                         (vti.Mask V0),
                                         VLOpFrag)),
              (!cast<Instruction>(inst#"_MASK")
                   vti.RegClass:$merge, vti.RegClass:$rs2, ivti.RegClass:$rs1,
                   (vti.Mask V0), GPR:$vl, vti.Log2SEW, TAIL_AGNOSTIC)>;
  }
}
