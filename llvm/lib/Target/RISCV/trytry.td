
// RISCVInstrInfoVPseudos.td
// The actual table.
def RISCVVPseudosTable : GenericTable {
  let FilterClass = "RISCVVPseudo";
  let FilterClassField = "NeedBeInPseudoTable";
  let CppTypeName = "PseudoInfo";
  let Fields = [ "Pseudo", "BaseInstr" ];
  let PrimaryKey = [ "Pseudo" ];
  let PrimaryKeyName = "getPseudoInfo";
  let PrimaryKeyEarlyOut = true;
}

def RISCVVInversePseudosTable : GenericTable {
  let FilterClass = "RISCVVPseudo";
  let CppTypeName = "PseudoInfo";
  let Fields = [ "Pseudo", "BaseInstr", "VLMul", "SEW"];
  let PrimaryKey = [ "BaseInstr", "VLMul", "SEW"];
  let PrimaryKeyName = "getBaseInfo";
  let PrimaryKeyEarlyOut = true;
}


//===----------------------------------------------------------------------===//
// VREV8 instruction format and definition in zvkb extension
//===----------------------------------------------------------------------===//
// RISCVInstrFormatsV.td
class RVInstV<bits<6> funct6, bits<5> vs1, RISCVVFormat opv, dag outs,
              dag ins, string opcodestr, string argstr>
    : RVInst<outs, ins, opcodestr, argstr, [], InstFormatR> {
  bits<5> vs2;
  bits<5> vd;
  bit vm;

  let Inst{31-26} = funct6;
  let Inst{25} = vm;
  let Inst{24-20} = vs2;
  let Inst{19-15} = vs1;
  let Inst{14-12} = opv.Value;
  let Inst{11-7} = vd;
  let Inst{6-0} = OPC_OP_V.Value; 

  let Uses = [VTYPE, VL];
  let RVVConstraint = VMConstraint;
}

// RISCVInstrInfoV.td
let hasSideEffects = 0, mayLoad = 1, mayStore = 0 in {
  class VALUVs2<bits<6> funct6, bits<5> vs1, RISCVVFormat opv, string opcodestr>
    : RVInstV<funct6, vs1, opv, (outs VR:$vd),
                (ins VR:$vs2), VMaskOp:$vm,
                opcodestr, "$vd, $vs2$vm">;
}

// RISCVInstrInfoZvk.td
let Predicates = [HasStdExtZvkb] in {
  def VREV8V : VALUVs2<0b010010, 0b01001, OPMVV, "vrev8.v">; 
}


//===----------------------------------------------------------------------===//
// PseudoVREV8 instruction format and definition in zvkb extension
//===----------------------------------------------------------------------===//

//--------------------------------
// Class related to VPseudoUnaryV_V
//--------------------------------
// RISCVInstrInfoVPseudos.td
class PseudoToVInst<string PseudoInst> {
  defvar AffixSubsts = [["Pseudo", ""],
                        ["_E64", ""],
                        ["_E32", ""],
                        ["_E16", ""],
                        ["_E8", ""],
                        ["FPR64", "F"],
                        ["FPR32", "F"],
                        ["FPR16", "F"],
                        ["_TIED", ""],
                        ["_MASK", ""],
                        ["_B64", ""],
                        ["_B32", ""],
                        ["_B16", ""],
                        ["_B8", ""],
                        ["_B4", ""],
                        ["_B2", ""],
                        ["_B1", ""],
                        ["_MF8", ""],
                        ["_MF4", ""],
                        ["_MF2", ""],
                        ["_M1", ""],
                        ["_M2", ""],
                        ["_M4", ""],
                        ["_M8", ""],
                        ["_SE", ""],
                        ["_RM", ""]
                       ];
  string VInst = !foldl(PseudoInst, AffixSubsts, Acc, AffixSubst,
                        !subst(AffixSubst[0], AffixSubst[1], Acc));
}

// RISCVInstrFormats.td
class Pseudo<dag outs, dag ins, list<dag> pattern, string opcodestr = "", string argstr = "">
    : RVInst<outs, ins, opcodestr, argstr, pattern, InstFormatPseudo> {
  let isPseudo = 1;
  let isCodeGenOnly = 1;
}

// This class holds the record of the RISCVVPseudoTable below.
// This represents the information we need in codegen for each pseudo.
// The definition should be consistent with `struct PseudoInfo` in
// RISCVInstrInfo.h.

// RISCVInstrInfoVPseudos.td
class RISCVVPseudo {
  Pseudo Pseudo = !cast<Pseudo>(NAME); // Used as a key.
  Instruction BaseInstr = !cast<Instruction>(PseudoToVInst<NAME>.VInst);
  // SEW = 0 is used to denote that the Pseudo is not SEW specific (or unknown).
  bits<8> SEW = 0;
  bit NeedBeInPseudoTable = 1;
}

// RISCVInstrInfoVPseudos.td
class VPseudoUnaryNoMask<DAGOperand RetClass,
                         DAGOperand OpClass,
                         string Constraint = "",
                         int TargetConstraintType = 1> :
      Pseudo<(outs RetClass:$rd),
             (ins RetClass:$merge, OpClass:$rs2,
                  AVL:$vl, ixlenimm:$sew, ixlenimm:$policy), []>,
      RISCVVPseudo {
  let mayLoad = 0;
  let mayStore = 0;
  let hasSideEffects = 0;
  let Constraints = !interleave([Constraint, "$rd = $merge"], ",");
  let TargetOverlapConstraintType = TargetConstraintType;
  let HasVLOp = 1;
  let HasSEWOp = 1;
  let HasVecPolicyOp = 1;
}

// RISCVInstrInfoVPseudos.td
class VPseudoUnaryMask<VReg RetClass,
                       VReg OpClass,
                       string Constraint = "",
                       int TargetConstraintType = 1> :
      Pseudo<(outs GetVRegNoV0<RetClass>.R:$rd),
             (ins GetVRegNoV0<RetClass>.R:$merge, OpClass:$rs2,
                  VMaskOp:$vm, AVL:$vl, ixlenimm:$sew, ixlenimm:$policy), []>,
      RISCVVPseudo {
  let mayLoad = 0;
  let mayStore = 0;
  let hasSideEffects = 0;
  let Constraints = !interleave([Constraint, "$rd = $merge"], ",");
  let TargetOverlapConstraintType = TargetConstraintType;
  let HasVLOp = 1;
  let HasSEWOp = 1;
  let HasVecPolicyOp = 1;
  let UsesMaskPolicy = 1;
}


// Describes the relation of a masked pseudo to the unmasked variants.
//    Note that all masked variants (in this table) have exactly one
//    unmasked variant.  For all but compares, both the masked and
//    unmasked variant have a passthru and policy operand.  For compares,
//    neither has a policy op, and only the masked version has a passthru.

// RISCVInstrInfoVPseudos.td
class RISCVMaskedPseudo<bits<4> MaskIdx, bit ActiveAffectsRes=false> {
  Pseudo MaskedPseudo = !cast<Pseudo>(NAME);
  Pseudo UnmaskedPseudo = !cast<Pseudo>(!subst("_MASK", "", NAME));
  bits<4> MaskOpIdx = MaskIdx;
  bit ActiveElementsAffectResult = ActiveAffectsRes;
}

// RISCVInstrInfoVPseudos.td
// This class describes information associated to the LMUL.
class LMULInfo<int lmul, int oct, VReg regclass, VReg wregclass,
               VReg f2regclass, VReg f4regclass, VReg f8regclass, string mx> {
  bits<3> value = lmul; // This is encoded as the vlmul field of vtype.
  VReg vrclass = regclass;
  VReg wvrclass = wregclass;
  VReg f8vrclass = f8regclass;
  VReg f4vrclass = f4regclass;
  VReg f2vrclass = f2regclass;
  string MX = mx;
  int octuple = oct;
}

// RISCVInstrInfoZvk.td
multiclass VPseudoUnaryV_V<LMULInfo m> {
  let VLMul = m.value in {
    defvar suffix = "_V_" # m.MX;
    def suffix : VPseudoUnaryNoMask<m.vrclass, m.vrclass>;
    def suffix # "_MASK" : VPseudoUnaryMask<m.vrclass, m.vrclass>,
                                            RISCVMaskedPseudo<MaskIdx=2>;
  }
}

//--------------------------------
// Class related to SchedUnary
//--------------------------------

// Common class of scheduling definitions.
// `ReadVMergeOp` will be prepended to reads if instruction is masked.
// `ReadVMask` will be appended to reads if instruction is masked.
// Operands:
//   `writes`       SchedWrites that are listed for each explicit def operand
//                  in order.
//   `reads`        SchedReads that are listed for each explicit use operand.
//   `forceMasked`  Forced to be masked (e.g. Add-with-Carry Instructions).
//   `forceMergeOpRead` Force to have read for merge operand.

// RISCVInstrInfoV.td
class SchedCommon<list<SchedWrite> writes, list<SchedRead> reads,
                  string mx = "WorstCase", int sew = 0, bit forceMasked = 0,
                  bit forceMergeOpRead = 0> : Sched<[]> {
  defvar isMasked = !ne(!find(NAME, "_MASK"), -1);
  defvar isMaskedOrForceMasked = !or(forceMasked, isMasked);
  defvar mergeRead = !if(!or(!eq(mx, "WorstCase"), !eq(sew, 0)),
                            !cast<SchedRead>("ReadVMergeOp_" # mx),
                            !cast<SchedRead>("ReadVMergeOp_" # mx # "_E" #sew));
  defvar needsMergeRead = !or(isMaskedOrForceMasked, forceMergeOpRead);
  defvar readsWithMask =
      !if(isMaskedOrForceMasked, !listconcat(reads, [ReadVMask]), reads);
  defvar allReads =
      !if(needsMergeRead, !listconcat([mergeRead], readsWithMask), reads);
let SchedRW = !listconcat(writes, allReads);
}

// Common class of scheduling definitions for n-ary instructions.
// The scheudling resources are relevant to LMUL and may be relevant to SEW.

// RISCVInstrInfoV.td
class SchedNary<string write, list<string> reads, string mx, int sew = 0,
                bit forceMasked = 0, bit forceMergeOpRead = 0>
    : SchedCommon<[!cast<SchedWrite>(
                      !if(sew,
                          write # "_" # mx # "_E" # sew,
                          write # "_" # mx))],
                  !foreach(read, reads,
                           !cast<SchedRead>(!if(sew, read #"_" #mx #"_E" #sew,
                                                 read #"_" #mx))),
                  mx, sew, forceMasked, forceMergeOpRead>;

class SchedUnary<string write, string read0, string mx, int sew = 0,
                 bit forceMasked = 0, bit forceMergeOpRead = 0>:
  SchedNary<write, [read0], mx, sew, forceMasked, forceMergeOpRead>;


// RISCVInstrInfoZvk.td
multiclass VPseudoVREV8 {
  foreach m = MxList in {
    defvar mx = m.MX;
    defm "" : VPseudoUnaryV_V<m>,
              SchedUnary<"WriteVREV8V", "ReadVREV8V", mx, forceMergeOpRead=true>;
  }
}

let Predicates = [HasStdExtZvkb] in {
  defm PseudoVREV8 : VPseudoVREV8;
}


//===----------------------------------------------------------------------===//
// PseudoVREV8 Pattern Matching
//===----------------------------------------------------------------------===//

class VTypeInfo<ValueType Vec, ValueType Mas, int Sew, LMULInfo M,
                ValueType Scal = XLenVT, RegisterClass ScalarReg = GPR> {
  ValueType Vector = Vec;
  ValueType Mask = Mas;
  int SEW = Sew;
  int Log2SEW = !logtwo(Sew);
  VReg RegClass = M.vrclass;
  LMULInfo LMul = M;
  ValueType Scalar = Scal;
  RegisterClass ScalarRegClass = ScalarReg;
  // The pattern fragment which produces the AVL operand, representing the
  // "natural" vector length for this type. For scalable vectors this is VLMax.
  OutPatFrag AVL = VLMax;

  string ScalarSuffix = !cond(!eq(Scal, XLenVT) : "X",
                              !eq(Scal, f16) : "FPR16",
                              !eq(Scal, bf16) : "FPR16",
                              !eq(Scal, f32) : "FPR32",
                              !eq(Scal, f64) : "FPR64");
}

defset list<VTypeInfo> AllVectors = {
  defset list<VTypeInfo> AllIntegerVectors = {
    defset list<VTypeInfo> NoGroupIntegerVectors = {
      defset list<VTypeInfo> FractionalGroupIntegerVectors = {
        def VI8MF8:  VTypeInfo<vint8mf8_t,  vbool64_t, 8,  V_MF8>;
        def VI8MF4:  VTypeInfo<vint8mf4_t,  vbool32_t, 8,  V_MF4>;
        def VI8MF2:  VTypeInfo<vint8mf2_t,  vbool16_t, 8,  V_MF2>;
        def VI16MF4: VTypeInfo<vint16mf4_t, vbool64_t, 16, V_MF4>;
        def VI16MF2: VTypeInfo<vint16mf2_t, vbool32_t, 16, V_MF2>;
        def VI32MF2: VTypeInfo<vint32mf2_t, vbool64_t, 32, V_MF2>;
      }
      def VI8M1:  VTypeInfo<vint8m1_t,  vbool8_t,   8, V_M1>;
      def VI16M1: VTypeInfo<vint16m1_t, vbool16_t, 16, V_M1>;
      def VI32M1: VTypeInfo<vint32m1_t, vbool32_t, 32, V_M1>;
      def VI64M1: VTypeInfo<vint64m1_t, vbool64_t, 64, V_M1>;
    }
    defset list<GroupVTypeInfo> GroupIntegerVectors = {
      def VI8M2: GroupVTypeInfo<vint8m2_t, vint8m1_t, vbool4_t, 8, V_M2>;
      def VI8M4: GroupVTypeInfo<vint8m4_t, vint8m1_t, vbool2_t, 8, V_M4>;
      def VI8M8: GroupVTypeInfo<vint8m8_t, vint8m1_t, vbool1_t, 8, V_M8>;

      def VI16M2: GroupVTypeInfo<vint16m2_t, vint16m1_t, vbool8_t, 16, V_M2>;
      def VI16M4: GroupVTypeInfo<vint16m4_t, vint16m1_t, vbool4_t, 16, V_M4>;
      def VI16M8: GroupVTypeInfo<vint16m8_t, vint16m1_t, vbool2_t, 16, V_M8>;

      def VI32M2: GroupVTypeInfo<vint32m2_t, vint32m1_t, vbool16_t, 32, V_M2>;
      def VI32M4: GroupVTypeInfo<vint32m4_t, vint32m1_t, vbool8_t,  32, V_M4>;
      def VI32M8: GroupVTypeInfo<vint32m8_t, vint32m1_t, vbool4_t,  32, V_M8>;

      def VI64M2: GroupVTypeInfo<vint64m2_t, vint64m1_t, vbool32_t, 64, V_M2>;
      def VI64M4: GroupVTypeInfo<vint64m4_t, vint64m1_t, vbool16_t, 64, V_M4>;
      def VI64M8: GroupVTypeInfo<vint64m8_t, vint64m1_t, vbool8_t,  64, V_M8>;
    }
  }
}

multiclass VPatUnarySDNode_V<SDPatternOperator op, string instruction_name,
                             Predicate predicate = HasStdExtZvbb> {
  foreach vti = AllIntegerVectors in {
    let Predicates = !listconcat([predicate],
                                 GetVTypePredicates<vti>.Predicates) in {
      def : Pat<(vti.Vector (op (vti.Vector vti.RegClass:$rs1))),
                (!cast<Instruction>(instruction_name#"_V_"#vti.LMul.MX)
                   (vti.Vector (IMPLICIT_DEF)),
                   vti.RegClass:$rs1,
                   vti.AVL, vti.Log2SEW, TA_MA)>;
    }
  }
}

defm : VPatUnarySDNode_V<bswap, "PseudoVREV8", HasStdExtZvkb>;



