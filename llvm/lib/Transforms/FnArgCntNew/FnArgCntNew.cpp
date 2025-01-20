#include "llvm/Transforms/FnArgCntNew/FnArgCntNew.h"
#include "llvm/IR/Function.h"  // For using getName() and arg_size()
#include "llvm/Support/raw_ostream.h"  // For using errs()

using namespace llvm;

PreservedAnalyses FnArgCntNewPass::run(Function &F, FunctionAnalysisManager &AM){
    errs() << "FnArgCnt --- " << F.getName() << ": " << F.arg_size() << "\n";
    return PreservedAnalyses::all();
}