#ifndef LLVM_TRANSFORMS_FNARGCNTNEW_H
#define LLVM_TRANSFORMS_FNARGCNTNEW_H

#include "llvm/IR/PassManager.h"

namespace llvm{
    class FnArgCntNewPass : public PassInfoMixin<FnArgCntNewPass>{
        public:
        // It means that the pass is focus on the function level, not module level
        PreservedAnalyses run(Function &F, FunctionAnalysisManager &AM);
        // It means that the pass is focus on the module level, not function level
        // PreservedAnalyses run(Module &M, ModuleAnalysisManager &AM);
    };
} // namespace llvm

#endif // LLVM_TRANSFORMS_FNARGCNTNEW_H