#include "llvm/Pass.h"
#include "llvm/Module.h"
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Constants.h"
#include "llvm/Analysis/Dominators.h"
#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/InstrTypes.h"
#include "llvm/DerivedTypes.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/AliasAnalysis.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Support/CallSite.h"
#include "llvm/Support/CFG.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/InlineAsm.h"
#include<map>
#include<string>
#include<queue>
using namespace llvm;

namespace {

  class IroncladVerifier: public ModulePass {
    
  public:
    static char ID;
    bool runOnModule(Module&);
    IroncladVerifier(): ModulePass((intptr_t)&ID){}

    

  };

  bool IroncladVerifier:: runOnModule(Module &){

    llvm::cerr<<"I am in IroncladVerifier\n";
  }

  char IroncladVerifier:: ID = 0;
  RegisterPass<IroncladVerifier> X("IroncladVerifier", "IroncladVerifier for memory safety"); 

}
