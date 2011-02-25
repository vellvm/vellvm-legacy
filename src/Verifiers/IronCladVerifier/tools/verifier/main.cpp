
#include "verifier.h"
#include<stdio.h>

#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/PassManager.h"
#include "llvm/CallGraphSCCPass.h"
#include "llvm/Bitcode/ReaderWriter.h"
#include "llvm/Assembly/PrintModulePass.h"
#include "llvm/Analysis/Verifier.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Target/TargetData.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Support/PassNameParser.h"
#include "llvm/System/Signals.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/IRReader.h"
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/PluginLoader.h"
#include "llvm/Support/PrettyStackTrace.h"
#include "llvm/Support/StandardPasses.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/LinkAllVMCore.h"
#include <memory>
#include <algorithm>
using namespace llvm;

static cl::opt<std::string>
Input1("inp1", cl::desc("<input file 1>"),
       cl::init("-"), cl::value_desc("filename"));

static cl::opt<std::string>
Input2("inp2", cl::desc("<input file 2>"),
       cl::init("-"), cl::value_desc("filename"));


int
main (int argc, char ** argv)
{

  llvm_shutdown_obj Y;
  LLVMContext &Context = getGlobalContext();

  SMDiagnostic Err;

  cl::ParseCommandLineOptions(argc, argv,
    "Ironclad verifier\n");


  std::auto_ptr<Module> M1;
  std::auto_ptr<Module> M2;

  M1.reset(ParseIRFile("test1.bc", Err, Context));
  M2.reset(ParseIRFile("test2.bc", Err, Context));

  if(M1.get() == 0){
    Err.Print(argv[0], errs());
  }

  if(M2.get() == 0){
    Err.Print(argv[0], errs());
  }
  
  M1.get()->dump();
  M2.get()->dump();
  
  printf("My verifier\n");
  
  exit (0);
}

