
#include "verifier.h"
#include<stdio.h>

#include "llvm/LLVMContext.h"
#include "llvm/Module.h"
#include "llvm/ModuleProvider.h"
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
#include "llvm/Support/ManagedStatic.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/PluginLoader.h"
#include "llvm/Support/StandardPasses.h"
#include "llvm/Support/SystemUtils.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/LinkAllPasses.h"
#include "llvm/LinkAllVMCore.h"
#include "llvm/OCamlPass/OCamlPass.h"
#include <memory>
#include <algorithm>
using namespace llvm;

#ifdef LLVM_27
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
#endif

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

#ifdef LLVM_27
  SMDiagnostic Err;
#else
  std::string Err;
#endif

  cl::ParseCommandLineOptions(argc, argv,
    "Ironclad verifier\n");


  std::auto_ptr<Module> M1;
  std::auto_ptr<Module> M2;

  MemoryBuffer* buffer1 = MemoryBuffer::getFileOrSTDIN("test1.bc", &Err);
  MemoryBuffer* buffer2 = MemoryBuffer::getFileOrSTDIN("test2.bc", &Err);
  
  if(buffer1 != NULL && buffer2 != NULL){

    M1.reset(ParseBitcodeFile(buffer1, Context, &Err));
    M2.reset(ParseBitcodeFile(buffer2, Context, &Err));
    
    delete buffer1;
    delete buffer2;
  }

  if(M1.get() == 0){
    //    Err.Print(argv[0], errs());
  }

  if(M2.get() == 0){
    //    Err.Print(argv[0], errs());
  }
  
  M1.get()->dump();
  M2.get()->dump();
  
  printf("My verifier\n");
  
  exit (0);
}

