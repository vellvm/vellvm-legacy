; ModuleID = '/home/jianzhou/Download/llvm-2.6z-obj/projects/test-suite/SingleSource/Benchmarks/Misc/Output/fbench.llvm.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"

; sext should not change the bitwidth of %0

define i32 @main() nounwind {
entry:
  %0 = add i16 0, 0
  %1 = sext i16 %0 to i32
  %2 = add i16 %0, 1    

  ret i32 0
}

