; ModuleID = 'testb.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"

define void @test(i32 %mm) nounwind {
entry:
	%arr1 = alloca i32, align 4		; <i32*> [#uses=1]
	free i32* %arr1
	ret void
}
