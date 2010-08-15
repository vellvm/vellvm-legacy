; ModuleID = 'testa.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"

define i32 @main(i32 %argc, i8** nocapture %argv) nounwind {
entry:
	%0 = getelementptr i8** %argv, i32 1		; <i8**> [#uses=1]
	%1 = load i8** %0, align 4		; <i8*> [#uses=1]
	%2 = tail call i32 @atoi(i8* %1) nounwind readonly		; <i32> [#uses=1]
	tail call void @test(i32 %2) nounwind
	ret i32 0
}

declare i32 @atoi(i8*) nounwind readonly

declare void @test(i32)
