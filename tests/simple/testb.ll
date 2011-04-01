; ModuleID = 'testb.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
@.str = internal constant [4 x i8] c"%d\0A\00"		; <[4 x i8]*> [#uses=1]

define void @test(i32 %mm) nounwind {
entry:
	%0 = malloc [10 x i32]		; <[10 x i32]*> [#uses=2]
	%.sub = getelementptr [10 x i32]* %0, i32 0, i32 0		; <i32*> [#uses=1]
	%1 = getelementptr [10 x i32]* %0, i32 0, i32 %mm		; <i32*> [#uses=1]
	store i32 42, i32* %1, align 4
	%2 = load i32* %.sub, align 4		; <i32> [#uses=1]
	%3 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str, i32 0, i32 0), i32 %2) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind
