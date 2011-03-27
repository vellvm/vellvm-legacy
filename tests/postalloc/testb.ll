; ModuleID = 'testb.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
@.str = internal constant [4 x i8] c"%d\0A\00"		; <[4 x i8]*> [#uses=1]

define void @test(i32 %mm) nounwind {
entry:
	%0 = icmp sgt i32 %mm, 0		; <i1> [#uses=1]
	br i1 %0, label %bb, label %bb2

bb:		; preds = %bb, %entry
	%i.04 = phi i32 [ 0, %entry ], [ %indvar.next7, %bb ]		; <i32> [#uses=2]
	%arr.05 = phi i32* [ null, %entry ], [ %.sub, %bb ]		; <i32*> [#uses=1]
	%value.03 = phi i32 [ 0, %entry ], [ %3, %bb ]		; <i32> [#uses=1]
	%1 = getelementptr i32* %arr.05, i32 %i.04		; <i32*> [#uses=1]
	%2 = load i32* %1, align 4		; <i32> [#uses=1]
	%3 = add i32 %2, %value.03		; <i32> [#uses=2]
	%4 = malloc [100 x i32]		; <[100 x i32]*> [#uses=1]
	%.sub = getelementptr [100 x i32]* %4, i32 0, i32 0		; <i32*> [#uses=1]
	%indvar.next7 = add i32 %i.04, 1		; <i32> [#uses=2]
	%exitcond8 = icmp eq i32 %indvar.next7, %mm		; <i1> [#uses=1]
	br i1 %exitcond8, label %bb2, label %bb

bb2:		; preds = %bb, %entry
	%value.0.lcssa = phi i32 [ 0, %entry ], [ %3, %bb ]		; <i32> [#uses=1]
	%5 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str, i32 0, i32 0), i32 %value.0.lcssa) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind
