; ModuleID = 'testb.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
@.str = internal constant [4 x i8] c"%x\0A\00"		; <[4 x i8]*> [#uses=1]

define void @test(i32 %mm) nounwind {
entry:
	%0 = malloc [100 x i32]		; <[100 x i32]*> [#uses=2]
	%.sub = getelementptr [100 x i32]* %0, i32 0, i32 0		; <i32*> [#uses=2]
	%1 = icmp sgt i32 %mm, 0		; <i1> [#uses=1]
	br i1 %1, label %bb, label %bb2

bb:		; preds = %bb, %entry
	%i.03 = phi i32 [ 0, %entry ], [ %3, %bb ]		; <i32> [#uses=2]
	%ptr.04 = phi i32* [ %.sub, %entry ], [ %4, %bb ]		; <i32*> [#uses=1]
	%2 = getelementptr i32* %ptr.04, i32 %i.03		; <i32*> [#uses=1]
	store i32 0, i32* %2, align 4
	%3 = add i32 %i.03, 1		; <i32> [#uses=3]
	%4 = getelementptr [100 x i32]* %0, i32 0, i32 %3		; <i32*> [#uses=2]
	%exitcond6 = icmp eq i32 %3, %mm		; <i1> [#uses=1]
	br i1 %exitcond6, label %bb2, label %bb

bb2:		; preds = %bb, %entry
	%ptr.0.lcssa = phi i32* [ %.sub, %entry ], [ %4, %bb ]		; <i32*> [#uses=1]
	%5 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str, i32 0, i32 0), i32* %ptr.0.lcssa) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind
