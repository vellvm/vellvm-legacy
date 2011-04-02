; ModuleID = 'testb.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
@.str = internal constant [4 x i8] c"%x\0A\00"		; <[4 x i8]*> [#uses=1]

define void @test(i32 %mm) nounwind {
entry:
	%0 = malloc [100 x i32]		; <[100 x i32]*> [#uses=2]
	%.sub = getelementptr [100 x i32]* %0, i32 0, i32 0		; <i32*> [#uses=1]
	%1 = getelementptr [100 x i32]* %0, i32 0, i32 %mm		; <i32*> [#uses=1]
	store i32 42, i32* %1, align 4
	%2 = icmp sgt i32 %mm, 0		; <i1> [#uses=1]
	br i1 %2, label %bb, label %bb2

bb:		; preds = %bb, %entry
	%i.03 = phi i32 [ 0, %entry ], [ %indvar.next7, %bb ]		; <i32> [#uses=2]
	%ptr.05 = phi i32* [ %.sub, %entry ], [ %5, %bb ]		; <i32*> [#uses=1]
	%value.04 = phi i32 [ 0, %entry ], [ %4, %bb ]		; <i32> [#uses=1]
	%3 = load i32* %ptr.05, align 4		; <i32> [#uses=1]
	%4 = add i32 %3, %value.04		; <i32> [#uses=2]
	%5 = malloc i32, i32 %mm		; <i32*> [#uses=2]
	%6 = getelementptr i32* %5, i32 %i.03		; <i32*> [#uses=1]
	store i32 42, i32* %6, align 4
	%indvar.next7 = add i32 %i.03, 1		; <i32> [#uses=2]
	%exitcond8 = icmp eq i32 %indvar.next7, %mm		; <i1> [#uses=1]
	br i1 %exitcond8, label %bb2, label %bb

bb2:		; preds = %bb, %entry
	%value.0.lcssa = phi i32 [ 0, %entry ], [ %4, %bb ]		; <i32> [#uses=1]
	%7 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str, i32 0, i32 0), i32 %value.0.lcssa) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind
