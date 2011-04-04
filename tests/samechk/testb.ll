; ModuleID = 'testb.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
@.str = internal constant [4 x i8] c"%d\0A\00"		; <[4 x i8]*> [#uses=1]

define void @test(i32 %mm) nounwind {
entry:
	%value = alloca i32, align 4		; <i32*> [#uses=7]
	store i32 %mm, i32* %value, align 4
	%0 = icmp sgt i32 %mm, 0		; <i1> [#uses=1]
	br i1 %0, label %bb, label %bb2

bb:		; preds = %bb, %entry
	%indvar = phi i32 [ 0, %entry ], [ %indvar.next8, %bb ]		; <i32> [#uses=2]
	%1 = phi i32 [ %mm, %entry ], [ %12, %bb ]		; <i32> [#uses=1]
	%ptr.04.rec = phi i32 [ 0, %entry ], [ %.rec, %bb ]		; <i32> [#uses=4]
	%i.03 = mul i32 %indvar, 3		; <i32> [#uses=4]
	%ptr.04.sum6 = add i32 %ptr.04.rec, %i.03		; <i32> [#uses=1]
	%2 = getelementptr i32* %value, i32 %ptr.04.sum6		; <i32*> [#uses=1]
	%3 = load i32* %2, align 4		; <i32> [#uses=1]
	%4 = add i32 %3, %1		; <i32> [#uses=2]
	store i32 %4, i32* %value, align 4
	%5 = add i32 %ptr.04.rec, 1		; <i32> [#uses=1]
	%ptr.04.sum5 = add i32 %5, %i.03		; <i32> [#uses=1]
	%6 = getelementptr i32* %value, i32 %ptr.04.sum5		; <i32*> [#uses=1]
	%7 = load i32* %6, align 4		; <i32> [#uses=1]
	%8 = add i32 %7, %4		; <i32> [#uses=2]
	store i32 %8, i32* %value, align 4
	%9 = add i32 %ptr.04.rec, 2		; <i32> [#uses=1]
	%ptr.04.sum = add i32 %9, %i.03		; <i32> [#uses=1]
	%10 = getelementptr i32* %value, i32 %ptr.04.sum		; <i32*> [#uses=1]
	%11 = load i32* %10, align 4		; <i32> [#uses=1]
	%12 = add i32 %11, %8		; <i32> [#uses=3]
	store i32 %12, i32* %value, align 4
	%13 = add i32 %i.03, 3		; <i32> [#uses=2]
	%.rec = add i32 %13, %ptr.04.rec		; <i32> [#uses=1]
	%14 = icmp slt i32 %13, %mm		; <i1> [#uses=1]
	%indvar.next8 = add i32 %indvar, 1		; <i32> [#uses=1]
	br i1 %14, label %bb, label %bb2

bb2:		; preds = %bb, %entry
	%15 = phi i32 [ %mm, %entry ], [ %12, %bb ]		; <i32> [#uses=1]
	%16 = call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str, i32 0, i32 0), i32 %15) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind
