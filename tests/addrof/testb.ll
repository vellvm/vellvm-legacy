; ModuleID = 'testb.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
@.str = internal constant [4 x i8] c"%d\0A\00"		; <[4 x i8]*> [#uses=1]

define void @test(i32) nounwind {
entry:
	%mm_addr = alloca i32, align 4		; <i32*> [#uses=2]
	%value = alloca i32, align 4		; <i32*> [#uses=3]
	store i32 %0, i32* %mm_addr
	store i32 0, i32* %value, align 4
	%1 = srem i32 %0, 3		; <i32> [#uses=1]
	%2 = icmp eq i32 %1, 0		; <i1> [#uses=1]
	%ptr.0.ph = select i1 %2, i32* %value, i32* %mm_addr		; <i32*> [#uses=1]
	%3 = icmp sgt i32 %0, 0		; <i1> [#uses=1]
	br i1 %3, label %bb2, label %bb4

bb2:		; preds = %bb2, %entry
	%i.06 = phi i32 [ 0, %entry ], [ %8, %bb2 ]		; <i32> [#uses=2]
	%4 = phi i32 [ 0, %entry ], [ %7, %bb2 ]		; <i32> [#uses=1]
	%ptr.05.rec = phi i32 [ 0, %entry ], [ %.rec, %bb2 ]		; <i32> [#uses=2]
	%ptr.05.sum = add i32 %ptr.05.rec, %i.06		; <i32> [#uses=1]
	%5 = getelementptr i32* %ptr.0.ph, i32 %ptr.05.sum		; <i32*> [#uses=1]
	%6 = load i32* %5, align 4		; <i32> [#uses=1]
	%7 = add i32 %6, %4		; <i32> [#uses=3]
	store i32 %7, i32* %value, align 4
	%8 = add i32 %i.06, 1		; <i32> [#uses=3]
	%.rec = add i32 %ptr.05.rec, %8		; <i32> [#uses=1]
	%exitcond = icmp eq i32 %8, %0		; <i1> [#uses=1]
	br i1 %exitcond, label %bb4, label %bb2

bb4:		; preds = %bb2, %entry
	%9 = phi i32 [ 0, %entry ], [ %7, %bb2 ]		; <i32> [#uses=1]
	%10 = call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str, i32 0, i32 0), i32 %9) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind
