; ModuleID = 'testb.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
@.str = internal constant [4 x i8] c"%d\0A\00"		; <[4 x i8]*> [#uses=1]

define void @test(i32 %mm) nounwind {
entry:
	%0 = malloc [10 x i32*]		; <[10 x i32*]*> [#uses=1]
	%1 = malloc [100 x i32]		; <[100 x i32]*> [#uses=1]
	%2 = malloc [50 x i32]		; <[50 x i32]*> [#uses=1]
	%.sub6 = getelementptr [100 x i32]* %1, i32 0, i32 0		; <i32*> [#uses=2]
	%.sub = getelementptr [50 x i32]* %2, i32 0, i32 0		; <i32*> [#uses=1]
	%3 = icmp sgt i32 %mm, 0		; <i1> [#uses=1]
	br i1 %3, label %bb, label %bb5

bb:		; preds = %bb, %entry
	%i.09 = phi i32 [ 0, %entry ], [ %indvar.next13, %bb ]		; <i32> [#uses=3]
	%ptr1.111 = phi i32* [ %.sub6, %entry ], [ %ptr1.0, %bb ]		; <i32*> [#uses=2]
	%value.010 = phi i32 [ 0, %entry ], [ %9, %bb ]		; <i32> [#uses=1]
	%prev.18 = phi i32 [ 0, %entry ], [ %prev.0, %bb ]		; <i32> [#uses=1]
	%4 = load i32* %ptr1.111, align 4		; <i32> [#uses=1]
	%5 = getelementptr [10 x i32*]* %0, i32 0, i32 %i.09		; <i32**> [#uses=2]
	%6 = load i32** %5, align 4		; <i32*> [#uses=1]
	%7 = load i32* %6, align 4		; <i32> [#uses=1]
	%8 = add i32 %4, %value.010		; <i32> [#uses=1]
	%9 = add i32 %8, %7		; <i32> [#uses=4]
	store i32 %9, i32* %ptr1.111, align 4
	%10 = load i32** %5, align 4		; <i32*> [#uses=1]
	store i32 %9, i32* %10, align 4
	%11 = icmp eq i32 %prev.18, 0		; <i1> [#uses=2]
	%prev.0 = zext i1 %11 to i32		; <i32> [#uses=1]
	%.pn = select i1 %11, i32* %.sub, i32* %.sub6		; <i32*> [#uses=1]
	%ptr1.0 = getelementptr i32* %.pn, i32 %i.09		; <i32*> [#uses=1]
	%indvar.next13 = add i32 %i.09, 1		; <i32> [#uses=2]
	%exitcond14 = icmp eq i32 %indvar.next13, %mm		; <i1> [#uses=1]
	br i1 %exitcond14, label %bb5, label %bb

bb5:		; preds = %bb, %entry
	%value.0.lcssa = phi i32 [ 0, %entry ], [ %9, %bb ]		; <i32> [#uses=1]
	%12 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str, i32 0, i32 0), i32 %value.0.lcssa) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind
