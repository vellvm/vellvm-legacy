; ModuleID = 'testb.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
@.str = internal constant [4 x i8] c"%x\0A\00"		; <[4 x i8]*> [#uses=1]

define void @test(i32 %mm) nounwind {
entry:
	%0 = malloc [100 x i32*]		; <[100 x i32*]*> [#uses=1]
	%.sub8 = getelementptr [100 x i32*]* %0, i32 0, i32 0		; <i32**> [#uses=1]
	%1 = add i32 %mm, 1		; <i32> [#uses=2]
	br label %bb6

bb:		; preds = %bb6
	%2 = malloc [100 x i32*]		; <[100 x i32*]*> [#uses=2]
	%.sub = getelementptr [100 x i32*]* %2, i32 0, i32 0		; <i32**> [#uses=1]
	%3 = icmp sgt i32 %1, %i.1		; <i1> [#uses=1]
	br i1 %3, label %bb.nph, label %bb3

bb.nph:		; preds = %bb
	%i.010 = add i32 %i.1, 1		; <i32> [#uses=1]
	%tmp20 = sub i32 %mm, %i.1		; <i32> [#uses=1]
	%tmp21 = add i32 %tmp20, 1		; <i32> [#uses=1]
	br label %bb1

bb1:		; preds = %bb1, %bb.nph
	%indvar = phi i32 [ 0, %bb.nph ], [ %indvar.next19, %bb1 ]		; <i32> [#uses=2]
	%.sum = add i32 %i.010, %indvar		; <i32> [#uses=1]
	%4 = getelementptr [100 x i32*]* %2, i32 0, i32 %.sum		; <i32**> [#uses=1]
	%5 = load i32** %4, align 4		; <i32*> [#uses=1]
	%indvar.next19 = add i32 %indvar, 1		; <i32> [#uses=2]
	%exitcond22 = icmp eq i32 %indvar.next19, %tmp21		; <i1> [#uses=1]
	br i1 %exitcond22, label %bb3, label %bb1

bb3:		; preds = %bb1, %bb
	%i.0.lcssa = phi i32 [ %i.1, %bb ], [ %1, %bb1 ]		; <i32> [#uses=2]
	%ptr2.0.lcssa = phi i32* [ %ptr2.1, %bb ], [ %5, %bb1 ]		; <i32*> [#uses=2]
	%6 = getelementptr i32** %arr1.1, i32 %i.0.lcssa		; <i32**> [#uses=1]
	%7 = load i32** %6, align 4		; <i32*> [#uses=3]
	%8 = add i32 %i.0.lcssa, 1		; <i32> [#uses=3]
	%9 = and i32 %8, 1		; <i32> [#uses=1]
	%toBool = icmp eq i32 %9, 0		; <i1> [#uses=1]
	%arr1.0 = select i1 %toBool, i32** %arr1.1, i32** %.sub		; <i32**> [#uses=1]
	%10 = load i32* %7, align 4		; <i32> [#uses=1]
	%11 = icmp slt i32 %10, %8		; <i1> [#uses=1]
	br i1 %11, label %bb7, label %bb6

bb6:		; preds = %bb3, %entry
	%ptr2.1 = phi i32* [ undef, %entry ], [ %ptr2.0.lcssa, %bb3 ]		; <i32*> [#uses=2]
	%i.1 = phi i32 [ 0, %entry ], [ %8, %bb3 ]		; <i32> [#uses=5]
	%ptr1.0 = phi i32* [ undef, %entry ], [ %7, %bb3 ]		; <i32*> [#uses=1]
	%arr1.1 = phi i32** [ %.sub8, %entry ], [ %arr1.0, %bb3 ]		; <i32**> [#uses=2]
	%12 = icmp slt i32 %i.1, %mm		; <i1> [#uses=1]
	br i1 %12, label %bb, label %bb7

bb7:		; preds = %bb6, %bb3
	%ptr2.2 = phi i32* [ %ptr2.0.lcssa, %bb3 ], [ %ptr2.1, %bb6 ]		; <i32*> [#uses=1]
	%ptr1.1 = phi i32* [ %7, %bb3 ], [ %ptr1.0, %bb6 ]		; <i32*> [#uses=1]
	%13 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str, i32 0, i32 0), i32* %ptr1.1) nounwind		; <i32> [#uses=0]
	%14 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str, i32 0, i32 0), i32* %ptr2.2) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind
