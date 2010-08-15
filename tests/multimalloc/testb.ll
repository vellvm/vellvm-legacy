; ModuleID = 'testb.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
@.str = internal constant [4 x i8] c"%x\0A\00"		; <[4 x i8]*> [#uses=1]

define void @test(i32 %mm) nounwind {
entry:
	%0 = malloc [400 x i8]		; <[400 x i8]*> [#uses=1]
	%.sub = getelementptr [400 x i8]* %0, i32 0, i32 0		; <i8*> [#uses=1]
	%1 = icmp sgt i32 %mm, 0		; <i1> [#uses=1]
	br i1 %1, label %bb.nph, label %bb2

bb.nph:		; preds = %entry
	%2 = shl i32 %mm, 2		; <i32> [#uses=1]
	br label %bb

bb:		; preds = %bb, %bb.nph
	%i.03 = phi i32 [ 0, %bb.nph ], [ %indvar.next7, %bb ]		; <i32> [#uses=1]
	%ptr.0.in5 = phi i8* [ %.sub, %bb.nph ], [ %5, %bb ]		; <i8*> [#uses=2]
	%value.04 = phi i32 [ 0, %bb.nph ], [ %4, %bb ]		; <i32> [#uses=1]
	%ptr.0 = bitcast i8* %ptr.0.in5 to i32*		; <i32*> [#uses=1]
	%3 = load i32* %ptr.0, align 4		; <i32> [#uses=1]
	%4 = add i32 %3, %value.04		; <i32> [#uses=2]
	free i8* %ptr.0.in5
	%5 = malloc i8, i32 %2		; <i8*> [#uses=1]
	%indvar.next7 = add i32 %i.03, 1		; <i32> [#uses=2]
	%exitcond8 = icmp eq i32 %indvar.next7, %mm		; <i1> [#uses=1]
	br i1 %exitcond8, label %bb2, label %bb

bb2:		; preds = %bb, %entry
	%value.0.lcssa = phi i32 [ 0, %entry ], [ %4, %bb ]		; <i32> [#uses=1]
	%6 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str, i32 0, i32 0), i32 %value.0.lcssa) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind
