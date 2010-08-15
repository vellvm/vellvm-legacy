; ModuleID = 'testb.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
@.str = internal constant [4 x i8] c"%x\0A\00"		; <[4 x i8]*> [#uses=1]

define void @test(i32 %mm) nounwind {
entry:
	%0 = malloc [100 x i32*]		; <[100 x i32*]*> [#uses=1]
	br label %bb2

bb:		; preds = %bb2
	%1 = getelementptr [100 x i32*]* %0, i32 0, i32 %i.0		; <i32**> [#uses=1]
	%2 = load i32** %1, align 4		; <i32*> [#uses=3]
	%3 = load i32* %2, align 4		; <i32> [#uses=1]
	%4 = icmp slt i32 %3, %i.0		; <i1> [#uses=1]
	br i1 %4, label %bb3, label %bb1

bb1:		; preds = %bb
	%indvar.next4 = add i32 %i.0, 1		; <i32> [#uses=1]
	br label %bb2

bb2:		; preds = %bb1, %entry
	%i.0 = phi i32 [ 0, %entry ], [ %indvar.next4, %bb1 ]		; <i32> [#uses=4]
	%ptr.0 = phi i32* [ undef, %entry ], [ %2, %bb1 ]		; <i32*> [#uses=1]
	%5 = icmp slt i32 %i.0, %mm		; <i1> [#uses=1]
	br i1 %5, label %bb, label %bb3

bb3:		; preds = %bb2, %bb
	%ptr.1 = phi i32* [ %2, %bb ], [ %ptr.0, %bb2 ]		; <i32*> [#uses=1]
	%6 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str, i32 0, i32 0), i32* %ptr.1) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind
