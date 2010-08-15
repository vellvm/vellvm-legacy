; ModuleID = 'testb.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
@.str = internal constant [4 x i8] c"%x\0A\00"		; <[4 x i8]*> [#uses=1]

define void @test(i32 %mm) nounwind {
entry:
	%0 = malloc [100 x i32*]		; <[100 x i32*]*> [#uses=1]
	%1 = malloc [100 x i32]		; <[100 x i32]*> [#uses=2]
	%.sub3 = getelementptr [100 x i32*]* %0, i32 0, i32 0		; <i32**> [#uses=2]
	%.sub = getelementptr [100 x i32]* %1, i32 0, i32 0		; <i32*> [#uses=2]
	store i32* %.sub, i32** %.sub3, align 4
	%2 = icmp sgt i32 %mm, 0		; <i1> [#uses=1]
	br i1 %2, label %bb, label %bb2

bb:		; preds = %bb, %entry
	%i.04 = phi i32 [ 0, %entry ], [ %indvar.next5, %bb ]		; <i32> [#uses=2]
	%3 = getelementptr [100 x i32]* %1, i32 0, i32 %i.04		; <i32*> [#uses=2]
	%indvar.next5 = add i32 %i.04, 1		; <i32> [#uses=2]
	%exitcond6 = icmp eq i32 %indvar.next5, %mm		; <i1> [#uses=1]
	br i1 %exitcond6, label %bb1.bb2_crit_edge, label %bb

bb1.bb2_crit_edge:		; preds = %bb
	store i32* %3, i32** %.sub3
	br label %bb2

bb2:		; preds = %bb1.bb2_crit_edge, %entry
	%4 = phi i32* [ %3, %bb1.bb2_crit_edge ], [ %.sub, %entry ]		; <i32*> [#uses=1]
	%5 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str, i32 0, i32 0), i32* %4) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind
