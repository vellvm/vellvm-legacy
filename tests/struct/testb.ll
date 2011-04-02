; ModuleID = 'testb.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
	%struct.A = type { [99 x i32], i32 }
@.str = internal constant [4 x i8] c"%d\0A\00"		; <[4 x i8]*> [#uses=1]

define void @test(i32 %mm) nounwind {
entry:
	%value2 = alloca [42 x %struct.A], align 8		; <[42 x %struct.A]*> [#uses=2]
	%value1 = alloca [42 x %struct.A], align 8		; <[42 x %struct.A]*> [#uses=2]
	%0 = getelementptr [42 x %struct.A]* %value1, i32 0, i32 0, i32 1		; <i32*> [#uses=1]
	store i32 42, i32* %0, align 4
	%1 = icmp sgt i32 %mm, 0		; <i1> [#uses=1]
	br i1 %1, label %bb.nph, label %bb4

bb.nph:		; preds = %entry
	%2 = getelementptr [42 x %struct.A]* %value2, i32 0, i32 0, i32 1		; <i32*> [#uses=1]
	br label %bb

bb:		; preds = %bb, %bb.nph
	%i.05 = phi i32 [ 0, %bb.nph ], [ %3, %bb ]		; <i32> [#uses=1]
	%value1.pn7 = phi [42 x %struct.A]* [ %value1, %bb.nph ], [ %value2, %bb ]		; <[42 x %struct.A]*> [#uses=2]
	%sum.06 = phi i32 [ 0, %bb.nph ], [ %9, %bb ]		; <i32> [#uses=1]
	store i32 42, i32* %2, align 4
	%3 = add i32 %i.05, 1		; <i32> [#uses=5]
	%4 = getelementptr [42 x %struct.A]* %value1.pn7, i32 0, i32 %3, i32 0, i32 %3		; <i32*> [#uses=1]
	%5 = load i32* %4, align 4		; <i32> [#uses=1]
	%6 = getelementptr [42 x %struct.A]* %value1.pn7, i32 0, i32 %3, i32 1		; <i32*> [#uses=1]
	%7 = load i32* %6, align 4		; <i32> [#uses=1]
	%8 = add i32 %5, %sum.06		; <i32> [#uses=1]
	%9 = add i32 %8, %7		; <i32> [#uses=2]
	%exitcond9 = icmp eq i32 %3, %mm		; <i1> [#uses=1]
	br i1 %exitcond9, label %bb4, label %bb

bb4:		; preds = %bb, %entry
	%sum.0.lcssa = phi i32 [ 0, %entry ], [ %9, %bb ]		; <i32> [#uses=1]
	%10 = call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str, i32 0, i32 0), i32 %sum.0.lcssa) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind
