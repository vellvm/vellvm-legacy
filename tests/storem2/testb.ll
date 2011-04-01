; ModuleID = 'testb.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
@.str = internal constant [4 x i8] c"%x\0A\00"		; <[4 x i8]*> [#uses=1]

define void @test(i32 %mm) nounwind {
entry:
	%0 = malloc [100 x i32*]		; <[100 x i32*]*> [#uses=1]
	%1 = malloc [100 x i32]		; <[100 x i32]*> [#uses=3]
	%.sub6 = getelementptr [100 x i32*]* %0, i32 0, i32 0		; <i32**> [#uses=2]
	%.sub5 = getelementptr [100 x i32]* %1, i32 0, i32 0		; <i32*> [#uses=2]
	store i32* %.sub5, i32** %.sub6, align 4
	br label %bb3

bb:		; preds = %bb3
	%2 = getelementptr [100 x i32]* %1, i32 0, i32 %i.0		; <i32*> [#uses=1]
	store i32* %2, i32** %arr1.1, align 4
	%3 = add i32 %i.0, 1		; <i32> [#uses=4]
	%4 = malloc [100 x i32*]		; <[100 x i32*]*> [#uses=1]
	%.sub = getelementptr [100 x i32*]* %4, i32 0, i32 0		; <i32**> [#uses=2]
	%5 = getelementptr [100 x i32]* %1, i32 0, i32 %3		; <i32*> [#uses=2]
	store i32* %5, i32** %.sub, align 4
	%6 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str, i32 0, i32 0), i32* %5) nounwind		; <i32> [#uses=0]
	%7 = and i32 %3, 1		; <i32> [#uses=1]
	%toBool = icmp eq i32 %7, 0		; <i1> [#uses=1]
	%arr1.0 = select i1 %toBool, i32** %arr1.1, i32** %.sub		; <i32**> [#uses=2]
	%8 = load i32* %.sub5, align 4		; <i32> [#uses=1]
	%9 = icmp slt i32 %8, %3		; <i1> [#uses=1]
	br i1 %9, label %bb4, label %bb3

bb3:		; preds = %bb, %entry
	%i.0 = phi i32 [ 0, %entry ], [ %3, %bb ]		; <i32> [#uses=3]
	%arr1.1 = phi i32** [ %.sub6, %entry ], [ %arr1.0, %bb ]		; <i32**> [#uses=3]
	%10 = icmp slt i32 %i.0, %mm		; <i1> [#uses=1]
	br i1 %10, label %bb, label %bb4

bb4:		; preds = %bb3, %bb
	%arr1.2 = phi i32** [ %arr1.0, %bb ], [ %arr1.1, %bb3 ]		; <i32**> [#uses=1]
	%11 = load i32** %arr1.2, align 4		; <i32*> [#uses=1]
	%12 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str, i32 0, i32 0), i32* %11) nounwind		; <i32> [#uses=0]
	ret void
}

declare i32 @printf(i8*, ...) nounwind
