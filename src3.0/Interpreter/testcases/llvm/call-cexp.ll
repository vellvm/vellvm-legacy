; ModuleID = 'test-softbound.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"

define weak void @__callDereferenceCheck(i8* %base, i8* %bound, i8* %ptr) nounwind alwaysinline {
entry:
	tail call void (...)* bitcast (void ()* @__softbound_abort to void (...)*)() noreturn nounwind
	unreachable

return:		; preds = %entry
	ret void
}

define void @__softbound_abort() nounwind {
entry:
	unreachable
}

define i32 @main(i32 %argc, i8** nocapture %argv) nounwind {
entry:
	ret i32 0
}

