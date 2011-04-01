; ModuleID = 'test-instrumented.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-pc-linux-gnu"
	%struct.__softbound_hash_table_entry_t = type { i8*, i8*, i8* }
@__softbound_hash_table_begin = external global %struct.__softbound_hash_table_entry_t*		; <%struct.__softbound_hash_table_entry_t**> [#uses=3]
@.str = internal constant [17 x i8] c"Hash table full\0A\00"		; <[17 x i8]*> [#uses=1]
@llvm.global_ctors = appending global [1 x { i32, void ()* }] [ { i32, void ()* } { i32 65535, void ()* @__softbound_global_init } ]		; <[1 x { i32, void ()* }]*> [#uses=0]
@value = common global i32* null		; <i32**> [#uses=3]
@.str1 = internal constant [4 x i8] c"%d\0A\00"		; <[4 x i8]*> [#uses=1]

define weak void @__shrinkBounds(i8* %new_base, i8* %new_bound, i8* %old_base, i8* %old_bound, i8** %base_alloca, i8** %bound_alloca) nounwind alwaysinline {
entry:
	%0 = icmp uge i8* %new_base, %old_base		; <i1> [#uses=1]
	%max = select i1 %0, i8* %new_base, i8* %old_base		; <i8*> [#uses=1]
	store i8* %max, i8** %base_alloca, align 4
	%1 = icmp ule i8* %new_bound, %old_bound		; <i1> [#uses=1]
	%min = select i1 %1, i8* %new_bound, i8* %old_bound		; <i8*> [#uses=1]
	store i8* %min, i8** %bound_alloca, align 4
	ret void
}

define weak void @__callDereferenceCheck(i8* %base, i8* %bound, i8* %ptr) nounwind alwaysinline {
entry:
	%0 = icmp ne i8* %base, %bound		; <i1> [#uses=1]
	%1 = icmp ne i8* %ptr, %base		; <i1> [#uses=1]
	%2 = and i1 %1, %0		; <i1> [#uses=1]
	br i1 %2, label %bb, label %return

bb:		; preds = %entry
	tail call void (...)* @__softbound_abort() noreturn nounwind
	unreachable

return:		; preds = %entry
	ret void
}

define weak void @__loadDereferenceCheck(i8* %base, i8* %bound, i8* %ptr, i32 %size_of_type, i32 %ptr_safe) nounwind alwaysinline {
entry:
	%0 = icmp ult i8* %ptr, %base		; <i1> [#uses=1]
	br i1 %0, label %bb1, label %bb

bb:		; preds = %entry
	%1 = getelementptr i8* %ptr, i32 %size_of_type		; <i8*> [#uses=1]
	%2 = icmp ugt i8* %1, %bound		; <i1> [#uses=1]
	br i1 %2, label %bb1, label %return

bb1:		; preds = %bb, %entry
	tail call void (...)* @__softbound_abort() noreturn nounwind
	unreachable

return:		; preds = %bb
	ret void
}

define weak void @__storeDereferenceCheck(i8* %base, i8* %bound, i8* %ptr, i32 %size_of_type, i32 %ptr_safe) nounwind alwaysinline {
entry:
	%0 = icmp ult i8* %ptr, %base		; <i1> [#uses=1]
	br i1 %0, label %bb1, label %bb

bb:		; preds = %entry
	%1 = getelementptr i8* %ptr, i32 %size_of_type		; <i8*> [#uses=1]
	%2 = icmp ugt i8* %1, %bound		; <i1> [#uses=1]
	br i1 %2, label %bb1, label %return

bb1:		; preds = %bb, %entry
	tail call void (...)* @__softbound_abort() noreturn nounwind
	unreachable

return:		; preds = %bb
	ret void
}

define weak void @__memcopyCheck_i64(i8* %ptr, i8* %ptr_base, i8* %ptr_bound, i32 %size) nounwind alwaysinline {
entry:
	%0 = icmp ugt i32 %size, -2147483648		; <i1> [#uses=1]
	br i1 %0, label %bb, label %bb1

bb:		; preds = %entry
	tail call void (...)* @__softbound_abort() noreturn nounwind
	unreachable

bb1:		; preds = %entry
	%1 = icmp ult i8* %ptr, %ptr_base		; <i1> [#uses=1]
	br i1 %1, label %bb6, label %bb2

bb2:		; preds = %bb1
	%2 = getelementptr i8* %ptr, i32 %size		; <i8*> [#uses=2]
	%3 = icmp ult i8* %2, %ptr_base		; <i1> [#uses=1]
	br i1 %3, label %bb6, label %bb3

bb3:		; preds = %bb2
	%4 = icmp ugt i8* %2, %ptr_bound		; <i1> [#uses=1]
	%5 = inttoptr i32 %size to i8*		; <i8*> [#uses=1]
	%6 = icmp ugt i8* %5, %ptr_bound		; <i1> [#uses=1]
	%7 = or i1 %4, %6		; <i1> [#uses=1]
	br i1 %7, label %bb6, label %return

bb6:		; preds = %bb3, %bb2, %bb1
	tail call void (...)* @__softbound_abort() noreturn nounwind
	unreachable

return:		; preds = %bb3
	ret void
}

define weak void @__memcopyCheck(i8* %ptr, i8* %ptr_base, i8* %ptr_bound, i32 %size) nounwind alwaysinline {
entry:
	%0 = icmp ugt i32 %size, -2147483648		; <i1> [#uses=1]
	br i1 %0, label %bb, label %bb1

bb:		; preds = %entry
	tail call void (...)* @__softbound_abort() noreturn nounwind
	unreachable

bb1:		; preds = %entry
	%1 = icmp ult i8* %ptr, %ptr_base		; <i1> [#uses=1]
	br i1 %1, label %bb6, label %bb2

bb2:		; preds = %bb1
	%2 = getelementptr i8* %ptr, i32 %size		; <i8*> [#uses=2]
	%3 = icmp ult i8* %2, %ptr_base		; <i1> [#uses=1]
	br i1 %3, label %bb6, label %bb3

bb3:		; preds = %bb2
	%4 = icmp ugt i8* %2, %ptr_bound		; <i1> [#uses=1]
	%5 = inttoptr i32 %size to i8*		; <i8*> [#uses=1]
	%6 = icmp ugt i8* %5, %ptr_bound		; <i1> [#uses=1]
	%7 = or i1 %4, %6		; <i1> [#uses=1]
	br i1 %7, label %bb6, label %return

bb6:		; preds = %bb3, %bb2, %bb1
	tail call void (...)* @__softbound_abort() noreturn nounwind
	unreachable

return:		; preds = %bb3
	ret void
}

define weak void @__hashStoreBaseBound(i8* %addr_of_ptr, i8* %base, i8* %bound, i8* %actual_ptr, i32 %size_of_type, i32 %ptr_safe) nounwind alwaysinline {
entry:
	%0 = ptrtoint i8* %addr_of_ptr to i32		; <i32> [#uses=1]
	%1 = lshr i32 %0, 2		; <i32> [#uses=1]
	%2 = load %struct.__softbound_hash_table_entry_t** @__softbound_hash_table_begin, align 4		; <%struct.__softbound_hash_table_entry_t*> [#uses=3]
	br label %bb

bb:		; preds = %bb8, %entry
	%counter.0 = phi i32 [ 0, %entry ], [ %indvar.next19, %bb8 ]		; <i32> [#uses=3]
	%3 = add i32 %counter.0, %1		; <i32> [#uses=1]
	%4 = and i32 %3, 134217727		; <i32> [#uses=3]
	%5 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 2		; <i8**> [#uses=2]
	%6 = load i8** %5, align 4		; <i8*> [#uses=2]
	%7 = icmp eq i8* %6, %addr_of_ptr		; <i1> [#uses=1]
	%8 = icmp eq i8* %6, null		; <i1> [#uses=1]
	%9 = or i1 %7, %8		; <i1> [#uses=1]
	br i1 %9, label %bb3, label %bb6

bb3:		; preds = %bb
	%10 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 0		; <i8**> [#uses=1]
	store i8* %base, i8** %10, align 4
	%11 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 1		; <i8**> [#uses=1]
	store i8* %bound, i8** %11, align 4
	store i8* %addr_of_ptr, i8** %5, align 4
	ret void

bb6:		; preds = %bb
	%12 = icmp ugt i32 %counter.0, 134217727		; <i1> [#uses=1]
	br i1 %12, label %bb7, label %bb8

bb7:		; preds = %bb6
	tail call void (i8*, ...)* @__softbound_printf(i8* getelementptr ([17 x i8]* @.str, i32 0, i32 0)) nounwind
	tail call void (...)* @__softbound_abort() noreturn nounwind
	unreachable

bb8:		; preds = %bb6
	%indvar.next19 = add i32 %counter.0, 1		; <i32> [#uses=1]
	br label %bb
}

define weak i32 @__hashProbeAddrOfPtr(i8* %addr_of_ptr, i8** %base, i8** %bound) nounwind alwaysinline {
entry:
	%0 = ptrtoint i8* %addr_of_ptr to i32		; <i32> [#uses=1]
	%1 = lshr i32 %0, 2		; <i32> [#uses=1]
	%2 = load %struct.__softbound_hash_table_entry_t** @__softbound_hash_table_begin, align 4		; <%struct.__softbound_hash_table_entry_t*> [#uses=3]
	br label %bb

bb:		; preds = %bb6, %entry
	%counter.0 = phi i32 [ 0, %entry ], [ %indvar.next15, %bb6 ]		; <i32> [#uses=2]
	%3 = add i32 %counter.0, %1		; <i32> [#uses=1]
	%4 = and i32 %3, 134217727		; <i32> [#uses=3]
	%5 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 2		; <i8**> [#uses=1]
	%6 = load i8** %5, align 4		; <i8*> [#uses=2]
	%7 = icmp eq i8* %6, %addr_of_ptr		; <i1> [#uses=1]
	br i1 %7, label %bb1, label %bb4

bb1:		; preds = %bb
	%8 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 0		; <i8**> [#uses=1]
	%9 = load i8** %8, align 4		; <i8*> [#uses=2]
	%10 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 1		; <i8**> [#uses=1]
	%11 = load i8** %10, align 4		; <i8*> [#uses=2]
	store i8* %9, i8** %base, align 4
	store i8* %11, i8** %bound, align 4
	%12 = ptrtoint i8* %9 to i32		; <i32> [#uses=1]
	%13 = ptrtoint i8* %11 to i32		; <i32> [#uses=1]
	%14 = or i32 %13, %12		; <i32> [#uses=1]
	%15 = inttoptr i32 %14 to i8*		; <i8*> [#uses=1]
	%not. = icmp ne i8* %15, null		; <i1> [#uses=1]
	%retval = zext i1 %not. to i32		; <i32> [#uses=1]
	ret i32 %retval

bb4:		; preds = %bb
	%16 = icmp eq i8* %6, null		; <i1> [#uses=1]
	br i1 %16, label %bb7, label %bb6

bb6:		; preds = %bb4
	%indvar.next15 = add i32 %counter.0, 1		; <i32> [#uses=1]
	br label %bb

bb7:		; preds = %bb4
	ret i32 0
}

define weak void @__hashLoadBaseBound(i8* %addr_of_ptr, i8** %base, i8** %bound, i8* %actual_ptr, i32 %size_of_type, i32* %ptr_safe) nounwind alwaysinline {
entry:
	%0 = ptrtoint i8* %addr_of_ptr to i32		; <i32> [#uses=1]
	%1 = lshr i32 %0, 2		; <i32> [#uses=1]
	%2 = load %struct.__softbound_hash_table_entry_t** @__softbound_hash_table_begin, align 4		; <%struct.__softbound_hash_table_entry_t*> [#uses=3]
	br label %bb

bb:		; preds = %bb2, %entry
	%counter.0 = phi i32 [ 0, %entry ], [ %7, %bb2 ]		; <i32> [#uses=2]
	%3 = add i32 %counter.0, %1		; <i32> [#uses=1]
	%4 = and i32 %3, 134217727		; <i32> [#uses=3]
	%5 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 2		; <i8**> [#uses=1]
	%6 = load i8** %5, align 4		; <i8*> [#uses=2]
	%7 = add i32 %counter.0, 1		; <i32> [#uses=2]
	%8 = icmp eq i8* %6, %addr_of_ptr		; <i1> [#uses=1]
	br i1 %8, label %bb1, label %bb2

bb1:		; preds = %bb
	%9 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 0		; <i8**> [#uses=1]
	%10 = load i8** %9, align 4		; <i8*> [#uses=1]
	%11 = getelementptr %struct.__softbound_hash_table_entry_t* %2, i32 %4, i32 1		; <i8**> [#uses=1]
	%12 = load i8** %11, align 4		; <i8*> [#uses=1]
	br label %bb4

bb2:		; preds = %bb
	%13 = icmp eq i8* %6, null		; <i1> [#uses=1]
	br i1 %13, label %bb4, label %bb

bb4:		; preds = %bb2, %bb1
	%final_bound.0 = phi i8* [ %12, %bb1 ], [ null, %bb2 ]		; <i8*> [#uses=1]
	%final_base.0 = phi i8* [ %10, %bb1 ], [ null, %bb2 ]		; <i8*> [#uses=1]
	store i8* %final_base.0, i8** %base, align 4
	store i8* %final_bound.0, i8** %bound, align 4
	%14 = icmp ugt i32 %7, 134217727		; <i1> [#uses=1]
	br i1 %14, label %bb5, label %return

bb5:		; preds = %bb4
	tail call void (...)* @__softbound_abort() noreturn nounwind
	unreachable

return:		; preds = %bb4
	ret void
}

declare void @__softbound_abort(...) noreturn

declare void @__softbound_printf(i8*, ...)

define internal void @__softbound_global_init() nounwind {
entry:
	tail call void @__softbound_init(i32 1, i32 0) nounwind
	ret void
}

declare void @__softbound_init(i32, i32)

define i32 @softbound_pseudo_main(i32 %argc, i8** %argv, i8* %argv_base, i8* %argv_bound) {
entry:
	%argv_bound2 = bitcast i8* %argv_bound to i8*		; <i8*> [#uses=1]
	%argv_base1 = bitcast i8* %argv_base to i8*		; <i8*> [#uses=1]
	%base.alloca = alloca i8*		; <i8**> [#uses=2]
	%bound.alloca = alloca i8*		; <i8**> [#uses=2]
	%safe.ptr = alloca i32		; <i32*> [#uses=2]
	%0 = getelementptr i8** %argv, i32 1		; <i8**> [#uses=3]
	%bcast_ld_dref_base = bitcast i8* %argv_base1 to i8*		; <i8*> [#uses=1]
	%bcast_arg_bound3 = bitcast i8* %argv_bound2 to i8*		; <i8*> [#uses=1]
	%bcast_ld_dref_bound = bitcast i8** %0 to i8*		; <i8*> [#uses=1]
	call void @__loadDereferenceCheck(i8* %bcast_ld_dref_base, i8* %bcast_arg_bound3, i8* %bcast_ld_dref_bound, i32 ptrtoint (i8** getelementptr (i8** null, i32 1) to i32), i32 1)
	%1 = load i8** %0, align 4		; <i8*> [#uses=2]
	%.ptr = bitcast i8** %0 to i8*		; <i8*> [#uses=1]
	%.ptrcast = bitcast i8* %1 to i8*		; <i8*> [#uses=1]
	call void @__hashLoadBaseBound(i8* %.ptr, i8** %base.alloca, i8** %bound.alloca, i8* %.ptrcast, i32 ptrtoint (i8* getelementptr (i8* null, i32 1) to i32), i32* %safe.ptr)
	%base.load = load i8** %base.alloca		; <i8*> [#uses=1]
	%bound.load = load i8** %bound.alloca		; <i8*> [#uses=1]
	%safe.ptr.load = load i32* %safe.ptr		; <i32> [#uses=0]
	%base.load1 = bitcast i8* %base.load to i8*		; <i8*> [#uses=1]
	%bound.load2 = bitcast i8* %bound.load to i8*		; <i8*> [#uses=1]
	%2 = call i32 @softbound_atoi(i8* %1, i8* %base.load1, i8* %bound.load2)		; <i32> [#uses=1]
	%value = bitcast i32** @value to i8*		; <i8*> [#uses=1]
	%3 = bitcast i32** getelementptr (i32** @value, i32 1) to i8*		; <i8*> [#uses=1]
	call void @softbound_test(i32 %2, i32** @value, i8* %value, i8* %3)
	ret i32 0
}

declare i32 @pseudo_main(i32, i8** nocapture)

declare i32 @softbound_atoi(i8*, i8*, i8*)

declare i32 @atoi(i8*) nounwind readonly

define void @softbound_test(i32 %mm, i32** %value, i8* %value_base, i8* %value_bound) {
entry:
	%value_bound2 = bitcast i8* %value_bound to i8*		; <i8*> [#uses=2]
	%value_base1 = bitcast i8* %value_base to i8*		; <i8*> [#uses=2]
	%base.alloca = alloca i8*		; <i8**> [#uses=2]
	%bound.alloca = alloca i8*		; <i8**> [#uses=2]
	%safe.ptr = alloca i32		; <i32*> [#uses=2]
	%bcast_ld_dref_base = bitcast i8* %value_base1 to i8*		; <i8*> [#uses=1]
	%bcast_arg_bound3 = bitcast i8* %value_bound2 to i8*		; <i8*> [#uses=1]
	%bcast_ld_dref_bound = bitcast i32** %value to i8*		; <i8*> [#uses=1]
	call void @__loadDereferenceCheck(i8* %bcast_ld_dref_base, i8* %bcast_arg_bound3, i8* %bcast_ld_dref_bound, i32 ptrtoint (i32** getelementptr (i32** null, i32 1) to i32), i32 1)
	%0 = load i32** %value, align 4		; <i32*> [#uses=4]
	%value.ptr = bitcast i32** %value to i8*		; <i8*> [#uses=1]
	%.ptrcast = bitcast i32* %0 to i8*		; <i8*> [#uses=1]
	call void @__hashLoadBaseBound(i8* %value.ptr, i8** %base.alloca, i8** %bound.alloca, i8* %.ptrcast, i32 ptrtoint (i32* getelementptr (i32* null, i32 1) to i32), i32* %safe.ptr)
	%base.load = load i8** %base.alloca		; <i8*> [#uses=1]
	%bound.load = load i8** %bound.alloca		; <i8*> [#uses=1]
	%safe.ptr.load = load i32* %safe.ptr		; <i32> [#uses=1]
	%base.load1 = bitcast i8* %base.load to i8*		; <i8*> [#uses=4]
	%bound.load2 = bitcast i8* %bound.load to i8*		; <i8*> [#uses=4]
	%1 = icmp sgt i32 %mm, 0		; <i1> [#uses=1]
	br i1 %1, label %bb, label %bb2

bb:		; preds = %bb, %entry
	%i.03 = phi i32 [ 0, %entry ], [ %5, %bb ]		; <i32> [#uses=2]
	%.rec8 = phi i32 [ 0, %entry ], [ %.rec9, %bb ]		; <i32> [#uses=1]
	%ptr.04.rec = phi i32 [ 0, %entry ], [ %.rec, %bb ]		; <i32> [#uses=2]
	%ptr.04.sum = add i32 %ptr.04.rec, %i.03		; <i32> [#uses=1]
	%2 = getelementptr i32* %0, i32 %ptr.04.sum		; <i32*> [#uses=2]
	%bcast_ld_dref_base4 = bitcast i8* %base.load1 to i8*		; <i8*> [#uses=1]
	%bound.load25 = bitcast i8* %bound.load2 to i8*		; <i8*> [#uses=1]
	%bcast_ld_dref_bound6 = bitcast i32* %2 to i8*		; <i8*> [#uses=1]
	call void @__loadDereferenceCheck(i8* %bcast_ld_dref_base4, i8* %bound.load25, i8* %bcast_ld_dref_bound6, i32 ptrtoint (i32* getelementptr (i32* null, i32 1) to i32), i32 1)
	%3 = load i32* %2, align 4		; <i32> [#uses=1]
	%.rec9 = add i32 %.rec8, %3		; <i32> [#uses=2]
	%4 = getelementptr i32* %0, i32 %.rec9		; <i32*> [#uses=3]
	%bcast_st_dref_base = bitcast i8* %value_base1 to i8*		; <i8*> [#uses=1]
	%bcast_st_dref_bound = bitcast i8* %value_bound2 to i8*		; <i8*> [#uses=1]
	%bcast_st_dref_ptr = bitcast i32** %value to i8*		; <i8*> [#uses=1]
	call void @__storeDereferenceCheck(i8* %bcast_st_dref_base, i8* %bcast_st_dref_bound, i8* %bcast_st_dref_ptr, i32 ptrtoint (i32** getelementptr (i32** null, i32 1) to i32), i32 1)
	store i32* %4, i32** %value, align 4
	%value.vptr = bitcast i32** %value to i8*		; <i8*> [#uses=1]
	%base.load1.vptr = bitcast i8* %base.load1 to i8*		; <i8*> [#uses=1]
	%bound.load2.vptr = bitcast i8* %bound.load2 to i8*		; <i8*> [#uses=1]
	%.aptr = bitcast i32* %4 to i8*		; <i8*> [#uses=1]
	call void @__hashStoreBaseBound(i8* %value.vptr, i8* %base.load1.vptr, i8* %bound.load2.vptr, i8* %.aptr, i32 ptrtoint (i32* getelementptr (i32* null, i32 1) to i32), i32 1)
	%5 = add i32 %i.03, 1		; <i32> [#uses=3]
	%.rec = add i32 %ptr.04.rec, %5		; <i32> [#uses=1]
	%exitcond11 = icmp eq i32 %5, %mm		; <i1> [#uses=1]
	br i1 %exitcond11, label %bb2, label %bb

bb2:		; preds = %bb, %entry
	%.lcssa_base = phi i8* [ %base.load1, %entry ], [ %base.load1, %bb ]		; <i8*> [#uses=0]
	%.lcssa_bound = phi i8* [ %bound.load2, %entry ], [ %bound.load2, %bb ]		; <i8*> [#uses=0]
	%safe.phi_node = phi i32 [ %safe.ptr.load, %entry ], [ 1, %bb ]		; <i32> [#uses=0]
	%.lcssa = phi i32* [ %0, %entry ], [ %4, %bb ]		; <i32*> [#uses=1]
	%6 = tail call i32 (i8*, ...)* @printf(i8* noalias getelementptr ([4 x i8]* @.str1, i32 0, i32 0), i32* %.lcssa) nounwind		; <i32> [#uses=0]
	ret void
}

declare void @test(i32, i32** nocapture) nounwind

declare i32 @printf(i8*, ...) nounwind
