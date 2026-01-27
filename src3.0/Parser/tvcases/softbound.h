/*
Copyright (c) 2009 Santosh Nagarakatte, Milo M. K. Martin. All rights reserved.

Developed by: Santosh Nagarakatte, Milo M.K. Martin,
              Jianzhou Zhao, Steve Zdancewic
              Department of Computer and Information Sciences,
              University of Pennsylvania
              http://www.cis.upenn.edu/acg/softbound/

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to
deal with the Software without restriction, including without limitation the
rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

  1. Redistributions of source code must retain the above copyright notice,
     this list of conditions and the following disclaimers.

  2. Redistributions in binary form must reproduce the above copyright
     notice, this list of conditions and the following disclaimers in the
     documentation and/or other materials provided with the distribution.

  3. Neither the names of Santosh Nagarakatte, Milo M. K. Martin,
     Jianzhou Zhao, Steve Zdancewic, University of Pennsylvania, nor
     the names of its contributors may be used to endorse or promote
     products derived from this Software without specific prior
     written permission.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
CONTRIBUTORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
WITH THE SOFTWARE.

*/

#ifndef __SOFTBOUND_H__
#define __SOFTBOUND_H__

#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>
#include <limits.h>
#include <sys/mman.h>
#include <string.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <assert.h>

// Check to make sure at least one and only one metadata representation is defined
#ifndef __SOFTBOUND_TRIE
#error "SoftBound error: configuration type not specified (-D__SOFTBOUND_TRIE))"
#endif


#ifdef __SOFTBOUND_TRIE
#undef __SOFTBOUND_TRIE
static const int __SOFTBOUND_TRIE = 1;
#else
static const int __SOFTBOUND_TRIE = 0;
#endif

#ifdef __SOFTBOUND_CHECK_DEBUG
#undef __SOFTBOUND_CHECK_DEBUG
static const int __SOFTBOUND_CHECK_DEBUG = 1;
#else
static const int __SOFTBOUND_CHECK_DEBUG = 0;
#endif


#ifdef __SOFTBOUNDCETSWITHSS_SHADOW_STACK_DEBUG
#undef __SOFTBOUNDCETSWITHSS_SHADOW_STACK_DEBUG
static const int __SOFTBOUNDCETSWITHSS_SHADOW_STACK_DEBUG = 1;
#else
static const int __SOFTBOUNDCETSWITHSS_SHADOW_STACK_DEBUG = 0;
#endif

#ifdef __SOFTBOUND_DEBUG
#undef __SOFTBOUND_DEBUG
static const int __SOFTBOUND_DEBUG = 1;
#define __SOFTBOUND_NORETURN 
#else 
static const int __SOFTBOUND_DEBUG = 0;
#define __SOFTBOUND_NORETURN __attribute__((__noreturn__))
#endif

#if __WORDSIZE == 32
static const size_t __SOFTBOUND_TRIE_PRIMARY_TABLE_ENTRIES = ((size_t) 4 * (size_t) 1024 ); // 2^12
static const size_t __SOFTBOUND_TRIE_SECONDARY_TABLE_ENTRIES = ((size_t) 256 * (size_t) 1024); // 2^18
static const size_t __SOFTBOUND_LOWER_ZERO_POINTER_BITS = 2;
static const size_t __SOFTBOUND_TRIE_SECONDARY_TABLE_BITS = 18;
static const size_t __SOFTBOUNDCETSWITHSS_SHADOW_STACK_ENTRIES = ((size_t) 128 * (size_t) 32 );
#endif

#if __WORDSIZE == 64
static const size_t __SOFTBOUND_TRIE_PRIMARY_TABLE_ENTRIES = ((size_t) 8*(size_t) 1024 * (size_t) 1024);
static const size_t __SOFTBOUND_TRIE_SECONDARY_TABLE_ENTRIES = ((size_t) 4 * (size_t) 1024 * (size_t) 1024); 
static const size_t __SOFTBOUND_LOWER_ZERO_POINTER_BITS = 3;
static const size_t __SOFTBOUND_TRIE_SECONDARY_TABLE_BITS = 22;
static const size_t __SOFTBOUNDCETSWITHSS_SHADOW_STACK_ENTRIES = ((size_t) 128 * (size_t) 32 );
#endif

typedef struct {
  void* base;
  void* bound;
} __softbound_trie_entry_t;

#define __WEAK_INLINE __attribute__((__weak__,__always_inline__)) inline

extern __softbound_trie_entry_t** __softbound_trie_primary_table;
extern size_t* __softboundcetswithss_shadow_stack_ptr;

extern __SOFTBOUND_NORETURN void __softbound_abort();
extern void __softbound_printf(char* str, ...);
__WEAK_INLINE __softbound_trie_entry_t* __softbound_trie_allocate();


/******************************************************************************/

extern void __softbound_init(int, int);
//extern __attribute__ ((__weak__, __noinline__)) void __softbound_init(int, int);
static __attribute__ ((__constructor__)) void __softbound_global_init();

void __softbound_global_init()
{
  __softbound_init(0,0);
}

/******************************************************************************/

__WEAK_INLINE void __softboundcetswithss_copy_metadata(void* dest, void* from, size_t size){

  //  printf("dest=%p, from=%p, size=%zx\n", dest, from, size);
  
  size_t dest_ptr = (size_t) dest;
  size_t dest_ptr_end = dest_ptr + size;

  size_t from_ptr = (size_t) from;
  size_t from_ptr_end = from_ptr + size;

  __softbound_trie_entry_t* trie_secondary_table_dest_begin;
  __softbound_trie_entry_t* trie_secondary_table_from_begin;

  size_t dest_primary_index_begin = (dest_ptr >> 25);
  size_t dest_primary_index_end = (dest_ptr_end >> 25);

  if(dest_primary_index_begin != dest_primary_index_end)
    return;


  //  assert(dest_primary_index_begin == dest_primary_index_end);

  size_t from_primary_index_begin = (from_ptr >> 25);
  size_t from_primary_index_end =  (from_ptr_end >> 25);

  if(from_primary_index_begin != from_primary_index_end)
    return;

  //  assert(from_primary_index_begin == from_primary_index_end);
  
  trie_secondary_table_dest_begin = __softbound_trie_primary_table[dest_primary_index_begin];
  trie_secondary_table_from_begin = __softbound_trie_primary_table[from_primary_index_begin];
  
  if(trie_secondary_table_from_begin == NULL)
    return;

  if(trie_secondary_table_dest_begin == NULL){
    trie_secondary_table_dest_begin = __softbound_trie_allocate();
    __softbound_trie_primary_table[dest_primary_index_begin] = trie_secondary_table_dest_begin;
  }

  size_t dest_secondary_index = ((dest_ptr>> 3) & 0x3fffff);
  size_t from_secondary_index = ((from_ptr>> 3) & 0x3fffff);
  
  void* dest_entry_ptr = &trie_secondary_table_dest_begin[dest_secondary_index];
  void* from_entry_ptr = &trie_secondary_table_from_begin[from_secondary_index];
  
  memcpy(dest_entry_ptr, from_entry_ptr, 8 * size);
  
  return;  
}


__WEAK_INLINE void __softboundcetswithss_allocate_shadow_stack_space(int num_pointer_args){
 
  size_t* prev_stack_size_ptr = __softboundcetswithss_shadow_stack_ptr + 1;
  size_t prev_stack_size = *((size_t*)prev_stack_size_ptr);

  if(__SOFTBOUNDCETSWITHSS_SHADOW_STACK_DEBUG){
    printf("[allocate_stack] shadow_stack_ptr = %p, prev_stack_size = %zx, prev_stack_size_ptr = %p\n", __softboundcetswithss_shadow_stack_ptr, prev_stack_size, prev_stack_size_ptr);
  }

  __softboundcetswithss_shadow_stack_ptr = __softboundcetswithss_shadow_stack_ptr + prev_stack_size + 2;

  if(__SOFTBOUNDCETSWITHSS_SHADOW_STACK_DEBUG){
    printf("[allocate_stack] new_shadow_stack_ptr = %p\n", __softboundcetswithss_shadow_stack_ptr);
  }
  
  *((size_t*) __softboundcetswithss_shadow_stack_ptr) = prev_stack_size;
  size_t* current_stack_size_ptr = __softboundcetswithss_shadow_stack_ptr + 1;
  
  ssize_t size = num_pointer_args * 4;
  *((size_t*) current_stack_size_ptr) = size;
}
   
__WEAK_INLINE void* __softboundcetswithss_load_base_shadow_stack(int arg_no){
  assert (arg_no >= 0 );
  size_t count = 2 +  arg_no * 4 + 0;
  size_t* base_ptr = (__softboundcetswithss_shadow_stack_ptr + count); 
  void* base = *((void**)base_ptr);
  if(__SOFTBOUNDCETSWITHSS_SHADOW_STACK_DEBUG){
    printf("[load_base] loading base=%p from shadow_stack_ptr=%p\n", base, base_ptr);
  }
  return base;
}

__WEAK_INLINE void* __softboundcetswithss_load_bound_shadow_stack(int arg_no){

  assert (arg_no >= 0 );
  size_t count = 2 + arg_no * 4 + 1;
  size_t* bound_ptr = (__softboundcetswithss_shadow_stack_ptr + count); 

  void* bound = *((void**)bound_ptr);
  if(__SOFTBOUNDCETSWITHSS_SHADOW_STACK_DEBUG){
    printf("[load_bound] loading bound=%p from shadow_stack_ptr=%p\n", bound, bound_ptr);
  }
  return bound;
}

__WEAK_INLINE size_t __softboundcetswithss_load_key_shadow_stack(int arg_no){

  assert (arg_no >= 0 );
  size_t count = 2 + arg_no * 4 + 2;
  size_t* key_ptr = (__softboundcetswithss_shadow_stack_ptr + count); 
  size_t key = *key_ptr;
  if(__SOFTBOUNDCETSWITHSS_SHADOW_STACK_DEBUG){
    printf("[load_key] loading key=%zx from shadow_stack_ptr=%p\n", key, key_ptr);
  }
  return key;
}

__WEAK_INLINE void* __softboundcetswithss_load_lock_shadow_stack(int arg_no){

  assert (arg_no >= 0 );
  size_t count = 2 + arg_no * 4 + 3;
  size_t* lock_ptr = (__softboundcetswithss_shadow_stack_ptr + count); 
  void* lock = *((void**)lock_ptr);
  if(__SOFTBOUNDCETSWITHSS_SHADOW_STACK_DEBUG){
    printf("[load_lock] loading lock=%p from shadow_stack_ptr=%p\n", lock, lock_ptr);
  }
  return lock;
}

__WEAK_INLINE void __softboundcetswithss_store_base_shadow_stack(void* base, int arg_no){
  
  assert(arg_no >= 0);
  size_t count = 2 +  arg_no * 4 + 0;
  void** base_ptr = (void**)(__softboundcetswithss_shadow_stack_ptr + count); 

  *(base_ptr) = base;
  if(__SOFTBOUNDCETSWITHSS_SHADOW_STACK_DEBUG){
    printf("[store_base] storing base=%p from shadow_stack_ptr=%p\n", base, base_ptr);
  }

}

__WEAK_INLINE void __softboundcetswithss_store_bound_shadow_stack(void* bound, int arg_no){

  assert(arg_no >= 0);
  size_t count = 2 +  arg_no * 4 + 1;
  void** bound_ptr = (void**)(__softboundcetswithss_shadow_stack_ptr + count); 

  *(bound_ptr) = bound;
  if(__SOFTBOUNDCETSWITHSS_SHADOW_STACK_DEBUG){  
    printf("[store_bound] storing bound=%p from shadow_stack_ptr=%p\n", bound, bound_ptr);
  }
}

__WEAK_INLINE void __softboundcetswithss_store_key_shadow_stack(size_t key, int arg_no){
  assert(arg_no >= 0);
  size_t count = 2 +  arg_no * 4 + 2;
  size_t* key_ptr = (__softboundcetswithss_shadow_stack_ptr + count); 

  *(key_ptr) = key;
  if(__SOFTBOUNDCETSWITHSS_SHADOW_STACK_DEBUG){
    printf("[store_base] storing key=%zx from shadow_stack_ptr=%p\n", key, key_ptr);
  }
}


__WEAK_INLINE void __softboundcetswithss_store_lock_shadow_stack(void* lock, int arg_no){
  assert(arg_no >= 0);
  size_t count = 2 +  arg_no * 4 + 3;
  void** lock_ptr = (void**)(__softboundcetswithss_shadow_stack_ptr + count); 

  *(lock_ptr) = lock;
  if(__SOFTBOUNDCETSWITHSS_SHADOW_STACK_DEBUG){
    printf("[store_base] storing lock=%p from shadow_stack_ptr=%p\n", lock, lock_ptr);
  }
}

__WEAK_INLINE void __softboundcetswithss_deallocate_shadow_stack_space(){

  size_t* reserved_space_ptr = __softboundcetswithss_shadow_stack_ptr;

  size_t read_value = *((size_t*) reserved_space_ptr);

  assert((read_value >=0 && read_value <= __SOFTBOUNDCETSWITHSS_SHADOW_STACK_ENTRIES));
                                                
  size_t* prev_ptr;

  if(__SOFTBOUNDCETSWITHSS_SHADOW_STACK_DEBUG){
    prev_ptr = __softboundcetswithss_shadow_stack_ptr;
  }

  __softboundcetswithss_shadow_stack_ptr =  __softboundcetswithss_shadow_stack_ptr - read_value - 2;

  if(__SOFTBOUNDCETSWITHSS_SHADOW_STACK_DEBUG){
    printf("[deallocate] current_shadow_stack_ptr=%p, prev_stack_ptr=%p\n", __softboundcetswithss_shadow_stack_ptr, prev_ptr);
  }
}

/******************************************************************************/

__WEAK_INLINE __softbound_trie_entry_t* __softbound_trie_allocate(){
  
  __softbound_trie_entry_t* secondary_entry;
  size_t length = (__SOFTBOUND_TRIE_SECONDARY_TABLE_ENTRIES) * sizeof(__softbound_trie_entry_t);
  secondary_entry = mmap(0, length, PROT_READ| PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE, -1, 0);
  //assert(secondary_entry != (void*)-1); 
  //  printf("snd trie table %p %lx\n", secondary_entry, length);
  return secondary_entry;
}


__WEAK_INLINE void __shrinkBounds(void* new_base, void* new_bound, void* old_base, void* old_bound, void** base_alloca, void** bound_alloca)
{
  *(base_alloca) = new_base < old_base ? old_base: new_base;
  *(bound_alloca) = new_bound > old_bound? old_bound : new_bound;
}

__WEAK_INLINE void __callDereferenceCheck(void* base, void* bound, void* ptr) 
{
  if ((base != bound) && (ptr != base)) {
    if (__SOFTBOUND_DEBUG) {
      __softbound_printf("In Call Dereference Check, base=%p, bound=%p, ptr=%p\n", base, bound, ptr);
    }
    __softbound_abort();
  }
}

__WEAK_INLINE void __loadDereferenceCheck(void *base, void *bound, void *ptr, size_t size_of_type, int ptr_safe)
{
  if ((ptr < base) || (ptr + size_of_type > bound)) {
    if (__SOFTBOUND_CHECK_DEBUG) {
      __softbound_printf("In Load Dereference Check, base=%p, bound=%p, ptr=%p\n", base, bound, ptr);
    }
    __softbound_abort();
  }
}

__WEAK_INLINE void __storeDereferenceCheck(void *base, void *bound, void *ptr, size_t size_of_type, int ptr_safe)
{
  if ((ptr < base) || (ptr + size_of_type > bound)) {
    if (__SOFTBOUND_CHECK_DEBUG) {
      __softbound_printf("In Store Dereference Check, base=%p, bound=%p, ptr=%p\n", base, bound, ptr);
    }
    __softbound_abort();
  }
}

__WEAK_INLINE void __memcopyCheck_i64(char* ptr, char* ptr_base, char* ptr_bound, size_t size) {
  
#if __WORDSIZE == 64
  if( size > 281474976710656 ){
    __softbound_abort();
  }
#else
  if( size > 2147483647){
    __softbound_abort();
  }
#endif

  if ( (ptr < ptr_base) || (ptr + size < ptr_base) || ( ptr +size > ptr_bound) || ((char*) size > ptr_bound) ) {
    if(__SOFTBOUND_DEBUG) {
      __softbound_printf("In memcopy check ptr = %p, ptr_base = %p, ptr_bound = %p, size = %zu\n", ptr, ptr_base, ptr_bound, size);
    }
    __softbound_abort();
  }
}

__WEAK_INLINE void __memcopyCheck(char* ptr, char* ptr_base, char* ptr_bound, size_t size) {

#if __WORDSIZE == 64
  if( size > 281474976710656 ){
    __softbound_abort();
  }
#else
  if( size > 2147483647){
    __softbound_abort();
  }
#endif

  if ( (ptr < ptr_base) || (ptr + size < ptr_base) || (ptr + size > ptr_bound) || ((char*) size > ptr_bound) ) {
    if(__SOFTBOUND_DEBUG) {
      __softbound_printf("In memcopy check ptr = %p, ptr_base = %p, ptr_bound = %p, size = %zu\n", ptr, ptr_base, ptr_bound, size);
    }
    __softbound_abort();
  }
}

__WEAK_INLINE void __hashStoreBaseBound(void* addr_of_ptr, void* base, void* bound, const void* actual_ptr, size_t size_of_type, int ptr_safe) {

  if(__SOFTBOUND_DEBUG) {
    //    if(__softbound_deref_check_count > (size_t)(704822000))
      __softbound_printf("[hashStoreBaseBound] addr_of_ptr = %p, base = %p, bound = %p, actual_ptr = %p, size_of_type = %zu\n",
             addr_of_ptr, base, bound, actual_ptr, size_of_type);
  }
  
  if(__SOFTBOUND_TRIE){
    
     
  size_t ptr = (size_t) addr_of_ptr;
  size_t primary_index;
  __softbound_trie_entry_t* trie_secondary_table;
  __softbound_trie_entry_t** trie_primary_table = __softbound_trie_primary_table;
  
  int shift_val = __SOFTBOUND_LOWER_ZERO_POINTER_BITS + __SOFTBOUND_TRIE_SECONDARY_TABLE_BITS;
  
  primary_index = (ptr >> shift_val);
  trie_secondary_table = __softbound_trie_primary_table[primary_index];

  if(trie_secondary_table == NULL){
    trie_secondary_table =  __softbound_trie_allocate();
    __softbound_trie_primary_table[primary_index] = trie_secondary_table;
  }    

#if __WORDSIZE == 64
  size_t secondary_index = ((ptr >> 3) & 0x3fffff);
#else
  size_t secondary_index = ((ptr >> __SOFTBOUND_LOWER_ZERO_POINTER_BITS) & 0x3ffff);
#endif
  assert(secondary_index < __SOFTBOUND_TRIE_SECONDARY_TABLE_ENTRIES);

  __softbound_trie_entry_t* entry_ptr =&trie_secondary_table[secondary_index];

  assert(trie_secondary_table != NULL);
  entry_ptr->base = base;
  entry_ptr->bound = bound;  
  }

  return;
}


__WEAK_INLINE void __hashLoadBaseBound(void* addr_of_ptr, void** base, void** bound, const void* actual_ptr, size_t size_of_type, int* ptr_safe) 
{
  
  if(__SOFTBOUND_TRIE){

    size_t ptr = (size_t) addr_of_ptr;
    __softbound_trie_entry_t* trie_secondary_table;
    __softbound_trie_entry_t** trie_primary_table = __softbound_trie_primary_table;
    
    int shift_val = __SOFTBOUND_LOWER_ZERO_POINTER_BITS + __SOFTBOUND_TRIE_SECONDARY_TABLE_BITS;
    size_t primary_index = ( ptr >> shift_val);
    trie_secondary_table = __softbound_trie_primary_table[primary_index];

    if(trie_secondary_table == NULL) {	
      *((void**) base) = 0;
      *((void**) bound) = 0;
      return;
    }

#if __WORDSIZE == 64
    size_t secondary_index = ((ptr >> 3) & 0x3fffff);
#else
    size_t secondary_index = ((ptr >> __SOFTBOUND_LOWER_ZERO_POINTER_BITS) & 0x3ffff);
#endif

    assert(secondary_index < __SOFTBOUND_TRIE_SECONDARY_TABLE_ENTRIES);

    __softbound_trie_entry_t* entry_ptr = &trie_secondary_table[secondary_index];
    
    assert(entry_ptr != NULL);

    *((void**) base) = entry_ptr->base;
    *((void**) bound) = entry_ptr->bound;
  }

  return;
}

/* __hashLoadBase must be called first, the __tmp_bound stores the corresponding
 * bound, and is returned by the following __hashLoadBound. 
 * */
static void* __tmp_bound = (void*)NULL;

__WEAK_INLINE void* __hashLoadBase(void* addr_of_ptr,  const void* actual_ptr, size_t size_of_type, int* ptr_safe) 
{
  
  if(__SOFTBOUND_TRIE){

    size_t ptr = (size_t) addr_of_ptr;
    __softbound_trie_entry_t* trie_secondary_table;
    __softbound_trie_entry_t** trie_primary_table = __softbound_trie_primary_table;
    
    int shift_val = __SOFTBOUND_LOWER_ZERO_POINTER_BITS + __SOFTBOUND_TRIE_SECONDARY_TABLE_BITS;
    size_t primary_index = ( ptr >> shift_val);
    trie_secondary_table = __softbound_trie_primary_table[primary_index];

    if(trie_secondary_table == NULL) {	
      __tmp_bound = (void*)NULL;	    
      return (void*)NULL;
    }

#if __WORDSIZE == 64
    size_t secondary_index = ((ptr >> 3) & 0x3fffff);
#else
    size_t secondary_index = ((ptr >> __SOFTBOUND_LOWER_ZERO_POINTER_BITS) & 0x3ffff);
#endif

    assert(secondary_index < __SOFTBOUND_TRIE_SECONDARY_TABLE_ENTRIES);

    __softbound_trie_entry_t* entry_ptr = &trie_secondary_table[secondary_index];
    
    assert(entry_ptr != NULL);

    __tmp_bound = entry_ptr->bound;
    return entry_ptr->base;
  }

  __tmp_bound = (void*)NULL;	    
  return (void*)NULL;
}

__WEAK_INLINE void* __hashLoadBound(void* addr_of_ptr,  const void* actual_ptr, size_t size_of_type, int* ptr_safe) 
{
  return __tmp_bound;
}
#endif
