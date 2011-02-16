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

#include <stddef.h>
#include <limits.h>

// Check to make sure at least one and only one metadata representation is defined
#ifndef __SOFTBOUND_HASHTABLE
#ifndef __SOFTBOUND_SHADOWSPACE
#ifndef __SOFTBOUND_DISABLE
#error "SoftBound error: configuration type not specified (-D__SOFTBOUND_HASHTABLE, -D__SOFTBOUND_SHADOWSPACE, or -D__SOFTBOUND_DISABLE)"
#endif
#endif
#endif

#ifdef __SOFTBOUND_HASHTABLE
#ifdef __SOFTBOUND_SHADOWSPACE
#error "SoftBound error: only one configuration may be specified (-D__SOFTBOUND_HASHTABLE, -D__SOFTBOUND_SHADOWSPACE, or -D__SOFTBOUND_DISABLE)"
#endif
#endif

#ifdef __SOFTBOUND_HASHTABLE
#ifdef __SOFTBOUND_DISABLE
#error "SoftBound error: only one configuration may be specified (-D__SOFTBOUND_HASHTABLE, -D__SOFTBOUND_SHADOWSPACE, or -D__SOFTBOUND_DISABLE)"
#endif
#endif

#ifdef __SOFTBOUND_SHADOWSPACE
#ifdef __SOFTBOUND_DISABLE
#error "SoftBound error: only one configuration may be specified (-D__SOFTBOUND_HASHTABLE, -D__SOFTBOUND_SHADOWSPACE, or -D__SOFTBOUND_DISABLE)"
#endif
#endif

#ifdef __SOFTBOUND_HASHTABLE
#undef __SOFTBOUND_HASHTABLE
static const int __SOFTBOUND_HASHTABLE = 1;
#else
static const int __SOFTBOUND_HASHTABLE = 0;
#endif

#ifdef __SOFTBOUND_SHADOWSPACE
#undef __SOFTBOUND_SHADOWSPACE
static const int __SOFTBOUND_SHADOWSPACE = 1;
#else
static const int __SOFTBOUND_SHADOWSPACE = 0;
#endif

#ifdef __SOFTBOUND_DISABLE
#undef __SOFTBOUND_DISABLE
static const int __SOFTBOUND_DISABLE = 1;
#else
static const int __SOFTBOUND_DISABLE = 0;
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
static const size_t __SOFTBOUND_N_HASH_ENTRIES = ((size_t) 128 * (size_t) 1024 * (size_t) 1024); // 2^27
static const size_t __SOFTBOUND_LOWER_ZERO_POINTER_BITS = 2;
#endif

#if __WORDSIZE == 64
static const size_t __SOFTBOUND_N_HASH_ENTRIES = ((size_t) 128 * (size_t) 1024 * (size_t) 1024); // 2^27
static const size_t __SOFTBOUND_LOWER_ZERO_POINTER_BITS = 3;
#endif

typedef struct {
  void* base;
  void* bound;
  void* tag;
} __softbound_hash_table_entry_t;

typedef struct {
  void* base;
  void* bound;
} __softbound_shadow_space_entry_t;

#define __WEAK_INLINE __attribute__((__weak__,__always_inline__)) inline

extern __softbound_hash_table_entry_t* __softbound_hash_table_begin;
extern __softbound_shadow_space_entry_t* __softbound_shadow_space_begin;

extern void __softbound_init(int is_hash_table, int is_shadow_space);
extern __SOFTBOUND_NORETURN void __softbound_abort();
extern void __softbound_printf(char* str, ...);


/******************************************************************************/

static __attribute__ ((__constructor__)) void __softbound_global_init();

void __softbound_global_init()
{
  __softbound_init(__SOFTBOUND_HASHTABLE, __SOFTBOUND_SHADOWSPACE);
}

/******************************************************************************/

__WEAK_INLINE void __shrinkBounds(void* new_base, void* new_bound, void* old_base, void* old_bound, void** base_alloca, void** bound_alloca)
{
  *(base_alloca) = new_base < old_base ? old_base: new_base;
  *(bound_alloca) = new_bound > old_bound? old_bound : new_bound;
}

__WEAK_INLINE void __callDereferenceCheck(void* base, void* bound, void* ptr) 
{
  if (__SOFTBOUND_DISABLE) {
    return;
  }

  if ((base != bound) && (ptr != base)) {
    if (__SOFTBOUND_DEBUG) {
      __softbound_printf("In Call Dereference Check, base=%p, bound=%p, ptr=%p\n", base, bound, ptr);
    }
    __softbound_abort();
  }
}

__WEAK_INLINE void __loadDereferenceCheck(void *base, void *bound, void *ptr, size_t size_of_type, int ptr_safe)
{
  if (__SOFTBOUND_DISABLE) {
    return;
  }

  if ((ptr < base) || (ptr + size_of_type > bound)) {
    if (__SOFTBOUND_DEBUG) {
      __softbound_printf("In Load Dereference Check, base=%p, bound=%p, ptr=%p\n", base, bound, ptr);
    }
    __softbound_abort();
  }
}

__WEAK_INLINE void __storeDereferenceCheck(void *base, void *bound, void *ptr, size_t size_of_type, int ptr_safe)
{
  if (__SOFTBOUND_DISABLE) {
    return;
  }      

  if ((ptr < base) || (ptr + size_of_type > bound)) {
    if (__SOFTBOUND_DEBUG) {
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
  if( size > 2147483648){
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
  if( size > 2147483648){
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

  if(__SOFTBOUND_HASHTABLE) {
    size_t counter = 0;    
    while(1) {
      void* ptr = addr_of_ptr;
      // FIXME: pull part of the following line out of the loop, get rid of "+ counter"
      // The only part to keep in the loop is the "index = index & mask" part
      size_t index = ((((size_t) addr_of_ptr ) >> __SOFTBOUND_LOWER_ZERO_POINTER_BITS) + counter) % __SOFTBOUND_N_HASH_ENTRIES;  
      
      if(__SOFTBOUND_DEBUG) {

        printf("index = %zx\n", index);
        printf("softbound_hash_entries = %zx\n", __SOFTBOUND_N_HASH_ENTRIES);
        printf("__softbound_hash_table_begin = %zx\n", __softbound_hash_table_begin);
        printf("&__softbound_hash_table_begin[index] = %zx\n", &__softbound_hash_table_begin[index]);

      }
      __softbound_hash_table_entry_t* entry_ptr = &__softbound_hash_table_begin[index];
      void* tag = entry_ptr->tag;
      
      if ((tag == ptr) | (tag == 0)) {

        if( base == 0 || bound == 0) {
          //          __softbound_printf("[hashStoreBaseBound], storing zero base and bound, ptr=%p, addr_of_ptr=%p\n", actual_ptr, addr_of_ptr);
        }

        entry_ptr->base = base;
        entry_ptr->bound = bound;
        entry_ptr->tag = ptr;
        if (__SOFTBOUND_DEBUG) {          
          //  __softbound_printf("tag match - storing ptr with base bound for ptr %p, %p, %p\n", addr_of_ptr, base, bound);
        }
        return;
      }
      
      if (__SOFTBOUND_DEBUG) {
        __softbound_printf("already a collision at this address=%p and value there is %p\n", addr_of_ptr, tag);
      }

      if(counter >= (__SOFTBOUND_N_HASH_ENTRIES)) {
        __softbound_printf("Hash table full\n");
        __softbound_abort();
      }
      
      if(__SOFTBOUND_DEBUG) {
        if(counter >= (__SOFTBOUND_N_HASH_ENTRIES/2)) {
          //          __softbound_printf("Hash table is over half full, count = %zu\n", counter);
          __softbound_abort();
        }
      }
      counter++;  // FIXME, change to "index++; Then put "index = index & mask;" at top of loop
    } /* end of while 1 */
    return;
  }
    
  if(__SOFTBOUND_SHADOWSPACE) {
    __softbound_shadow_space_entry_t* entry_ptr;
    size_t index = (((size_t) addr_of_ptr) >> __SOFTBOUND_LOWER_ZERO_POINTER_BITS) % __SOFTBOUND_N_HASH_ENTRIES;    
    // size_t ptr = (size_t) addr_of_ptr;    
    entry_ptr = &__softbound_shadow_space_begin[index];    
    entry_ptr->base = base;
    entry_ptr->bound = bound;
    return;
  }   
}

__WEAK_INLINE int  __hashProbeAddrOfPtr(void* addr_of_ptr, void** base, void** bound) {

  if(__SOFTBOUND_DEBUG) {
    __softbound_printf("probing has shadow space for addr_of_ptr = %p\n", addr_of_ptr);
  }

  if(__SOFTBOUND_DISABLE) {
    return 0;
  }

  if(__SOFTBOUND_HASHTABLE) {
    size_t counter = 0;
    
    while(1) {
      void* final_base = NULL;
      void* final_bound = NULL;
      void* ptr = addr_of_ptr;
      size_t index = ((((size_t) addr_of_ptr ) >> __SOFTBOUND_LOWER_ZERO_POINTER_BITS) + counter) % __SOFTBOUND_N_HASH_ENTRIES;    
      
      __softbound_hash_table_entry_t* entry_ptr = &__softbound_hash_table_begin[index];
      void* tag = entry_ptr->tag;
      
      if(tag == ptr) {
        final_base = entry_ptr->base;
        final_bound = entry_ptr->bound;
        
        *((void**) base) = final_base;
        *((void**) bound) = final_bound;
        
        if(final_base == NULL && final_bound == NULL) {
          return 0;
        }
        else {
          return 1;
        }
      }
      if (tag == 0) {
        return 0;
      }
      if(__SOFTBOUND_DEBUG) {
        if(counter >= (__SOFTBOUND_N_HASH_ENTRIES/2)) {
          __softbound_printf("Hash table is over half full, count = %zu\n", counter);
          __softbound_abort();
        }
      }
      counter++;
    } /* end of while 1 */
    return 0;
  }

  if(__SOFTBOUND_SHADOWSPACE) {
    
    void* final_base = NULL;
    void* final_bound = NULL;
    size_t index = ((((size_t) addr_of_ptr) >> __SOFTBOUND_LOWER_ZERO_POINTER_BITS)) % __SOFTBOUND_N_HASH_ENTRIES;
    __softbound_shadow_space_entry_t* entry_ptr = &__softbound_shadow_space_begin[index];    
    
    final_base = entry_ptr->base;
    final_bound = entry_ptr->bound;
    
    *((void**) base) = final_base;
    *((void**) bound) = final_bound;

    if(final_base == NULL && final_bound == NULL) {
      return 0;
    } 
    else {
      return 1;
    }    
  }
  return 0;
}


__WEAK_INLINE void __hashLoadBaseBound(void* addr_of_ptr, void** base, void** bound, const void* actual_ptr, size_t size_of_type, int* ptr_safe) 
{

  if (__SOFTBOUND_DISABLE) {
    return;
  }


  if(__SOFTBOUND_HASHTABLE) {

    size_t counter = 0;
    void* ptr = addr_of_ptr;
    void* final_base = NULL;
    void* final_bound = NULL;    
    while(1) {      
      size_t index = ((((size_t) addr_of_ptr) >> __SOFTBOUND_LOWER_ZERO_POINTER_BITS) + counter) % __SOFTBOUND_N_HASH_ENTRIES;
      __softbound_hash_table_entry_t* entry_ptr = &__softbound_hash_table_begin[index];
      void* tag = entry_ptr->tag;
      counter++;
      if (tag == ptr) {
        final_base = entry_ptr->base;
        final_bound = entry_ptr->bound;
        break;
      }
      if(tag == 0) {
        //        __softbound_printf("[hashLoadBaseBound], Loading zeros, ptr=%p, addr_of_ptr=%p\n", actual_ptr, addr_of_ptr);
        final_base = 0;
        final_bound  = 0;
        break;
      }
    }
    *((void**) base) = final_base;
    *((void**) bound) = final_bound;
    if(counter >= __SOFTBOUND_N_HASH_ENTRIES) {
      __softbound_abort();
    }
  
    if(__SOFTBOUND_DEBUG) {
      //      if(__softbound_deref_check_count > (size_t)(704822000))
        __softbound_printf("[hashLoadBaseBound] probing hash shadow space for addr_of_ptr = %p, base = %p, bound=%p, actual_ptr = %p\n", addr_of_ptr, final_base, final_bound, actual_ptr);
    }   
  

    return;    
  }

  if(__SOFTBOUND_SHADOWSPACE) {
    void* final_base = NULL;
    void* final_bound = NULL;
    size_t index = ((((size_t) addr_of_ptr) >> __SOFTBOUND_LOWER_ZERO_POINTER_BITS)) % __SOFTBOUND_N_HASH_ENTRIES;
    __softbound_shadow_space_entry_t* entry_ptr = &__softbound_shadow_space_begin[index];   
    final_base = entry_ptr->base;
    final_bound  = entry_ptr->bound;
    *((void**) base) = final_base;
    *((void**) bound) = final_bound;
  
    if(__SOFTBOUND_DEBUG) {
      //      if(__softbound_deref_check_count > (size_t)(704822000))
        __softbound_printf("[hashLoadBaseBound] probing hash shadow space for addr_of_ptr = %p, base = %p, bound=%p, actual_ptr = %p\n", addr_of_ptr, final_base, final_bound, actual_ptr);
    }   
  
    return;        
  }
}


#endif
