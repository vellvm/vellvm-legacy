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

#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <malloc.h>
#include <string.h>
#include <ctype.h>
#include <stdarg.h>
#include <sys/mman.h>
#include <execinfo.h>
#include "softbound.h"

__softbound_hash_table_entry_t* __softbound_hash_table_begin = NULL;
__softbound_shadow_space_entry_t* __softbound_shadow_space_begin = NULL;
size_t __softbound_deref_check_count = 0;

__SOFTBOUND_NORETURN void __softbound_abort()
{
  fprintf(stderr, "\nSoftBound: Bounds violation detected\n\nBacktrace:\n");

  // Based on code from the backtrace man page
  size_t size;
  void *array[100];
  
  size = backtrace(array, 100);
  backtrace_symbols_fd(array, size, fileno(stderr));
  
  fprintf(stderr, "\n\n");

  abort();
}

static int softbound_initialized = 0;

void __softbound_init(int is_hash_table, int is_shadow_space) 
{
  if (__SOFTBOUND_DEBUG) {
    __softbound_printf("Running __softbound_init for module\n");
  }

  if (__SOFTBOUND_HASHTABLE != is_hash_table) {
    __softbound_printf("SoftBound: Inconsistent specification of metadata encoding\n");
    abort();
  }
  
  if (is_shadow_space != __SOFTBOUND_SHADOWSPACE) {
    __softbound_printf("SoftBound: Inconsistent specification of metadata encoding\n");
    abort();
  }

  if (softbound_initialized != 0) {
    return;  // already initialized, do nothing
  }
  
  softbound_initialized = 1;

  if (__SOFTBOUND_DEBUG) {
    __softbound_printf("Initializing softbound metadata space\n");
  }
  
  if (__SOFTBOUND_HASHTABLE) {
    size_t length3 = (__SOFTBOUND_N_HASH_ENTRIES) * sizeof(__softbound_hash_table_entry_t);
    __softbound_hash_table_begin = mmap(0, length3, PROT_READ| PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE, -1, 0);

    if(__SOFTBOUND_DEBUG){
      printf("length = %zx\n", length3);
    }
    assert(__softbound_hash_table_begin != (void *)-1);  // FIXME - don't use assert, always want this to fail
    return;
  }

  if (__SOFTBOUND_SHADOWSPACE) {
    size_t length2 = (__SOFTBOUND_N_HASH_ENTRIES) * sizeof(__softbound_shadow_space_entry_t);
    __softbound_shadow_space_begin = mmap(0, length2, PROT_READ| PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS|MAP_NORESERVE, -1, 0);
    assert(__softbound_shadow_space_begin != (void*)-1);   // FIXME - don't use assert, always want this to fail
    return;
  }
}

static void softbound_init_ctype(){  
  char* ptr;
  char* base_ptr;

  ptr = (void*) __ctype_b_loc();
  base_ptr = (void*) (*(__ctype_b_loc()));
  __hashStoreBaseBound(ptr, ((char*) base_ptr - 129), ((char*) base_ptr + 256), base_ptr, 1, 1);
}

static __attribute__ ((__destructor__)) void softbound_process_memory_total()
{
  if (!__SOFTBOUND_DEBUG) {
    return;
  }

  const double MULTIPLIER = 4096.0/(1024.0*1024.0); // 4kB page size, 1024*1024 bytes per MB,
  FILE* proc_file;
  int total_size_in_pages = 0;
  int res_size_in_pages = 0;
  
  proc_file = fopen("/proc/self/statm", "r");
  fscanf(proc_file, "%d %d", &total_size_in_pages, &res_size_in_pages);

  fprintf(stderr, "memory_total = %lf MB\n", total_size_in_pages*MULTIPLIER);
  fprintf(stderr, "memory_resident = %lf MB\n", res_size_in_pages*MULTIPLIER);
}

void __softbound_printf(char* str, ...)
{
  va_list args;
  
  va_start(args, str);
  vfprintf(stderr, str, args);
  va_end(args);
}

extern int softbound_pseudo_main(int argc, char **argv, void*, void*);

int main(int argc, char **argv){

  char* new_argv[argc];
  int i;
  char* temp_ptr;
  int return_value;

  mallopt(M_MMAP_MAX, 0);
  for(i = 0; i < argc; i++) { 
    new_argv[i] = argv[i];
    //    printf("new_argv[i] = %zx\n", new_argv[i]);
    // printf("new_argv[i] + strlen(new_argv[i]) + 1= %zx\n", new_argv[i] + strlen(new_argv[i]) + 1);
    __hashStoreBaseBound(&new_argv[i], new_argv[i], new_argv[i] + strlen(new_argv[i]) + 1, new_argv[i], 0, 1); 
  }
  softbound_init_ctype();

  /* Santosh: Real Nasty hack because C programmers assume argv[argc]
   * to be NULL. Also this NUll is a pointer, doing + 1 will make the
   * size_of_type to fail 
   */
  temp_ptr = (char*) &new_argv[argc] + 8;
  new_argv[argc] = NULL;
  return_value = softbound_pseudo_main(argc, new_argv, &new_argv[0], temp_ptr);

  return return_value;
}
