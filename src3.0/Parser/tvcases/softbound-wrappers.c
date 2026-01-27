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


#include <arpa/inet.h>
#include<bits/errno.h>

#include<sys/mman.h>
#include<sys/times.h>
#include<sys/types.h>
#include<sys/stat.h>
#include<sys/time.h>
#include<sys/resource.h>
#include<sys/socket.h>
#include<sys/wait.h>

#include<netinet/in.h>

#include <assert.h>
#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <grp.h>
#include <getopt.h>
#include <glob.h>
#include <limits.h>
#include <math.h>
#include <netdb.h>
#include <pwd.h>
#include <syslog.h>
#include <setjmp.h>
#include <string.h>
#include <signal.h>
#include <stdarg.h>
#include<stdio.h>
#include<stdlib.h>

#include <ttyent.h>
#include <time.h>
#include <unistd.h>
#include <utime.h>
#include <wait.h>
#include <math.h>

#include <fcntl.h>

#include "softbound.h"


__WEAK_INLINE void __softbound_store_null_return_metadata(){
  __softboundcetswithss_store_base_shadow_stack(NULL, 0);
  __softboundcetswithss_store_bound_shadow_stack(NULL, 0);
}

__WEAK_INLINE void __softbound_store_return_metadata(void* base, void* bound){

  //  printf("[store_return_metadata], base=%p, bound=%p\n", base, bound);
  __softboundcetswithss_store_base_shadow_stack(base, 0);
  __softboundcetswithss_store_bound_shadow_stack(bound, 0);
}

__WEAK_INLINE void __softboundcetswithss_propagate_metadata_shadow_stack_from(int from_argnum, int to_argnum){
  
  void* base = __softboundcetswithss_load_base_shadow_stack(from_argnum);
  void* bound = __softboundcetswithss_load_bound_shadow_stack(from_argnum);
  
  __softboundcetswithss_store_base_shadow_stack(base, to_argnum);
  __softboundcetswithss_store_bound_shadow_stack(bound, to_argnum);

}



/* wrappers for library calls (incomplete) */
//////////////////////system wrappers //////////////////////

__WEAK_INLINE int softbound_system(char* ptr) {

  return system(ptr);
}

__WEAK_INLINE int softbound_setreuid(uid_t ruid, uid_t euid) {

  /* tested */
  return setreuid(ruid, euid);
}

__WEAK_INLINE int softbound_mkstemp(char* template){
  
  /* tested */
  return mkstemp(template);
}

__WEAK_INLINE uid_t softbound_getuid(void) {

  /* tested */
  return getuid();
}

__WEAK_INLINE int softbound_getrlimit(int resource, struct rlimit* rlim){ 

  /* tested */
  return getrlimit(resource, rlim);
}

__WEAK_INLINE int softbound_setrlimit(int resource, const struct rlimit* rlim){ 

  /* tested */
  return setrlimit(resource, rlim);
}

#if 0
__WEAK_INLINE void softbound_qsort(void* base, size_t nmemb, size_t size, 
                            int (* compar)(const void *, const void *), 
                            char *base_base, char* base_bound, char* compar_base, 
                            char* compar_bound) {

  /* TODO: untested */
  //  printf("[SoftBound Warning] using untested wrapper [softbound_qsort]\n");
  qsort(base, nmemb, size, compar);

}
#endif 

__WEAK_INLINE size_t softbound_fread(void *ptr, size_t size, size_t nmemb, 
                                     FILE *stream){

  /* tested */
  return fread(ptr, size, nmemb, stream);
}

__WEAK_INLINE mode_t softbound_umask(mode_t mask) {

  /* tested */
  return umask(mask);
}

__WEAK_INLINE int softbound_mkdir(const char* pathname, mode_t mode){ 
  
  /* tested */
  return mkdir(pathname, mode);
}

__WEAK_INLINE int softbound_chroot(const char* path){

  /* tested */
  return chroot(path);
}

__WEAK_INLINE int softbound_rmdir(const char* pathname){ 

  /* tested */
  return rmdir(pathname);
}

__WEAK_INLINE int softbound_stat(const char* path, struct stat* buf){
  /* tested */
  return stat(path, buf);
}

__WEAK_INLINE int softbound_fputc(int c, FILE* stream){ 

  /* tested */
  return fputc(c, stream);
}

__WEAK_INLINE int softbound_fileno(FILE* stream){

  return fileno(stream);
}

__WEAK_INLINE int softbound_fgetc(FILE* stream){

  return fgetc(stream);
}

__WEAK_INLINE int softbound_strncmp(const char* s1, const char* s2,  size_t n){
  return strncmp(s1, s2, n);
}

__WEAK_INLINE double softbound_log(double x) {

  return log(x);
}
long long softbound_fwrite(char* ptr, size_t size, size_t nmemb, FILE* stream){ 
  return fwrite(ptr, size, nmemb, stream);
}

__WEAK_INLINE double softbound_atof(char* ptr){
  return atof(ptr);
}

__WEAK_INLINE int softbound_feof(FILE* stream){
  return feof(stream);
}

__WEAK_INLINE int softbound_remove(const char* pathname){ 

  return remove(pathname);
}

///////////////////// Math library functions here //////////////////

__WEAK_INLINE double softbound_acos(double x) {

  return acos(x);
}

__WEAK_INLINE double softbound_atan2(double y, double x) {

  return atan2(y, x);
}
__WEAK_INLINE float softbound_sqrtf(float x) {

  return sqrtf(x);
}

__WEAK_INLINE float softbound_expf(float x) {

  return expf(x);
}

double exp2(double);

__WEAK_INLINE double softbound_exp2(double x) {

  return exp2(x);
}


__WEAK_INLINE float softbound_floorf(float x) {

  return floorf(x);
}

__WEAK_INLINE double softbound_ceil(double x){

  return ceil(x);
}

__WEAK_INLINE float softbound_ceilf(float x) {

  return ceilf(x);
}
__WEAK_INLINE double softbound_floor(double x) {

  return floor(x);
}

__WEAK_INLINE double softbound_sqrt(double x) {

  return sqrt(x);
}

__WEAK_INLINE double softbound_fabs(double x) {

  return fabs(x);
}

__WEAK_INLINE void softbound_srand(unsigned int seed){
  srand(seed);
}

__WEAK_INLINE void softbound_srand48(long int seed){
  srand48(seed);
}


__WEAK_INLINE double softbound_pow(double x, double y) {
  
  return pow(x,y);

}

__WEAK_INLINE float softbound_fabsf(float x) {

  return fabsf(x);
}

__WEAK_INLINE double softbound_tan(double x ) {

  return tan(x);
}

__WEAK_INLINE float softbound_tanf(float x) {

  return tanf(x);
}

__WEAK_INLINE long double softbound_tanl(long double x) {


  return tanl(x);
}

__WEAK_INLINE double softbound_log10(double x) {

  return log10(x);
}
__WEAK_INLINE double softbound_sin(double x) {

  return sin(x);
}

__WEAK_INLINE float softbound_sinf(float x) {

  return sinf(x);
}

__WEAK_INLINE long double softbound_sinl(long double x) {

  return sinl(x);
}

__WEAK_INLINE double softbound_cos(double x) {

  return cos(x);
}

__WEAK_INLINE float softbound_cosf(float x) {

  return cosf(x);
}

__WEAK_INLINE long double softbound_cosl(long double x) {

  return cosl(x);
}

__WEAK_INLINE double softbound_exp(double x) {

  return exp(x);
}

__WEAK_INLINE double softbound_ldexp(double x, int exp) {
  
  return ldexp(x, exp);
}


////////////////File Library Wrappers here //////////////////////

__WEAK_INLINE FILE* softbound_tmpfile(){

  void* ret_ptr = tmpfile();
  void* ret_ptr_bound = ret_ptr + sizeof(FILE);
  __softbound_store_return_metadata(ret_ptr, ret_ptr_bound);
  return ret_ptr;
}

__WEAK_INLINE int softbound_ferror(FILE* stream) {
  return ferror(stream);
}

__WEAK_INLINE long softbound_ftell(FILE* stream) {

  return ftell(stream);
}

__WEAK_INLINE int softbound_fstat(int filedes, struct stat* buff) {

  return fstat(filedes, buff);
}

__WEAK_INLINE int softbound_fflush(FILE* stream){

  return fflush(stream);
}

__WEAK_INLINE int softbound_fputs(const char* s, FILE* stream){
  
  return fputs(s, stream);
}

__WEAK_INLINE FILE* softbound_fopen(const char* path, const char* mode){

  void* ret_ptr = (void*) fopen(path, mode);
  void* ret_ptr_bound = ret_ptr + sizeof(FILE);
  __softbound_store_return_metadata(ret_ptr, ret_ptr_bound);
  return (FILE*) ret_ptr;
}

__WEAK_INLINE FILE* softbound_fdopen(int fildes, const char* mode){ 

  void* ret_ptr = (void*) fdopen(fildes, mode);
  void* ret_ptr_bound = ret_ptr + sizeof(FILE);
  __softbound_store_return_metadata(ret_ptr, ret_ptr_bound);  
  return (FILE*) ret_ptr;
}


__WEAK_INLINE int softbound_fseek(FILE* stream, long offset, int whence) {

  return fseek(stream, offset, whence);
}

__WEAK_INLINE int softbound_ftruncate(int fd, off_t length) {
  return ftruncate(fd, length);
}


__WEAK_INLINE FILE* softbound_popen(const char* command, 
                                    const char* type){

  void* ret_ptr = (void*) popen(command, type);
  void* ret_ptr_bound = ret_ptr + sizeof(FILE);
  
  __softbound_store_return_metadata(ret_ptr, ret_ptr_bound);
  return (FILE*) ret_ptr;
}

__WEAK_INLINE int softbound_pclose(FILE* stream){
  return pclose(stream);
}

__WEAK_INLINE void softbound_rewind(FILE* stream){

  rewind(stream);
}

__WEAK_INLINE struct dirent* softbound_readdir(DIR* dir){
  
  void* ret_ptr = (void*) readdir(dir);
  void* ret_ptr_bound = ret_ptr + sizeof(struct dirent);

  __softbound_store_return_metadata(ret_ptr, ret_ptr_bound);
  return (struct dirent*) ret_ptr;
}

__WEAK_INLINE DIR* softbound_opendir(const char* name){ 

  void* ret_ptr = opendir(name);
  /* FIX Required, don't know the sizeof(DIR) */
  void* ret_ptr_bound = ret_ptr + 1024* 1024;
  __softbound_store_return_metadata(ret_ptr, ret_ptr_bound);
  return(DIR*) ret_ptr;

}

__WEAK_INLINE int softbound_closedir(DIR* dir) {

  return closedir(dir);
}

__WEAK_INLINE int softbound_rename(const char* old_path, const char* new_path){ 

  return rename(old_path, new_path);
}

__WEAK_INLINE void softbound_qsort(void* base, size_t nmemb, size_t size, int (*compar)(const void*, const void*)){
  
  printf("should not use qsort\n");
  __softbound_abort();
}


////////////////////unistd.h wrappers ////////////////////////////////

__WEAK_INLINE unsigned int softbound_sleep(unsigned int seconds) {

  return sleep(seconds);
}

__WEAK_INLINE char* softbound_getcwd(char* buf, size_t size){ 

  if(buf == NULL) {
    printf("This case not handled, requesting memory from system\n");
    __softbound_abort();
  }

  char* ret_ptr = getcwd(buf, size);

  void* base = __softboundcetswithss_load_base_shadow_stack(1);
  void* bound = __softboundcetswithss_load_bound_shadow_stack(1);
  
  __softbound_store_return_metadata(base, bound);
  return ret_ptr;
}

__WEAK_INLINE int softbound_chown(const char* path, uid_t owner, gid_t group){
  
  return chown(path, owner, group);
  
}

__WEAK_INLINE int softbound_isatty(int desc) {

  return isatty(desc);
}

__WEAK_INLINE int softbound_chdir(const char* path){

  return chdir(path);
}

///////////////////String related wrappers ////////////////////////////


__WEAK_INLINE void* softbound_memchr(const void * s, int c, size_t n){

  //  printf("[SoftBound Warning] using untested wrapper [softbound_memchr] \n");
  
  void* ret_ptr = memchr(s, c, n);

  if(ret_ptr != NULL){
    __softboundcetswithss_propagate_metadata_shadow_stack_from(1, 0);
  }
  else{
    __softbound_store_null_return_metadata();
  }
  
  return ret_ptr;

}

__WEAK_INLINE int softbound_strcasecmp(const char* s1, const char* s2){

  return strcasecmp(s1,s2);
}

__WEAK_INLINE int softbound_strncasecmp(const char* s1, const char* s2, size_t n){

  //printf("[SoftBound Warning] using untested wrapper [softbound_strncasecmp] \n");
  return strncasecmp(s1, s2, n);
}

__WEAK_INLINE size_t softbound_strlen(const char* s) {

  return strlen(s);
}


#if 0
__WEAK_INLINE void softbound___strpbrk_c3(struct PtrBaseBound* return_ptr, 
                              const char* s, const char* accept, 
                              char* s_base, char* s_bound, 
                              char* accept_base, char* accept_bound) {
  
  //printf("[SoftBound Warning] using untested wrapper [softbound_strpbrk] \n");
  return_ptr->ptr = strpbrk(s, accept);
  if(return_ptr->ptr != NULL) {
    return_ptr->ptr_base = s_base ;
    return_ptr->ptr_bound = s_bound ;
  }
  else {
    return_ptr->ptr_base = NULL;
    return_ptr->ptr_bound = NULL;
  }

}
#endif

__WEAK_INLINE char* softbound_strpbrk(const char* s, const char* accept){  
  //printf("[SoftBound Warning] using untested wrapper [softbound_strpbrk] \n");

  char* ret_ptr = strpbrk(s, accept);
  if(ret_ptr != NULL) {
    __softboundcetswithss_propagate_metadata_shadow_stack_from(1, 0);
  }
  else {
    __softbound_store_null_return_metadata();
  }
  return ret_ptr;
}

__WEAK_INLINE char* softbound_gets(char* s){ 
  char* ret_ptr = gets(s);
  __softboundcetswithss_propagate_metadata_shadow_stack_from(1, 0);
  return ret_ptr;
}

__WEAK_INLINE char*  softbound_fgets(char* s, int size, FILE* stream){ 

  char* ret_ptr = fgets(s, size, stream);
  __softboundcetswithss_propagate_metadata_shadow_stack_from(1,0);

  return ret_ptr;
}


__WEAK_INLINE void softbound_perror(const char* s){ 

  perror(s);
}

__WEAK_INLINE void softbound_puts(char* ptr) {
  puts(ptr);
}

__WEAK_INLINE int softbound_atoi(const char* ptr) {

  if(ptr == NULL) {
    __softbound_abort();
  }
  return atoi(ptr);
    
}

__WEAK_INLINE clock_t softbound_clock(void){

  return clock();
}

__WEAK_INLINE void softbound_exit(int status) {
  exit(status);
}

__WEAK_INLINE long softbound_atol(const char* nptr) {
  return atol(nptr);
}

__WEAK_INLINE void* softbound_malloc(size_t size) {
  
  void* ret_ptr = malloc(size);
  if(ret_ptr == NULL){
    __softbound_store_null_return_metadata();
  }
  else{
    void* base = ret_ptr;
    void* bound = (void*)((char*)ret_ptr + size);
    //    printf("in malloc, ret_ptr = %p, base=%p, bound=%p, size=%zx\n", ret_ptr, base, bound, size);
    __softbound_store_return_metadata(base, bound);
  }

  return ret_ptr;
} 


__WEAK_INLINE void* softbound_calloc(size_t nmemb, size_t size) {

  void* ret_ptr = calloc(nmemb, size);
  if(ret_ptr == NULL){
    __softbound_store_null_return_metadata();
  }
  else{
    void* base = ret_ptr;
    void* bound = (void*)((char*) ret_ptr + nmemb* size);
    __softbound_store_return_metadata(base,bound);
  }
  return ret_ptr;
}


__WEAK_INLINE void softbound_abort() {
  abort();
}

__WEAK_INLINE int softbound_rand() {
  return rand();
}

__WEAK_INLINE int softbound_fclose(FILE* fp){

  return fclose(fp);
}

__WEAK_INLINE int softbound_putchar(int c) {

  return putchar(c);
}

__WEAK_INLINE unsigned short const** softbound___ctype_b_loc() {

  unsigned short const** ret_ptr =__ctype_b_loc();
  __softbound_store_return_metadata((void*) ret_ptr, (void*) ret_ptr + sizeof(int*));
  return ret_ptr;

}


__WEAK_INLINE int softbound_strcmp(const char* s1, const char* s2){

  return strcmp(s1, s2);
}


__WEAK_INLINE clock_t softbound_times(struct tms* buf){ 
  return times(buf);
}

__WEAK_INLINE char* softbound_strcpy(char* dest, char* src){

  /* FIXME: needs a check */
  char* ret_ptr ;
  ret_ptr  = strcpy(dest,src);
  __softboundcetswithss_propagate_metadata_shadow_stack_from(1, 0);
  return ret_ptr;
}


__WEAK_INLINE double softbound_drand48(){

  return drand48();
}

__WEAK_INLINE long int softbound_lrand48(){

  return lrand48();
}


__WEAK_INLINE char* softbound_strchr(const char* s, int c){ 
  
  char* ret_ptr = strchr(s,c);  
  __softboundcetswithss_propagate_metadata_shadow_stack_from(1,0);
  return ret_ptr;
}

__WEAK_INLINE int softbound_toupper(int c) {

  return toupper(c);
}

__WEAK_INLINE int softbound_tolower(int c){

  return tolower(c);
}


__WEAK_INLINE int softbound_memcmp(const char* s1, const char* s2, size_t n){

  return memcmp(s1, s2, n);

}

__WEAK_INLINE char* softbound_strcat (char* dest, const char* src){

  char* ret_ptr = strcat(dest, src);
  __softboundcetswithss_propagate_metadata_shadow_stack_from(1, 0);
  return ret_ptr;
}

/* errno is defined as (* __errno_location()) in bits/errno.h */

__WEAK_INLINE int* softbound___errno_location() {

  int* ret_ptr = (int*) __errno_location();
  __softbound_store_return_metadata(ret_ptr, ret_ptr + sizeof(int*));

  return ret_ptr;

}

__WEAK_INLINE void softbound_free(void* ptr){
  free(ptr);
}

__WEAK_INLINE char* softbound_getenv(const char* name){
   
  char* ret_ptr = getenv(name);
   
  if(ret_ptr != NULL){
    __softbound_store_return_metadata(ret_ptr, ret_ptr+strlen(ret_ptr) + 1);
  }
  else {
    __softbound_store_null_return_metadata();
  }
  return ret_ptr;
}

__WEAK_INLINE char* softbound_strerror(int errnum) {

  char* ret_ptr = strerror(errnum);  
  __softbound_store_return_metadata(ret_ptr, ret_ptr + strlen(ret_ptr) + 1);
  return ret_ptr;
}

__WEAK_INLINE char* softbound_strrchr(const char* s, int c) {


  char* ret_ptr = strrchr(s, c);
  
  if(ret_ptr != NULL){
    __softboundcetswithss_propagate_metadata_shadow_stack_from(1, 0);
  }
  else{
    __softbound_store_return_metadata(NULL, NULL);
  }
  return ret_ptr;

} 
 __WEAK_INLINE void* softbound_realloc(void* ptr, size_t size){
  
  /* TODO: may be necessary to copy metadata */
   void* ret_ptr = realloc(ptr, size);
   __softbound_store_return_metadata(ret_ptr, (char*)(ret_ptr) + size);
   return ret_ptr;
 }


__WEAK_INLINE int softbound_open(const char *pathname, int flags){
  
  return open(pathname, flags);

}

__WEAK_INLINE ssize_t softbound_read(int fd, void* buf, size_t count) {

  return read(fd, buf, count);
}

__WEAK_INLINE ssize_t softbound_write(int fd, void* buf, size_t count) {

  return write(fd, buf, count);
}


__WEAK_INLINE off_t softbound_lseek(int fildes, off_t offset, int whence) {

  return lseek(fildes, offset, whence);
}

__WEAK_INLINE char* softbound_strstr(const char* haystack, const char* needle){
  
  char* ret_ptr = strstr(haystack, needle);
  
  if(ret_ptr == NULL){
    __softbound_store_return_metadata(NULL, NULL);
  }
  else{
    __softboundcetswithss_propagate_metadata_shadow_stack_from(1, 0);
  }
  return ret_ptr;
}

__WEAK_INLINE int softbound_strtol(const char* nptr, char **endptr, int base){
  
  //printf("[SoftBound Warning] using untested wrapper [softbound_strtol] \n");
  int temp = strtol(nptr, endptr, base);
  /* URGENT TODO:  This function requires code review */
  __hashStoreBaseBound(endptr, 
                       *endptr, 
                       *endptr + strlen(*endptr) + 1, 
                       *endptr, 1 , 1);

  return temp;
}


__WEAK_INLINE struct tm * softbound_localtime(const time_t* timep) {

  struct tm* ret_ptr = localtime(timep);
  
  if(ret_ptr == NULL){
    __softbound_store_return_metadata(NULL, NULL);
  }
  else{
    __softbound_store_return_metadata(ret_ptr, ((char*)ret_ptr + sizeof(struct tm)));
  }
  return ret_ptr;
}

__WEAK_INLINE time_t softbound_time(time_t* t) {

  return time(t);
}

__WEAK_INLINE size_t softbound_strspn(const char* s, const char* accept){

  return strspn(s, accept);
}


__WEAK_INLINE int const** softbound___ctype_toupper_loc(void) {
  
  int const** ret_ptr = __ctype_toupper_loc();
  __softbound_store_return_metadata(ret_ptr, (void*)ret_ptr + sizeof(int*));
  return ret_ptr;
}

__WEAK_INLINE int const ** softbound___ctype_tolower_loc(void) {

  int const** ret_ptr = __ctype_tolower_loc();
  __softbound_store_return_metadata(ret_ptr, (void*)ret_ptr + sizeof(int*));
  return ret_ptr;
}


 __WEAK_INLINE char*  softbound_strtok(char* str, const char* delim){

   
   char* ret_ptr = strtok(str, delim);
#if __WORDSIZE > 32
  __softbound_store_return_metadata((void*)0, (void*)(281474976710656));
#else
  __softbound_store_return_metadata((void*)0, (void*)(2147483647));
#endif
 
   return ret_ptr;
 }

typedef void(*sighandler_t)(int);

__WEAK_INLINE sighandler_t softbound_signal(int signum, sighandler_t handler){

  sighandler_t  ptr = signal(signum, handler);
  return ptr;
}


__WEAK_INLINE char* softbound_strncpy(char* dest, 
                                      char* src, size_t n){

  char* ret_ptr = strncpy(dest, src, n);
  __softboundcetswithss_propagate_metadata_shadow_stack_from(1, 0);
  return ret_ptr;
}

__WEAK_INLINE int softbound_close(int fd) {

  return close(fd);
}

typedef void (*void_func_ptr)(void);
__WEAK_INLINE int softbound_atexit(void_func_ptr function) {
  return atexit(function);
}





//// URGENT: Need Fixes ////////////////////


#if 0



/////////////string functions ////////////

__WEAK_INLINE int softbound_strtoul(const char* nptr, char** endptr, int base,
                             char* nptr_base, char* nptr_bound, 
                             char* endptr_base, char* endptr_bound) {

  //printf("[SoftBound Warning] using untested wrapper [softbound_strtoul] \n");
  int temp = strtoul(nptr, endptr, base);
  /* URGENT TODO:  This function requires code review */
  __hashStoreBaseBound(endptr, 
                       *endptr, 
                       *endptr + strlen(*endptr) + 1, 
                       *endptr, 1 , 1);
  
  return temp;

}


#endif


#if 0

#if 0
__WEAK_INLINE void softbound_rindex(struct PtrBaseBound* ptrs, char* s, int c, 
                             char* s_base, char* s_bound) {

  ptrs->ptr = rindex(s, c);
  ptrs->ptr_base = s_base;
  ptrs->ptr_bound = s_bound;

}
#endif

__WEAK_INLINE void softbound_strtok(struct PtrBaseBound* ptrs, 
                             char* str, const char* delim, 
                             char* str_base, char* str_bound, 
                             char* delim_base, char* delim_bound) {
  
  ptrs->ptr = strtok(str, delim);
  ptrs->ptr_base = 0;
#if __WORDSIZE > 32
  ptrs->ptr_bound = (void*)(281474976710656);
#else
  ptrs->ptr_bound = (void*)(2147483647);
#endif
}

__WEAK_INLINE void softbound___strdup(struct PtrBaseBound* ptrs, 
                             const char* s , 
                             char* s_base, char* s_bound) {

  ptrs->ptr = strdup(s);
  ptrs->ptr_base = ptrs->ptr;
  ptrs->ptr_bound = ptrs->ptr + strlen(s) + 1;
  /* IMP: strdup just copies the string s */
}

__WEAK_INLINE void softbound_strdup(struct PtrBaseBound* ptrs, 
                             const char* s , 
                             char* s_base, char* s_bound) {

  ptrs->ptr = strdup(s);
  ptrs->ptr_base = ptrs->ptr;
  ptrs->ptr_bound = ptrs->ptr + strlen(s) + 1;
  /* IMP: strdup just copies the string s */
}
__WEAK_INLINE size_t softbound_strcspn(const char* s, const char* reject, 
                                char* s_base, char* s_bound, 
                                char* reject_base, char* reject_bound) {

  return strcspn(s, reject);
}


__WEAK_INLINE void softbound_strncat (struct PtrBaseBound* ptrs,  char* dest, 
                               const char* src, size_t n, 
                               char* dest_base, char* dest_bound, 
                               char* src_base, char* src_bound) {
  
  ptrs->ptr = strncat(dest, src, n);
  ptrs->ptr_base = dest_base;
  ptrs->ptr_bound = dest_bound;
}








__WEAK_INLINE int softbound_sigemptyset(sigset_t* set, 
                                 char* set_base, char* set_bound) {

  return sigemptyset(set);
}
__WEAK_INLINE int softbound_setegid(gid_t egid) {

  return setegid(egid);
}

__WEAK_INLINE int softbound_initgroups(const char*  user, gid_t group, 
                                char* user_base, char* user_bound) {

  return initgroups(user, group);
}

__WEAK_INLINE int softbound_seteuid(uid_t euid) {

  return seteuid(euid);
}

__WEAK_INLINE int softbound_daemon(int nochdir, int noclose) {

  return daemon(nochdir, noclose);
}

__WEAK_INLINE int softbound_sigfillset(sigset_t* set, 
                             char* set_base, char* set_bound) {

  return sigfillset(set);
}

__WEAK_INLINE int softbound_sigprocmask(int how, const sigset_t *set, sigset_t * oldset,
                             char* set_base, char* set_bound, 
                             char* oldset_base, char* oldset_bound) {

  return sigprocmask(how, set, oldset);
}

__WEAK_INLINE void softbound_tzset() {
  /* URGENT: it initializes a global variable, need to look into the issue */ 
  tzset();
}

__WEAK_INLINE int softbound_sigaddset(sigset_t *set, int signum, 
                               char* set_base, char* set_bound) {
  return sigaddset(set, signum);
}

__WEAK_INLINE int softbound_gethostname(char* name, size_t len, 
                                 char* name_base, char* name_bound) {

  return gethostname(name, len);
}



__WEAK_INLINE void softbound_realloc(struct PtrBaseBound* ptrs, void* ptr, 
                              size_t size, 
                              void* ptr_base, void* ptr_bound) {

  void* temp;
  // printf("[SoftBound Warning] using untested wrapper [softbound_realloc] \n");
  //  printf("before realloc %zx\n", ptr);
  ptrs->ptr = ptr;
  temp = realloc(ptr, size);
  ptrs->ptr = temp;
  //  printf("after realloc temp = %zx, ptr = %zx\n", temp, ptrs->ptr);
  ptrs->ptr_base = ptrs->ptr;
  ptrs->ptr_bound = (char*)((char*)(ptrs->ptr) + size);

}

__WEAK_INLINE void softbound_gmtime(struct PtrBaseBound* ptrs, const time_t* timep,
                             char* timep_base, char* timep_bound) {
  
  ptrs->ptr = (void*)gmtime(timep);
  ptrs->ptr_base = ptrs->ptr;
  ptrs->ptr_bound = ptrs->ptr + sizeof(struct tm);

}







////////////////////Time Related Library Wrappers//////////////////////////

__WEAK_INLINE int softbound_utime(const char* filename, const struct utimbuf* buf, 
                           char* filename_base, char* filename_bound, 
                           char* buf_base, char* buf_bound) {

  return utime(filename, buf);
}

__WEAK_INLINE void softbound_ctime(struct PtrBaseBound* ptrs, const time_t* timep, 
                            char* timep_base, char* timep_bound) {
  
  ptrs->ptr = ctime(timep);
  ptrs->ptr_base = ptrs->ptr;
  ptrs->ptr_bound = ((char*) ptrs->ptr) + strlen(ptrs->ptr) + 1;

}



__WEAK_INLINE double softbound_difftime(time_t time1, time_t time0) {
  
  return difftime(time1, time0);
} 


__WEAK_INLINE void softbound_setbuf(FILE* stream, char* buf, 
                             char* stream_base, char* stream_bound, 
                             char* buf_base, char* buf_bound) {

  setbuf(stream, buf);
}


__WEAK_INLINE int softbound_getopt(int argc, char* argv[], const char* optstring, 
                            char* argv_base, char* argv_bound, 
                            char* optstring_base, char* optstring_bound) {

  return getopt(argc, argv, optstring);
}

__WEAK_INLINE int softbound_getopt_long(int argc, char* const argv[], const char* optstring, 
                                 const struct option* longopts, int* longindex, 
                                 char* argv_base, char* argv_bound, 
                                 char* optstring_base, char* optstring_bound, 
                                 char* longopts_base, char* longopts_bound, 
                                 char* longindex_base, char* longindex_bound) {

  return getopt_long(argc, argv, optstring, longopts, longindex);

}

__WEAK_INLINE int softbound_chmod (const char* path, mode_t mode, 
                            char* path_base, char* path_bound) {

  return chmod(path, mode);
}

__WEAK_INLINE int softbound_lstat(const char* path, struct stat* buf, 
                           char* path_base, char* path_bound, 
                           char* buf_base, char* buf_bound) {
  
  return lstat(path, buf);
}






////////////// Network wrappers //////////////////////////


__WEAK_INLINE in_addr_t softbound_inet_addr(const char* cp,
                                     char* cp_base, char* cp_bound) {

  return inet_addr(cp);
}

__WEAK_INLINE int softbound_getpeername(int s, struct sockaddr * name, socklen_t *namelen, 
                                 char* name_base, char* name_bound, 
                                 char* namelen_base, char* namelen_bound) {
  
  /* Confirm actually nothing to set here */
  return getpeername(s, name, namelen);
}

__WEAK_INLINE int softbound_getsockname(int s, struct sockaddr* name, socklen_t *namelen, 
                                 char* name_base, char* name_bound, 
                                 char* namelen_base, char* namelen_bound) {

  /* Confirm actually nothing here */
  return getsockname(s, name, namelen);
}


__WEAK_INLINE void  softbound_inet_ntoa(struct PtrBaseBound* ptrs, struct in_addr in) {
  ptrs->ptr = inet_ntoa(in);
  ptrs->ptr_base = ptrs->ptr;
  ptrs->ptr_bound = ptrs->ptr + strlen(ptrs->ptr) + 1;
}

__WEAK_INLINE int softbound_socket(int domain, int type, int protocol) {

  return socket(domain, type, protocol);
}
__WEAK_INLINE int softbound_bind( int sockfd, const struct sockaddr* my_addr, 
                           socklen_t addrlen, 
                           char* my_addr_base, char* my_addr_bound) {

  return bind(sockfd, my_addr, addrlen);
}

__WEAK_INLINE int softbound_connect(int sockfd, const struct sockaddr* serv_addr, 
                             socklen_t addrlen, 
                             char* serv_addr_base, char* serv_addr_bound) {

  return connect(sockfd, serv_addr, addrlen);
}

__WEAK_INLINE uint16_t softbound_ntohs(uint16_t netshort) {

  return ntohs(netshort);
}

__WEAK_INLINE uint16_t softbound_htons(uint16_t hostshort) {

  return htons(hostshort);
}

__WEAK_INLINE int softbound_unlink(const char* pathname, 
                            char* pathname_base, char* pathname_bound) {

  return unlink(pathname);
}



__WEAK_INLINE void softbound_openlog(const char* ident, int option, int facility, 
                              char* ident_base, char* ident_bound) {

  openlog(ident, option, facility);
}

__WEAK_INLINE ssize_t softbound_send(int s , const void* buf, size_t len, int flags, 
                              char* buf_base, char* buf_bound) {

  return send(s, buf, len, flags);
}

__WEAK_INLINE void softbound_getpwuid(struct PtrBaseBound* ptrs, uid_t uid) {
  
  /* URGENT:TODO needs code review */
  //printf("[SoftBound Warning] using untested wrapper [softbound_getpwuid] \n");
  ptrs->ptr = (void*) getpwuid(uid);

  if(ptrs->ptr != NULL) {
    ptrs->ptr_base = ptrs->ptr;
    ptrs->ptr_bound = ptrs->ptr + sizeof(struct passwd);
    /* struct passwd has the following fields 
     * char* pw_name,
     * char* pw_passwd,
     * char* pw_uid,
     * uid_t pw_uid,
     * gid_t pw_gid,
     * char* pw_gecos,
     * char* pw_dir,
     * char* pw_shell
     */
    
    struct passwd* temp = (struct passwd *) (ptrs->ptr);
    
    __hashStoreBaseBound(&temp->pw_name, 
                         temp->pw_name,
                         temp->pw_name + strlen(temp->pw_name) + 1,
                         temp->pw_name, 0, 1);

    __hashStoreBaseBound(&temp->pw_passwd,
                         temp->pw_passwd,
                         temp->pw_passwd + strlen(temp->pw_passwd) + 1,
                         temp->pw_passwd, 0 , 1);



    __hashStoreBaseBound(&temp->pw_gecos,
                         temp->pw_gecos,
                         temp->pw_gecos + strlen(temp->pw_gecos) + 1,
                         temp->pw_gecos, 0, 1);

    __hashStoreBaseBound(&temp->pw_dir,
                         temp->pw_dir,
                         temp->pw_dir + strlen(temp->pw_dir) + 1,
                         temp->pw_dir, 0, 1);

    __hashStoreBaseBound(&temp->pw_shell,
                         temp->pw_shell,
                         temp->pw_shell + strlen(temp->pw_shell) + 1,
                         temp->pw_shell, 0, 1);


  }
  else {
    ptrs->ptr_base = NULL;
    ptrs->ptr_bound = NULL;
  }
  

}

__WEAK_INLINE void softbound_getgrgid(struct PtrBaseBound* ptrs, gid_t gid) {

  //printf("[SoftBound Warning] using untested wrapper [softbound_getgrgid] \n");
  /* URGENT: TODO, needs code review */
  ptrs->ptr = (void*) getgrgid(gid);

  if(ptrs->ptr != NULL) {

    struct group* temp = (struct group*) getgrgid(gid);

    __hashStoreBaseBound(&temp->gr_name,
                         temp->gr_name,
                         temp->gr_name + strlen(temp->gr_name) + 1,
                         temp->gr_name, 1, 1);

    __hashStoreBaseBound(&temp->gr_passwd,
                         temp->gr_passwd,
                         temp->gr_passwd + strlen(temp->gr_passwd) + 1,
                         temp->gr_passwd, 1, 1);

    char** gr_mem_temp = temp->gr_mem;

    if(gr_mem_temp) {
      int i = 0;

      while(gr_mem_temp[i]) {
        
        __hashStoreBaseBound(&gr_mem_temp[i],
                             gr_mem_temp[i],
                             gr_mem_temp[i] + strlen(gr_mem_temp[i]) + 1,
                             gr_mem_temp[i], 1, 1);

        i++;

      }
      __hashStoreBaseBound(&temp->gr_mem,
                           temp->gr_mem,
                           temp->gr_mem + (i + 1),
                           temp->gr_mem, 1, 1);
    }

  }
  else {
    ptrs->ptr_base = NULL;
    ptrs->ptr_bound = NULL;

  }

}

__WEAK_INLINE void softbound_getpwnam(struct PtrBaseBound* ptrs, const char* name, 
                               char* name_base, char* name_bound) {

  //printf("[SoftBound Warning] using untested wrapper [softbound_getpwnam] \n");
  /* URGENT: Needs code review */
  ptrs->ptr = (void*) getpwnam(name);

  /* do the stores to the metadata space here */
  if(ptrs->ptr != NULL) {

    ptrs->ptr_base = ptrs->ptr;
    ptrs->ptr_bound = ptrs->ptr + sizeof(struct passwd);

    /* struct passwd has the following fields 
     * char* pw_name,
     * char* pw_passwd,
     * char* pw_uid,
     * uid_t pw_uid,
     * gid_t pw_gid,
     * char* pw_gecos,
     * char* pw_dir,
     * char* pw_shell
     */

    struct passwd* temp = (struct passwd *)(ptrs->ptr);    
    __hashStoreBaseBound(&temp->pw_name, 
                         temp->pw_name, 
                         temp->pw_name + strlen(temp->pw_name) + 1, 
                         temp->pw_name, 0, 1);
    
    __hashStoreBaseBound(&temp->pw_passwd, 
                         temp->pw_passwd, 
                         temp->pw_passwd + strlen(temp->pw_passwd) + 1, 
                         temp->pw_passwd, 0, 1);

    __hashStoreBaseBound(&temp->pw_gecos, 
                         temp->pw_gecos, 
                         temp->pw_gecos + strlen(temp->pw_gecos) + 1, 
                         temp->pw_gecos, 0, 1);
    
    __hashStoreBaseBound(&temp->pw_dir, 
                         temp->pw_dir, 
                         temp->pw_dir + strlen(temp->pw_dir) + 1,  
                         temp->pw_dir, 0, 1);

    __hashStoreBaseBound(&temp->pw_shell, 
                         temp->pw_shell, 
                         temp->pw_shell + strlen(temp->pw_shell) + 1, 
                         temp->pw_shell, 0, 1);
  }
  else {
    ptrs->ptr_base = NULL;
    ptrs->ptr_bound = NULL;
  }
}

__WEAK_INLINE int softbound_setgid(gid_t gid) {
  
  return setgid(gid);
}

__WEAK_INLINE int softbound_setuid(uid_t uid) {

  return setuid(uid);
}

__WEAK_INLINE int softbound_setenv(const char* name, const char* value, int overwrite, 
                            const char* name_base, const char* name_bound, 
                            const char* value_base, const char* value_bound) {

  return setenv(name, value, overwrite);
}

__WEAK_INLINE void softbound_closelog(void) {
  
  closelog();
}


__WEAK_INLINE int softbound_listen(int sockfd, int backlog) {

  return listen(sockfd, backlog);
}

__WEAK_INLINE pid_t softbound_getpid(void) {

  return getpid();
}

__WEAK_INLINE pid_t softbound_waitpid(pid_t pid, int* status, int options, 
                               char* status_base, char* status_bound) {

  return waitpid(pid, status, options);
}
__WEAK_INLINE int softbound_accept(int sockfd, struct sockaddr* addr, socklen_t* addrlen, 
                            char* addr_base, char* addr_bound, 
                            char* addrlen_base, char* addrlen_bound) {

  return accept(sockfd, addr, addrlen);
}

__WEAK_INLINE uint32_t softbound_htonl(uint32_t hostlong) {

  return htonl(hostlong);
}
__WEAK_INLINE ssize_t softbound_recv(int s, void* buf, size_t len, int flags, 
                              char* buf_base, char* buf_bound) {

  return recv(s, buf, len, flags);
}

__WEAK_INLINE pid_t softbound_wait3(int* status, int options, struct rusage* rusage,
                             char* status_base, char* status_bound,
                             char* rusage_base, char* rusage_bound) {
  /* URGENT: rusage field may have pointer types */

  return wait3(status, options, rusage);
}

__WEAK_INLINE void softbound__exit(int status) {
  _exit(status);
}

__WEAK_INLINE void softbound_endusershell() {
  return endusershell();
}

__WEAK_INLINE void softbound_getusershell(struct PtrBaseBound* ptrs) {
  ptrs->ptr = getusershell();
  if(ptrs->ptr) {

    ptrs->ptr_base = ptrs->ptr;
    ptrs->ptr_bound = ptrs->ptr + strlen(ptrs->ptr) + 1;
  }
  else {
    ptrs->ptr_base = NULL;
    ptrs->ptr_bound = NULL;
    
  }
}

__WEAK_INLINE int softbound_getdtablesize() {

  return getdtablesize();
}
__WEAK_INLINE void softbound_realpath(struct PtrBaseBound* ptrs, const char* path,
                               char* resolved_path, 
                               char* path_base, char* path_bound, 
                               char* resolved_path_base, char* resolved_path_bound) {

  ptrs->ptr = realpath(path, resolved_path);
  ptrs->ptr_base = resolved_path_base;
  ptrs->ptr_bound = resolved_path_bound;

}
__WEAK_INLINE unsigned int softbound_alarm(unsigned int seconds) {

  return alarm(seconds);
}

/* URGENT mmap will not have base and bound */
__WEAK_INLINE unsigned int softbound_munmap(void* start, size_t length, 
                                     char* start_base, char* start_bound) {

  return munmap(start, length);
}

__WEAK_INLINE int softbound_setsockopt(int s, int level, int optname, const void* optval, 
                                socklen_t optlen, 
                                char* optval_base, char* optval_bound, 
                                char* optlen_base, char* optlen_bound) {

  return setsockopt(s, level, optname, optval, optlen);
}

__WEAK_INLINE int softbound_fchmod(int fildes, mode_t mode) {

  return fchmod(fildes, mode);
}

__WEAK_INLINE int softbound_getnameinfo(const struct sockaddr* sa, socklen_t salen, 
                                 char* host, size_t hostlen,
                                 char* serv, size_t servlen, int flags,
                                 char* sa_base, char* sa_bound,
                                 char* host_base, char* host_bound,
                                 char* serv_base, char* serv_bound) {

  return getnameinfo(sa, salen, host, hostlen, serv, servlen, flags);
}

#if 0
__WEAK_INLINE int softbound_alphasort(const void* a, const void* b, 
                               char* a_base, char* a_bound,
                               char* b_base, char* b_bound) {

  return alphasort(a, b);
}
#endif
__WEAK_INLINE int softbound_select(int nfds, fd_set* readfds, fd_set* writefds,
                            fd_set* exceptfds, struct timeval* timeout,
                            char* readfds_base, char* readfds_bound,
                            char* writefds_base, char* writefds_bound,
                            char* exceptfds_base, char* exceptfds_bound,
                            char* timeout_base, char* timeout_bound) {
  return select(nfds, readfds, writefds, exceptfds, timeout);
}

__WEAK_INLINE size_t softbound_strftime(char* s, size_t max, const char* format, 
                       const struct tm* tm, char* s_base, char* s_bound,
                       char* format_base, char* format_bound,
                       char* tm_base, char* tm_bound) {
  
  return strftime(s, max, format, tm);
}

#if 0
__WEAK_INLINE int softbound_scandir(const char* dir, struct dirent*** namelist,
                             int (*filter)(const struct dirent *),
                             int (*compar)(const void *, const void *),
                             char* dir_base, char* dir_bound,
                             char* namelist_base, char* namelist_bound,
                             char* filter_base, char* filter_bound,
                             char* compar_base, char* compar_bound ) {

  /* TODO: URGENT: need to test this */
  /* Need to set the base and bound for namelist */

  //printf("[SoftBound Warning] using untested wrapper [softbound_scandir] \n");
  int temp = scandir(dir, namelist, filter, compar);
  
  if(namelist) {
    int i = 0;
    struct dirent** namelist_temp = *namelist;
    while(i < temp) {
      __hashStoreBaseBound(&namelist_temp[i]->d_name, 
                           namelist_temp[i]->d_name, 
                           namelist_temp[i]->d_name + 256, 
                           namelist_temp[i]->d_name, 1, 1);
      
      __hashStoreBaseBound(&namelist_temp[i],
                           namelist_temp[i] , 
                           namelist_temp[i] + sizeof(struct dirent), 
                           namelist_temp[i], 1, 1);
    }
    __hashStoreBaseBound(namelist, 
                         *namelist, 
                         *namelist + temp, 
                         *namelist, 8, 1);
  }                       
  return temp;
}
#endif

__WEAK_INLINE int softbound_usleep(useconds_t usec) {

  return usleep(usec);
}


__WEAK_INLINE void softbound_gethostbyaddr(struct PtrBaseBound* ptrs, const void* addr, 
                                    int len, int type, 
                                    char* addr_base, char* addr_bound) {

  //printf("[SoftBound Warning] using untested wrapper [softbound_gethostbyaddr] \n");
  ptrs->ptr = (void*)gethostbyaddr(addr, len, type);
  ptrs->ptr_base = ptrs->ptr;
  ptrs->ptr_bound = ptrs->ptr + sizeof(struct hostent);
  
  /* struct hostent has the following fields 
   * char* h_name;
   * char** h_aliases;
   * int h_addrtype;
   * int h_length
   * char **h_addr_list
   */
  struct hostent* temp = (struct hostent *) ptrs->ptr;

  __hashStoreBaseBound(&temp->h_name, 
                       temp->h_name, 
                       temp->h_name + strlen(temp->h_name), 
                       temp->h_name, 1, 1);
  
  int i = 0;

  /* identify the number of pointers to strings */
  if(temp->h_aliases) {
    while(temp->h_aliases[i]) {
      
      __hashStoreBaseBound(&temp->h_aliases[i], 
                           temp->h_aliases[i], 
                           temp->h_aliases[i] + strlen(temp->h_aliases[i]), 
                           temp->h_aliases[i], 1, 1);
      i++;
    }
    __hashStoreBaseBound(&temp->h_aliases, 
                         temp->h_aliases, 
                         temp->h_aliases + (i + 1), 
                         temp->h_aliases, sizeof(char*), 1);
  }
  
  i = 0;
  if(temp->h_addr_list) {    
    while(temp->h_addr_list[i]) {   
      __hashStoreBaseBound(&temp->h_addr_list[i], 
                           temp->h_addr_list[i], 
                           temp->h_addr_list[i] + strlen(temp->h_addr_list[i]), 
                           temp->h_addr_list[i], 1, 1);
      i++;
    }
    __hashStoreBaseBound(&temp->h_addr_list, 
                         temp->h_addr_list, 
                         temp->h_addr_list + (i + 1), 
                         temp->h_addr_list, 1, 1);
  }  
}

__WEAK_INLINE void softbound_gethostbyname(struct PtrBaseBound* ptrs, const char* name, 
                                    char* name_base, char* name_bound) {
  
  //printf("[SoftBound Warning] using untested wrapper [softbound_gethostbyname] \n");
  /* TODO: This entire wrapper needs to be tested */
  ptrs->ptr = (void*)gethostbyname(name);
  ptrs->ptr_base = ptrs->ptr;
  ptrs->ptr_bound = ptrs->ptr + sizeof(struct hostent);
  
  /* struct hostent has the following fields 
   * char* h_name;
   * char** h_aliases;
   * int h_addrtype;
   * int h_length
   * char **h_addr_list
   */
  struct hostent* temp = (struct hostent *) ptrs->ptr;

  __hashStoreBaseBound(&temp->h_name, 
                       temp->h_name, 
                       temp->h_name + strlen(temp->h_name), 
                       temp->h_name, 1, 1);
  
  int i = 0;

  /* identify the number of pointers to strings */
  if(temp->h_aliases) {
    while(temp->h_aliases[i]) {
      
      __hashStoreBaseBound(&temp->h_aliases[i], 
                           temp->h_aliases[i], 
                           temp->h_aliases[i] + strlen(temp->h_aliases[i]), 
                           temp->h_aliases[i], 1, 1);
      i++;
    }
    __hashStoreBaseBound(&temp->h_aliases, 
                         temp->h_aliases, 
                         temp->h_aliases + (i + 1), 
                         temp->h_aliases, sizeof(char*), 1);
  }
  
  i = 0;
  if(temp->h_addr_list) {    
    while(temp->h_addr_list[i]) {   
      __hashStoreBaseBound(&temp->h_addr_list[i], 
                           temp->h_addr_list[i], 
                           temp->h_addr_list[i] + strlen(temp->h_addr_list[i]),
                           temp->h_addr_list[i], 1, 1);
      i++;
    }
    __hashStoreBaseBound(&temp->h_addr_list, 
                         temp->h_addr_list, 
                         temp->h_addr_list + (i + 1), 
                         temp->h_addr_list, 1, 1);
  }
}


__WEAK_INLINE int softbound_getaddrinfo(const char* node, const char* service, 
                                 const struct addrinfo* hints,
                                 struct addrinfo** res, 
                                 char* node_base, char* node_bound,
                                 char* service_base, char* service_bound,
                                 char* hints_base, char* hints_bound,
                                 char* res_base, char* res_bound) {

  //printf("[SoftBound Warning] using untested wrapper [softbound_getaddrinfo] \n");
  int ret_int = getaddrinfo(node, service, hints, res);

  /* getaddrinfo creates a linked list of addrinfo nodes in res !!!!*/

  struct addrinfo *temp = *res;

  __hashStoreBaseBound(res, 
                       temp, 
                       (char *) temp + sizeof(struct addrinfo), 
                       temp, 1, 1);
  while(temp) {
    
    __hashStoreBaseBound(&temp->ai_addr, 
                         temp->ai_addr, 
                         (char*) temp->ai_addr + sizeof(struct sockaddr),
                         temp->ai_addr, 1, 1);


    __hashStoreBaseBound(&temp->ai_canonname, 
                         temp->ai_canonname, 
                         temp->ai_canonname + strlen(temp->ai_canonname) + 1, 
                         temp->ai_canonname, 1, 1);

    if(temp->ai_next) {
      __hashStoreBaseBound(&temp->ai_next, 
                           temp->ai_next, 
                           (char*) temp->ai_next + sizeof(struct addrinfo), 
                           temp->ai_next, 1, 1);
    }

    temp= temp->ai_next;
                           
  }
  return ret_int;

}


/* FIXME:TODO:URGENT: MMAP returns a pointer and its currently
 * softbound_defined 
 */

#define  _XOPEN_SOURCE
char* crypt(const char*, const char*);
__WEAK_INLINE void softbound_crypt(struct PtrBaseBound* ptrs, const char* key, const char* salt,
                            char* key_base, char* key_bound,
                            char* salt_base, char* salt_bound) {


  ptrs->ptr = (void *)crypt(key, salt);
  ptrs->ptr_base = ptrs->ptr;
  ptrs->ptr_bound = ptrs->ptr + strlen(ptrs->ptr) + 1;
}



__WEAK_INLINE int softbound_vprintf(const char* format, va_list ap, 
                             char* format_base, char* format_bound, 
                             char* ap_base, char* ap_bound) {

  return vprintf(format, ap);
}

__WEAK_INLINE void softbound_my_mmap(struct PtrBaseBound* ptrs, void* start, size_t length,
                              int prot, int flags, int fd, off_t offset ,
                              char* start_base, char* start_bound) {
  
  //printf("[SoftBound Warning] using untested wrapper [softbound_my_mmap] \n");
  ptrs->ptr = mmap(start, length, prot, flags, fd, offset);
  if(ptrs->ptr) {
    ptrs->ptr_base = ptrs->ptr;
    ptrs->ptr_bound = ptrs->ptr + length;
  }
  else {

    ptrs->ptr_base = NULL;
    ptrs->ptr_bound = NULL;
  }

}

__WEAK_INLINE void softbound_getservbyname(struct PtrBaseBound* ptrs, const char* name, 
                                    char* proto, char* name_base, char* name_bound,
                                    char* proto_base, char* proto_bound) {

  //printf("[SoftBound Warning] using untested getservbyname wrapper [softbound_getservbyname] \n");
  ptrs->ptr = (void *) getservbyname(name, proto);
  ptrs->ptr_base = ptrs->ptr;
  ptrs->ptr_bound = ptrs->ptr + sizeof(struct servent);

  struct servent* temp = (struct servent*) ptrs->ptr;
  __hashStoreBaseBound(&temp->s_name, 
                       temp->s_name, 
                       temp->s_name + strlen(temp->s_name) + 1, 
                       temp->s_name, 1, 1);

  int i = 0;

  if(temp->s_aliases) {    
    while( temp->s_aliases[i]) {
      __hashStoreBaseBound(&temp->s_aliases[i], 
                           temp->s_aliases[i], 
                           temp->s_aliases[i] + strlen(temp->s_aliases[i]) + 1, 
                           temp->s_aliases[i], 1, 1);
      i++;
    }
    __hashStoreBaseBound(&temp->s_aliases, 
                         temp->s_aliases, 
                         temp->s_aliases + (i + 1), 
                         temp->s_aliases, 8, 1);
  }  
  __hashStoreBaseBound(&temp->s_proto, 
                       temp->s_proto, 
                       temp->s_proto + strlen(temp->s_proto) + 1,
                       temp->s_proto, 1, 1 );
}



////////////////////////////glob wrappers //////////////////////////

__WEAK_INLINE int softbound_glob(const char *pattern, int flags,
                                                int(*errfunc)(const char *epath, int eerrno),
                                                glob_t *pglob, 
                                                char* pattern_base, char* pattern_bound,
                                                char* errfunc_base, char* errfunc_bound,
                                                char* pglob_base, char* pglob_bound ) {
  
  //printf("[SoftBound Warning] using untested wrapper [softbound_glob] \n");
  int temp = glob(pattern, flags, errfunc, pglob);
  size_t gl_offs = pglob->gl_offs;
  size_t i = gl_offs;

  while(pglob->gl_pathv[i]) {    
    __hashStoreBaseBound(&pglob->gl_pathv[i], 
                         pglob->gl_pathv[i], 
                         pglob->gl_pathv[i] + strlen(pglob->gl_pathv[i]) + 1, 
                         pglob->gl_pathv[i], 1, 1);
    i++;
  }

  __hashStoreBaseBound(&pglob->gl_pathv, 
                       pglob->gl_pathv, 
                       pglob->gl_pathv + i + 1, 
                       pglob->gl_pathv,
                       8, 1);

  return temp;
}

void softbound_globfree(glob_t* pglob, 
                        char* pglob_base, char* pglob_bound) {
  // TODO: untested
  globfree(pglob);
}


///////////////////////////////////////////////////////////////////


__WEAK_INLINE void softbound_getttyent(struct PtrBaseBound* ptrs) {

  // TODO: untested
  //printf("[SoftBound Warning] using untested gettyent wrapper [softbound_getttyent] \n");
  ptrs->ptr = (void *) getttyent();
  ptrs->ptr_base = ptrs->ptr;
  ptrs->ptr_bound = ptrs->ptr + sizeof(struct ttyent);
  
  struct ttyent* temp = (struct ttyent*)(ptrs->ptr);
  __hashStoreBaseBound(&temp->ty_name, 
                       temp->ty_name, 
                       temp->ty_name + strlen(temp->ty_name) + 1, 
                       temp->ty_name, 1, 1);
  
  __hashStoreBaseBound(&temp->ty_getty, 
                       temp->ty_getty, 
                       temp->ty_getty + strlen(temp->ty_getty) + 1,
                       temp->ty_getty, 1, 1);
  
  __hashStoreBaseBound(&temp->ty_type, 
                       temp->ty_type, 
                       temp->ty_type + strlen(temp->ty_type) + 1,
                       temp->ty_type, 1, 1);
  
  __hashStoreBaseBound(&temp->ty_window, 
                       temp->ty_window, 
                       temp->ty_type + strlen(temp->ty_window) + 1,
                       temp->ty_window, 1, 1);
  
  __hashStoreBaseBound(&temp->ty_comment, 
                       temp->ty_comment, 
                       temp->ty_comment + strlen(temp->ty_comment) + 1,
                       temp->ty_comment, 1, 1);

}

__WEAK_INLINE void softbound_bcopy(const void *src, void* dest, size_t n,
                            char* src_base, char* src_bound,
                            char* dest_base, char* dest_bound ) {

  /* TODO: untested */
  /* TODO: URGENT: Assert that you are not copying pointers */
  bcopy(src, dest, n);

}

#if 0
__WEAK_INLINE int softbound__setjmp(jmp_buf env, char* env_base, char* env_bound) {  
  return _setjmp(env);
}
__WEAK_INLINE void softbound_longjmp(jmp_buf env, int val, char* env_base, char* env_bound) {

  longjmp(env, val);
}

#endif

#endif

///////////////////////////////////////////////
