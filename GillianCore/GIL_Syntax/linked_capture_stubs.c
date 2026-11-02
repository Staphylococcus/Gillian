/* Local POSIX metadata only: no program/solver semantics. */
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdint.h>
#include <limits.h>
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
static value capture_stat(struct stat *s) {
  CAMLparam0(); CAMLlocal2(out,n);
  if (s->st_size < 0 || s->st_blocks < 0 ||
      (uint64_t)s->st_blocks > INT64_MAX / 512 || s->st_blksize <= 0)
    caml_failwith("linked capture physical stat overflow");
  int64_t size=(int64_t)s->st_size, alloc=(int64_t)s->st_blocks*512;
  int64_t fields[9]={(int64_t)s->st_dev,(int64_t)s->st_ino,size,
    alloc>size?alloc:size,(int64_t)s->st_blksize,(int64_t)s->st_nlink,
    (int64_t)s->st_uid,S_ISREG(s->st_mode)?0:S_ISDIR(s->st_mode)?1:S_ISLNK(s->st_mode)?2:3,(int64_t)(s->st_mode & 07777)};
  out=caml_alloc(9,0);
  for(int i=0;i<9;i++)Field(out,i)=Val_unit;
  for(int i=0;i<9;i++){n=caml_copy_int64(fields[i]);Store_field(out,i,n);}
  CAMLreturn(out);
}
CAMLprim value gillian_capture_probe_fd(value fd) {
  CAMLparam1(fd);struct stat s;if(fstat(Int_val(fd),&s))caml_failwith("linked capture fstat");CAMLreturn(capture_stat(&s));
}
CAMLprim value gillian_capture_probe_path(value path) {
  CAMLparam1(path);struct stat s;if(lstat(String_val(path),&s))caml_failwith("linked capture lstat");CAMLreturn(capture_stat(&s));
}
CAMLprim value gillian_capture_probe_at(value fd,value name) {
  CAMLparam2(fd,name);struct stat s;if(fstatat(Int_val(fd),String_val(name),&s,AT_SYMLINK_NOFOLLOW))caml_failwith("linked capture fstatat");CAMLreturn(capture_stat(&s));
}
CAMLprim value gillian_capture_open_root(value path) {
  CAMLparam1(path);int fd=open(String_val(path),O_RDONLY|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);if(fd<0)caml_failwith("linked capture open root");CAMLreturn(Val_int(fd));
}
CAMLprim value gillian_capture_create_at(value fd,value name) {
  CAMLparam2(fd,name);int out=openat(Int_val(fd),String_val(name),O_WRONLY|O_CREAT|O_EXCL|O_NOFOLLOW|O_CLOEXEC|O_NONBLOCK,0600);if(out<0)caml_failwith("linked capture exclusive openat");CAMLreturn(Val_int(out));
}
