; ModuleID = 'scope/byteswap.c' (written by hand; see byteswap.c; htons as
; glibc declares it, __attribute__((const)), which clang reads as willreturn
; memory(none) on the declaration and the call)
source_filename = "scope/byteswap.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@.str = private unnamed_addr constant [10 x i8] c"127.0.0.1\00", align 1

define dso_local i32 @main() #0 {
  %1 = call zeroext i16 @htons(i16 noundef zeroext 27015) #2
  %z = zext i16 %1 to i32
  %2 = icmp ne i32 %z, 34665
  br i1 %2, label %err, label %3

3:
  %4 = call i32 @htonl(i32 noundef -2080177663)
  %5 = icmp ne i32 %4, 16909188
  br i1 %5, label %err, label %6

6:
  %7 = call i32 @inet_addr(ptr noundef @.str)
  %8 = icmp ne i32 %7, 16777343
  br i1 %8, label %err, label %9

9:
  ret i32 0

err:
  call void @reach_error()
  unreachable
}

declare zeroext i16 @htons(i16 noundef zeroext) #2
declare i32 @htonl(i32 noundef) #1
declare i32 @inet_addr(ptr noundef) #1
declare void @reach_error() #1

attributes #0 = { noinline nounwind uwtable }
attributes #1 = { nounwind }
attributes #2 = { nounwind willreturn memory(none) }

!llvm.module.flags = !{!90}
!90 = !{i32 2, !"Debug Info Version", i32 3}
