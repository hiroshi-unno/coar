; ModuleID = 'scope/socket.c' (written by hand; see socket.c)
source_filename = "scope/socket.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define dso_local i32 @main() #0 {
  %1 = call i32 @socket(i32 noundef 2, i32 noundef 1, i32 noundef 6)
  %2 = icmp slt i32 %1, -1
  br i1 %2, label %err, label %3

3:
  %4 = call i32 @listen(i32 noundef %1, i32 noundef 5)
  %5 = icmp sgt i32 %4, 0
  br i1 %5, label %err, label %6

6:
  %7 = call i32 @accept(i32 noundef %1, ptr noundef null, ptr noundef null)
  %8 = icmp slt i32 %7, -1
  br i1 %8, label %err, label %9

9:
  %10 = call i32 @close(i32 noundef %7)
  %11 = call i32 @close(i32 noundef %1)
  %12 = icmp sgt i32 %11, 0
  br i1 %12, label %err, label %13

13:
  ret i32 0

err:
  call void @reach_error()
  unreachable
}

declare i32 @socket(i32 noundef, i32 noundef, i32 noundef) #1
declare i32 @listen(i32 noundef, i32 noundef) #1
declare i32 @accept(i32 noundef, ptr noundef, ptr noundef) #1
declare i32 @close(i32 noundef) #1
declare void @reach_error() #1

attributes #0 = { noinline nounwind uwtable }
attributes #1 = { nounwind }

!llvm.module.flags = !{!90}
!90 = !{i32 2, !"Debug Info Version", i32 3}
