; ModuleID = 'scope/inethex.c' (written by hand)
; int main(void) { return inet_addr("0x7f.0.0.1") == 0; }
source_filename = "scope/inethex.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@.str = private unnamed_addr constant [11 x i8] c"0x7f.0.0.1\00", align 1

define dso_local i32 @main() #0 {
  %1 = call i32 @inet_addr(ptr noundef @.str)
  %2 = icmp eq i32 %1, 0
  %3 = zext i1 %2 to i32
  ret i32 %3
}

declare i32 @inet_addr(ptr noundef) #1

attributes #0 = { noinline nounwind uwtable }
attributes #1 = { nounwind }

!llvm.module.flags = !{!90}
!90 = !{i32 2, !"Debug Info Version", i32 3}
