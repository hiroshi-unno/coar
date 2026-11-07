; ModuleID = 'scope/socket2.c' (written by hand)
; int socket(int, int); int main(void) { return socket(2, 1); }
source_filename = "scope/socket2.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define dso_local i32 @main() #0 {
  %1 = call i32 @socket(i32 noundef 2, i32 noundef 1)
  ret i32 %1
}

declare i32 @socket(i32 noundef, i32 noundef) #1

attributes #0 = { noinline nounwind uwtable }
attributes #1 = { nounwind }

!llvm.module.flags = !{!90}
!90 = !{i32 2, !"Debug Info Version", i32 3}
