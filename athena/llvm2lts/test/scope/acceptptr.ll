; ModuleID = 'scope/acceptptr.c' (written by hand)
; int main(void) { int len; accept(3, 0, &len); return 0; }
source_filename = "scope/acceptptr.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define dso_local i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = call i32 @accept(i32 noundef 3, ptr noundef null, ptr noundef %1)
  ret i32 0
}

declare i32 @accept(i32 noundef, ptr noundef, ptr noundef) #1

attributes #0 = { noinline nounwind uwtable }
attributes #1 = { nounwind }

!llvm.module.flags = !{!90}
!90 = !{i32 2, !"Debug Info Version", i32 3}
