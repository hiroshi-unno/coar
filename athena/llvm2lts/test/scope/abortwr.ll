; ModuleID = 'scope/abortwr.c' (written by hand)
; abort declared willreturn, which it cannot keep: the promise is refused
source_filename = "scope/abortwr.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define dso_local i32 @main() #0 {
  call void @abort() #1
  unreachable
}

declare void @abort() #1

attributes #0 = { noinline nounwind uwtable }
attributes #1 = { nounwind willreturn }

!llvm.module.flags = !{!90}
!90 = !{i32 2, !"Debug Info Version", i32 3}
