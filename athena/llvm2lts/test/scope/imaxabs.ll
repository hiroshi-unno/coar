; ModuleID = 'scope/imaxabs.c' (written by hand; see imaxabs.c)
source_filename = "scope/imaxabs.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define dso_local i32 @main() #0 {
  call void @llvm.experimental.noalias.scope.decl(metadata !0)
  %1 = call i64 @__VERIFIER_nondet_long()
  %2 = call i64 @imaxabs(i64 noundef %1)
  %3 = icmp slt i64 %2, 0
  br i1 %3, label %err, label %4

4:
  ret i32 0

err:
  call void @reach_error()
  unreachable
}

declare void @llvm.experimental.noalias.scope.decl(metadata)
declare i64 @__VERIFIER_nondet_long() #1
declare i64 @imaxabs(i64 noundef) #1
declare void @reach_error() #1

attributes #0 = { noinline nounwind uwtable }
attributes #1 = { nounwind }

!0 = !{!1}
!1 = distinct !{!1, !2, !"main: x"}
!2 = distinct !{!2, !"main"}

!llvm.module.flags = !{!90}
!90 = !{i32 2, !"Debug Info Version", i32 3}
