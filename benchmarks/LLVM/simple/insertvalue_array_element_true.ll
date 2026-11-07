; An insertvalue whose indices pass through an array inside a struct:
; s.a[1] = 5 written into a struct value, the value stored, and s.a[1] read
; back from memory.  The read gives 5, so reach_error is unreachable (YES).
; Hand-written LLVM 19 IR.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare void @reach_error()

define i32 @main() {
entry:
  %slot = alloca { [2 x i32] }, align 4
  %s0 = insertvalue { [2 x i32] } undef, i32 0, 0, 0
  %s1 = insertvalue { [2 x i32] } %s0, i32 0, 0, 1
  %s2 = insertvalue { [2 x i32] } %s1, i32 5, 0, 1
  store { [2 x i32] } %s2, ptr %slot, align 4
  %p = getelementptr inbounds { [2 x i32] }, ptr %slot, i64 0, i32 0, i64 1
  %v = load i32, ptr %p, align 4
  %bad = icmp ne i32 %v, 5
  br i1 %bad, label %error, label %done

error:
  call void @reach_error()
  br label %done

done:
  ret i32 0
}

!llvm.module.flags = !{!0}
!0 = !{i32 2, !"Debug Info Version", i32 3}
