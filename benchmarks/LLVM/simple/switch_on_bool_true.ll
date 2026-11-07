; A switch on an i1 condition: the case true is taken exactly when x < 0,
; and the default edge exactly when x >= 0, so reach_error is unreachable
; (YES).  Hand-written LLVM 19 IR.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare void @reach_error()

declare i32 @__VERIFIER_nondet_int()

define i32 @main() {
entry:
  %x = call i32 @__VERIFIER_nondet_int()
  %neg = icmp slt i32 %x, 0
  switch i1 %neg, label %nonneg [
    i1 true, label %negative
  ]

negative:
  %ok1 = icmp slt i32 %x, 0
  br i1 %ok1, label %done, label %error

nonneg:
  %ok2 = icmp sge i32 %x, 0
  br i1 %ok2, label %done, label %error

error:
  call void @reach_error()
  br label %done

done:
  ret i32 0
}

!llvm.module.flags = !{!0}
!0 = !{i32 2, !"Debug Info Version", i32 3}
