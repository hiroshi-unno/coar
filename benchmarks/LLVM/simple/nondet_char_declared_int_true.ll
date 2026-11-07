; __VERIFIER_nondet_char declared as returning int (as an unprototyped or
; carelessly declared call gives it): its value is a char's, so it is never
; above 127 or below -128 and reach_error is unreachable (YES), in BV mode
; as in Int mode, where the name already gave the range.
; Hand-written LLVM 19 IR.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare void @reach_error()

declare i32 @__VERIFIER_nondet_char()

declare i32 @__VERIFIER_nondet_uchar()

define i32 @main() {
entry:
  %c = call i32 @__VERIFIER_nondet_char()
  %high = icmp sgt i32 %c, 127
  %low = icmp slt i32 %c, -128
  %u = call i32 @__VERIFIER_nondet_uchar()
  %uhigh = icmp ugt i32 %u, 255
  %out = or i1 %high, %low
  %bad = or i1 %out, %uhigh
  br i1 %bad, label %error, label %done

error:
  call void @reach_error()
  br label %done

done:
  ret i32 0
}

!llvm.module.flags = !{!0}
!0 = !{i32 2, !"Debug Info Version", i32 3}
