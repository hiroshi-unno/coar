; An extractvalue whose indices pass through an array of structs: the
; global holds { [ {1, 2}, {3, 4} ] }, element 1 of the array is taken as a
; struct value and its field 0 read.  It is 3, so reach_error is
; unreachable (YES).  Hand-written LLVM 19 IR.
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@g = global { [2 x { i32, i32 }] } { [2 x { i32, i32 }] [{ i32, i32 } { i32 1, i32 2 }, { i32, i32 } { i32 3, i32 4 }] }, align 4

declare void @reach_error()

define i32 @main() {
entry:
  %v = load { [2 x { i32, i32 }] }, ptr @g, align 4
  %e = extractvalue { [2 x { i32, i32 }] } %v, 0, 1
  %f = extractvalue { i32, i32 } %e, 0
  %bad = icmp ne i32 %f, 3
  br i1 %bad, label %error, label %done

error:
  call void @reach_error()
  br label %done

done:
  ret i32 0
}

!llvm.module.flags = !{!0}
!0 = !{i32 2, !"Debug Info Version", i32 3}
