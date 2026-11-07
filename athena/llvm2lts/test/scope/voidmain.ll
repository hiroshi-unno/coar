; ModuleID = 'scope/voidmain.c'
source_filename = "scope/voidmain.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local void @main() #0 !dbg !10 {
  %1 = alloca i32, align 4
    #dbg_declare(ptr %1, !14, !DIExpression(), !16)
  %2 = call i32 @__VERIFIER_nondet_int(), !dbg !17
  store i32 %2, ptr %1, align 4, !dbg !16
  %3 = load i32, ptr %1, align 4, !dbg !18
  %4 = icmp eq i32 %3, 3, !dbg !20
  br i1 %4, label %5, label %6, !dbg !21

5:                                                ; preds = %0
  call void @reach_error(), !dbg !22
  br label %6, !dbg !22

6:                                                ; preds = %5, %0
  ret void, !dbg !23
}

declare i32 @__VERIFIER_nondet_int() #1

declare void @reach_error() #1

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3, !4, !5, !6, !7, !8}
!llvm.ident = !{!9}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "scope/voidmain.c", directory: "/home/grafen/fptprove/athena/llvm2lts/test", checksumkind: CSK_MD5, checksum: "61f439e5bd72e7ac2fa8a68441303dda")
!2 = !{i32 7, !"Dwarf Version", i32 5}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !{i32 1, !"wchar_size", i32 4}
!5 = !{i32 8, !"PIC Level", i32 2}
!6 = !{i32 7, !"PIE Level", i32 2}
!7 = !{i32 7, !"uwtable", i32 2}
!8 = !{i32 7, !"frame-pointer", i32 2}
!9 = !{!"clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)"}
!10 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 4, type: !11, scopeLine: 4, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !13)
!11 = !DISubroutineType(types: !12)
!12 = !{null}
!13 = !{}
!14 = !DILocalVariable(name: "x", scope: !10, file: !1, line: 5, type: !15)
!15 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!16 = !DILocation(line: 5, column: 7, scope: !10)
!17 = !DILocation(line: 5, column: 11, scope: !10)
!18 = !DILocation(line: 6, column: 7, scope: !19)
!19 = distinct !DILexicalBlock(scope: !10, file: !1, line: 6, column: 7)
!20 = !DILocation(line: 6, column: 9, scope: !19)
!21 = !DILocation(line: 6, column: 7, scope: !10)
!22 = !DILocation(line: 6, column: 15, scope: !19)
!23 = !DILocation(line: 7, column: 1, scope: !10)
