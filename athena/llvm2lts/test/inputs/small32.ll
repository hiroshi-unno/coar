; ModuleID = 'small.c'
source_filename = "small.c"
target datalayout = "e-m:e-p:32:32-p270:32:32-p271:32:32-p272:64:64-i128:128-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @inc(i32 noundef %0) #0 !dbg !11 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
    #dbg_declare(ptr %2, !16, !DIExpression(), !17)
  %3 = load i32, ptr %2, align 4, !dbg !18
  %4 = add nsw i32 %3, 1, !dbg !19
  ret i32 %4, !dbg !20
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !21 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !24, !DIExpression(), !25)
  %3 = call i32 @__VERIFIER_nondet_int(), !dbg !26
  store i32 %3, ptr %2, align 4, !dbg !25
  %4 = load i32, ptr %2, align 4, !dbg !27
  %5 = call i32 @inc(i32 noundef %4), !dbg !28
  ret i32 %5, !dbg !29
}

declare i32 @__VERIFIER_nondet_int() #1

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="i686" "target-features"="+cmov,+cx8,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="i686" "target-features"="+cmov,+cx8,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!2, !3, !4, !5, !6, !7, !8, !9}
!llvm.ident = !{!10}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "small.c", directory: "/w", checksumkind: CSK_MD5, checksum: "a0bc8504aa8068340dda9aacfaf6dc35")
!2 = !{i32 1, !"NumRegisterParameters", i32 0}
!3 = !{i32 7, !"Dwarf Version", i32 5}
!4 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !{i32 1, !"wchar_size", i32 4}
!6 = !{i32 8, !"PIC Level", i32 2}
!7 = !{i32 7, !"PIE Level", i32 2}
!8 = !{i32 7, !"uwtable", i32 2}
!9 = !{i32 7, !"frame-pointer", i32 2}
!10 = !{!"Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)"}
!11 = distinct !DISubprogram(name: "inc", scope: !1, file: !1, line: 2, type: !12, scopeLine: 2, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !15)
!12 = !DISubroutineType(types: !13)
!13 = !{!14, !14}
!14 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!15 = !{}
!16 = !DILocalVariable(name: "x", arg: 1, scope: !11, file: !1, line: 2, type: !14)
!17 = !DILocation(line: 2, column: 13, scope: !11)
!18 = !DILocation(line: 2, column: 25, scope: !11)
!19 = !DILocation(line: 2, column: 27, scope: !11)
!20 = !DILocation(line: 2, column: 18, scope: !11)
!21 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 3, type: !22, scopeLine: 3, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !15)
!22 = !DISubroutineType(types: !23)
!23 = !{!14}
!24 = !DILocalVariable(name: "x", scope: !21, file: !1, line: 4, type: !14)
!25 = !DILocation(line: 4, column: 7, scope: !21)
!26 = !DILocation(line: 4, column: 11, scope: !21)
!27 = !DILocation(line: 5, column: 14, scope: !21)
!28 = !DILocation(line: 5, column: 10, scope: !21)
!29 = !DILocation(line: 5, column: 3, scope: !21)
