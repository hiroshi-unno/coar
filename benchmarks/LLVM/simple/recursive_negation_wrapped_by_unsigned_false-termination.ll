; ModuleID = 'recursive_negation_wrapped_by_unsigned_false-termination.c'
source_filename = "recursive_negation_wrapped_by_unsigned_false-termination.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @f(i32 noundef %0) #0 !dbg !13 {
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 %0, ptr %3, align 4
    #dbg_declare(ptr %3, !18, !DIExpression(), !19)
  %4 = load i32, ptr %3, align 4, !dbg !20
  %5 = icmp slt i32 %4, 0, !dbg !22
  br i1 %5, label %6, label %10, !dbg !23

6:                                                ; preds = %1
  %7 = load i32, ptr %3, align 4, !dbg !24
  %8 = sub i32 0, %7, !dbg !25
  %9 = call i32 @f(i32 noundef %8), !dbg !26
  store i32 %9, ptr %2, align 4, !dbg !27
  br label %19, !dbg !27

10:                                               ; preds = %1
  %11 = load i32, ptr %3, align 4, !dbg !28
  %12 = icmp eq i32 %11, 0, !dbg !30
  br i1 %12, label %13, label %14, !dbg !31

13:                                               ; preds = %10
  store i32 0, ptr %2, align 4, !dbg !32
  br label %19, !dbg !32

14:                                               ; preds = %10
  %15 = load i32, ptr %3, align 4, !dbg !33
  %16 = sub nsw i32 %15, 1, !dbg !34
  %17 = call i32 @f(i32 noundef %16), !dbg !35
  %18 = add nsw i32 1, %17, !dbg !36
  store i32 %18, ptr %2, align 4, !dbg !37
  br label %19, !dbg !37

19:                                               ; preds = %14, %13, %6
  %20 = load i32, ptr %2, align 4, !dbg !38
  ret i32 %20, !dbg !38
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !39 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !42, !DIExpression(), !43)
  %4 = call i32 @__VERIFIER_nondet_int(), !dbg !44
  store i32 %4, ptr %2, align 4, !dbg !43
    #dbg_declare(ptr %3, !45, !DIExpression(), !46)
  %5 = load i32, ptr %2, align 4, !dbg !47
  %6 = call i32 @f(i32 noundef %5), !dbg !48
  store i32 %6, ptr %3, align 4, !dbg !46
  ret i32 0, !dbg !49
}

declare i32 @__VERIFIER_nondet_int() #1

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!5, !6, !7, !8, !9, !10, !11}
!llvm.ident = !{!12}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "Ubuntu clang version 19.1.1 (1ubuntu1~24.04.2)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, retainedTypes: !2, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "recursive_negation_wrapped_by_unsigned_false-termination.c", directory: "/home/opam/coar", checksumkind: CSK_MD5, checksum: "5320b7039057f9e3b1c3f0141f46e441")
!2 = !{!3, !4}
!3 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!4 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!5 = !{i32 7, !"Dwarf Version", i32 5}
!6 = !{i32 2, !"Debug Info Version", i32 3}
!7 = !{i32 1, !"wchar_size", i32 4}
!8 = !{i32 8, !"PIC Level", i32 2}
!9 = !{i32 7, !"PIE Level", i32 2}
!10 = !{i32 7, !"uwtable", i32 2}
!11 = !{i32 7, !"frame-pointer", i32 2}
!12 = !{!"Ubuntu clang version 19.1.1 (1ubuntu1~24.04.2)"}
!13 = distinct !DISubprogram(name: "f", scope: !14, file: !14, line: 8, type: !15, scopeLine: 8, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !17)
!14 = !DIFile(filename: "recursive_negation_wrapped_by_unsigned_false-termination.c", directory: "", checksumkind: CSK_MD5, checksum: "5320b7039057f9e3b1c3f0141f46e441")
!15 = !DISubroutineType(types: !16)
!16 = !{!3, !3}
!17 = !{}
!18 = !DILocalVariable(name: "m", arg: 1, scope: !13, file: !14, line: 8, type: !3)
!19 = !DILocation(line: 8, column: 11, scope: !13)
!20 = !DILocation(line: 8, column: 20, scope: !21)
!21 = distinct !DILexicalBlock(scope: !13, file: !14, line: 8, column: 20)
!22 = !DILocation(line: 8, column: 22, scope: !21)
!23 = !DILocation(line: 8, column: 20, scope: !13)
!24 = !DILocation(line: 8, column: 57, scope: !21)
!25 = !DILocation(line: 8, column: 45, scope: !21)
!26 = !DILocation(line: 8, column: 34, scope: !21)
!27 = !DILocation(line: 8, column: 27, scope: !21)
!28 = !DILocation(line: 8, column: 66, scope: !29)
!29 = distinct !DILexicalBlock(scope: !13, file: !14, line: 8, column: 66)
!30 = !DILocation(line: 8, column: 68, scope: !29)
!31 = !DILocation(line: 8, column: 66, scope: !13)
!32 = !DILocation(line: 8, column: 74, scope: !29)
!33 = !DILocation(line: 8, column: 97, scope: !13)
!34 = !DILocation(line: 8, column: 99, scope: !13)
!35 = !DILocation(line: 8, column: 95, scope: !13)
!36 = !DILocation(line: 8, column: 93, scope: !13)
!37 = !DILocation(line: 8, column: 84, scope: !13)
!38 = !DILocation(line: 8, column: 105, scope: !13)
!39 = distinct !DISubprogram(name: "main", scope: !14, file: !14, line: 9, type: !40, scopeLine: 9, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !17)
!40 = !DISubroutineType(types: !41)
!41 = !{!3}
!42 = !DILocalVariable(name: "m", scope: !39, file: !14, line: 9, type: !3)
!43 = !DILocation(line: 9, column: 18, scope: !39)
!44 = !DILocation(line: 9, column: 22, scope: !39)
!45 = !DILocalVariable(name: "r", scope: !39, file: !14, line: 9, type: !3)
!46 = !DILocation(line: 9, column: 51, scope: !39)
!47 = !DILocation(line: 9, column: 57, scope: !39)
!48 = !DILocation(line: 9, column: 55, scope: !39)
!49 = !DILocation(line: 9, column: 61, scope: !39)
