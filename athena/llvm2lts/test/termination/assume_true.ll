; ModuleID = 'termination/assume_true.c'
source_filename = "termination/assume_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !27 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #4, !dbg !30
  unreachable, !dbg !30
}

; Function Attrs: noreturn
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @__VERIFIER_assert(i32 noundef %0) #0 !dbg !31 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
    #dbg_declare(ptr %2, !36, !DIExpression(), !37)
  %3 = load i32, ptr %2, align 4, !dbg !38
  %4 = icmp ne i32 %3, 0, !dbg !38
  br i1 %4, label %6, label %5, !dbg !40

5:                                                ; preds = %1
  call void @reach_error(), !dbg !41
  call void @abort() #5, !dbg !43
  unreachable, !dbg !43

6:                                                ; preds = %1
  ret void, !dbg !44
}

; Function Attrs: noreturn nounwind
declare void @abort() #2

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !45 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  call void @__VERIFIER_assume(i32 noundef 1), !dbg !48
    #dbg_declare(ptr %2, !49, !DIExpression(), !50)
  %3 = call i32 @__VERIFIER_nondet_int(), !dbg !51
  store i32 %3, ptr %2, align 4, !dbg !50
  br label %4, !dbg !52

4:                                                ; preds = %7, %0
  %5 = load i32, ptr %2, align 4, !dbg !53
  %6 = icmp sgt i32 %5, 0, !dbg !54
  br i1 %6, label %7, label %10, !dbg !52

7:                                                ; preds = %4
  %8 = load i32, ptr %2, align 4, !dbg !55
  %9 = add nsw i32 %8, -1, !dbg !55
  store i32 %9, ptr %2, align 4, !dbg !55
  br label %4, !dbg !52, !llvm.loop !56

10:                                               ; preds = %4
  ret i32 0, !dbg !57
}

declare void @__VERIFIER_assume(i32 noundef) #3

declare i32 @__VERIFIER_nondet_int() #3

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { noreturn }
attributes #5 = { noreturn nounwind }

!llvm.dbg.cu = !{!17}
!llvm.module.flags = !{!19, !20, !21, !22, !23, !24, !25}
!llvm.ident = !{!26}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 6, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "termination/assume_true.c", directory: "/w", checksumkind: CSK_MD5, checksum: "cbd0a6c8703c78819f258679b41fdf38")
!3 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 16, elements: !5)
!4 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!5 = !{!6}
!6 = !DISubrange(count: 2)
!7 = !DIGlobalVariableExpression(var: !8, expr: !DIExpression())
!8 = distinct !DIGlobalVariable(scope: null, file: !2, line: 6, type: !9, isLocal: true, isDefinition: true)
!9 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 32, elements: !10)
!10 = !{!11}
!11 = !DISubrange(count: 4)
!12 = !DIGlobalVariableExpression(var: !13, expr: !DIExpression())
!13 = distinct !DIGlobalVariable(scope: null, file: !2, line: 6, type: !14, isLocal: true, isDefinition: true)
!14 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 96, elements: !15)
!15 = !{!16}
!16 = !DISubrange(count: 12)
!17 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !18, splitDebugInlining: false, nameTableKind: None)
!18 = !{!0, !7, !12}
!19 = !{i32 7, !"Dwarf Version", i32 5}
!20 = !{i32 2, !"Debug Info Version", i32 3}
!21 = !{i32 1, !"wchar_size", i32 4}
!22 = !{i32 8, !"PIC Level", i32 2}
!23 = !{i32 7, !"PIE Level", i32 2}
!24 = !{i32 7, !"uwtable", i32 2}
!25 = !{i32 7, !"frame-pointer", i32 2}
!26 = !{!"Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)"}
!27 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 6, type: !28, scopeLine: 6, spFlags: DISPFlagDefinition, unit: !17)
!28 = !DISubroutineType(types: !29)
!29 = !{null}
!30 = !DILocation(line: 6, column: 22, scope: !27)
!31 = distinct !DISubprogram(name: "__VERIFIER_assert", scope: !2, file: !2, line: 7, type: !32, scopeLine: 7, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!32 = !DISubroutineType(types: !33)
!33 = !{null, !34}
!34 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!35 = !{}
!36 = !DILocalVariable(name: "cond", arg: 1, scope: !31, file: !2, line: 7, type: !34)
!37 = !DILocation(line: 7, column: 28, scope: !31)
!38 = !DILocation(line: 7, column: 41, scope: !39)
!39 = distinct !DILexicalBlock(scope: !31, file: !2, line: 7, column: 40)
!40 = !DILocation(line: 7, column: 40, scope: !31)
!41 = !DILocation(line: 7, column: 49, scope: !42)
!42 = distinct !DILexicalBlock(scope: !39, file: !2, line: 7, column: 47)
!43 = !DILocation(line: 7, column: 64, scope: !42)
!44 = !DILocation(line: 7, column: 75, scope: !31)
!45 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 8, type: !46, scopeLine: 8, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!46 = !DISubroutineType(types: !47)
!47 = !{!34}
!48 = !DILocation(line: 9, column: 3, scope: !45)
!49 = !DILocalVariable(name: "x", scope: !45, file: !2, line: 10, type: !34)
!50 = !DILocation(line: 10, column: 7, scope: !45)
!51 = !DILocation(line: 10, column: 11, scope: !45)
!52 = !DILocation(line: 11, column: 3, scope: !45)
!53 = !DILocation(line: 11, column: 10, scope: !45)
!54 = !DILocation(line: 11, column: 12, scope: !45)
!55 = !DILocation(line: 11, column: 18, scope: !45)
!56 = distinct !{!56, !52, !55}
!57 = !DILocation(line: 12, column: 3, scope: !45)
