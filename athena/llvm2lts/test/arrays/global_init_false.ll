; ModuleID = 'global_init_false.c'
source_filename = "global_init_false.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12
@a = dso_local global [4 x i32] [i32 3, i32 1, i32 4, i32 1], align 16, !dbg !17

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !31 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #4, !dbg !34
  unreachable, !dbg !34
}

; Function Attrs: noreturn
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @__VERIFIER_assert(i32 noundef %0) #0 !dbg !35 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
    #dbg_declare(ptr %2, !39, !DIExpression(), !40)
  %3 = load i32, ptr %2, align 4, !dbg !41
  %4 = icmp ne i32 %3, 0, !dbg !41
  br i1 %4, label %6, label %5, !dbg !43

5:                                                ; preds = %1
  call void @reach_error(), !dbg !44
  call void @abort() #5, !dbg !46
  unreachable, !dbg !46

6:                                                ; preds = %1
  ret void, !dbg !47
}

; Function Attrs: noreturn nounwind
declare void @abort() #2

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !48 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !51, !DIExpression(), !52)
  %3 = call i32 @__VERIFIER_nondet_int(), !dbg !53
  store i32 %3, ptr %2, align 4, !dbg !52
  %4 = load i32, ptr %2, align 4, !dbg !54
  %5 = icmp slt i32 %4, 0, !dbg !56
  br i1 %5, label %9, label %6, !dbg !57

6:                                                ; preds = %0
  %7 = load i32, ptr %2, align 4, !dbg !58
  %8 = icmp sge i32 %7, 4, !dbg !59
  br i1 %8, label %9, label %10, !dbg !60

9:                                                ; preds = %6, %0
  store i32 0, ptr %1, align 4, !dbg !61
  br label %17, !dbg !61

10:                                               ; preds = %6
  %11 = load i32, ptr %2, align 4, !dbg !62
  %12 = sext i32 %11 to i64, !dbg !63
  %13 = getelementptr inbounds [4 x i32], ptr @a, i64 0, i64 %12, !dbg !63
  %14 = load i32, ptr %13, align 4, !dbg !63
  %15 = icmp ne i32 %14, 4, !dbg !64
  %16 = zext i1 %15 to i32, !dbg !64
  call void @__VERIFIER_assert(i32 noundef %16), !dbg !65
  store i32 0, ptr %1, align 4, !dbg !66
  br label %17, !dbg !66

17:                                               ; preds = %10, %9
  %18 = load i32, ptr %1, align 4, !dbg !67
  ret i32 %18, !dbg !67
}

declare i32 @__VERIFIER_nondet_int() #3

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { noreturn }
attributes #5 = { noreturn nounwind }

!llvm.dbg.cu = !{!19}
!llvm.module.flags = !{!23, !24, !25, !26, !27, !28, !29}
!llvm.ident = !{!30}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 4, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "global_init_false.c", directory: "/w", checksumkind: CSK_MD5, checksum: "86bb306290b1a35919494070533def03")
!3 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 16, elements: !5)
!4 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!5 = !{!6}
!6 = !DISubrange(count: 2)
!7 = !DIGlobalVariableExpression(var: !8, expr: !DIExpression())
!8 = distinct !DIGlobalVariable(scope: null, file: !2, line: 4, type: !9, isLocal: true, isDefinition: true)
!9 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 32, elements: !10)
!10 = !{!11}
!11 = !DISubrange(count: 4)
!12 = !DIGlobalVariableExpression(var: !13, expr: !DIExpression())
!13 = distinct !DIGlobalVariable(scope: null, file: !2, line: 4, type: !14, isLocal: true, isDefinition: true)
!14 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 96, elements: !15)
!15 = !{!16}
!16 = !DISubrange(count: 12)
!17 = !DIGlobalVariableExpression(var: !18, expr: !DIExpression())
!18 = distinct !DIGlobalVariable(name: "a", scope: !19, file: !2, line: 6, type: !21, isLocal: false, isDefinition: true)
!19 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !20, splitDebugInlining: false, nameTableKind: None)
!20 = !{!0, !7, !12, !17}
!21 = !DICompositeType(tag: DW_TAG_array_type, baseType: !22, size: 128, elements: !10)
!22 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!23 = !{i32 7, !"Dwarf Version", i32 5}
!24 = !{i32 2, !"Debug Info Version", i32 3}
!25 = !{i32 1, !"wchar_size", i32 4}
!26 = !{i32 8, !"PIC Level", i32 2}
!27 = !{i32 7, !"PIE Level", i32 2}
!28 = !{i32 7, !"uwtable", i32 2}
!29 = !{i32 7, !"frame-pointer", i32 2}
!30 = !{!"Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)"}
!31 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 4, type: !32, scopeLine: 4, spFlags: DISPFlagDefinition, unit: !19)
!32 = !DISubroutineType(types: !33)
!33 = !{null}
!34 = !DILocation(line: 4, column: 22, scope: !31)
!35 = distinct !DISubprogram(name: "__VERIFIER_assert", scope: !2, file: !2, line: 5, type: !36, scopeLine: 5, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19, retainedNodes: !38)
!36 = !DISubroutineType(types: !37)
!37 = !{null, !22}
!38 = !{}
!39 = !DILocalVariable(name: "cond", arg: 1, scope: !35, file: !2, line: 5, type: !22)
!40 = !DILocation(line: 5, column: 28, scope: !35)
!41 = !DILocation(line: 5, column: 41, scope: !42)
!42 = distinct !DILexicalBlock(scope: !35, file: !2, line: 5, column: 40)
!43 = !DILocation(line: 5, column: 40, scope: !35)
!44 = !DILocation(line: 5, column: 49, scope: !45)
!45 = distinct !DILexicalBlock(scope: !42, file: !2, line: 5, column: 47)
!46 = !DILocation(line: 5, column: 64, scope: !45)
!47 = !DILocation(line: 5, column: 75, scope: !35)
!48 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 7, type: !49, scopeLine: 7, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19, retainedNodes: !38)
!49 = !DISubroutineType(types: !50)
!50 = !{!22}
!51 = !DILocalVariable(name: "k", scope: !48, file: !2, line: 8, type: !22)
!52 = !DILocation(line: 8, column: 7, scope: !48)
!53 = !DILocation(line: 8, column: 11, scope: !48)
!54 = !DILocation(line: 9, column: 7, scope: !55)
!55 = distinct !DILexicalBlock(scope: !48, file: !2, line: 9, column: 7)
!56 = !DILocation(line: 9, column: 9, scope: !55)
!57 = !DILocation(line: 9, column: 13, scope: !55)
!58 = !DILocation(line: 9, column: 16, scope: !55)
!59 = !DILocation(line: 9, column: 18, scope: !55)
!60 = !DILocation(line: 9, column: 7, scope: !48)
!61 = !DILocation(line: 9, column: 24, scope: !55)
!62 = !DILocation(line: 10, column: 23, scope: !48)
!63 = !DILocation(line: 10, column: 21, scope: !48)
!64 = !DILocation(line: 10, column: 26, scope: !48)
!65 = !DILocation(line: 10, column: 3, scope: !48)
!66 = !DILocation(line: 11, column: 3, scope: !48)
!67 = !DILocation(line: 12, column: 1, scope: !48)
