; ModuleID = 'ptr2arr/region_false.c'
source_filename = "ptr2arr/region_false.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12
@p2a_mem0_free = dso_local global i32 2, align 4, !dbg !17
@p2a_mem0 = dso_local global [100 x i32] zeroinitializer, align 16, !dbg !21

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !35 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #2, !dbg !38
  unreachable, !dbg !38
}

; Function Attrs: noreturn
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @__p2a_arbitrary_p2a_mem0() #0 !dbg !39 {
  ret void, !dbg !40
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !41 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  call void @__p2a_arbitrary_p2a_mem0(), !dbg !45
  store i32 7, ptr getelementptr inbounds ([100 x i32], ptr @p2a_mem0, i64 0, i64 1), align 4, !dbg !46
    #dbg_declare(ptr %2, !47, !DIExpression(), !48)
  %3 = load i32, ptr @p2a_mem0_free, align 4, !dbg !49
  store i32 %3, ptr %2, align 4, !dbg !48
  %4 = load i32, ptr @p2a_mem0_free, align 4, !dbg !50
  %5 = add nsw i32 %4, 1, !dbg !50
  store i32 %5, ptr @p2a_mem0_free, align 4, !dbg !50
  %6 = load i32, ptr getelementptr inbounds ([100 x i32], ptr @p2a_mem0, i64 0, i64 1), align 4, !dbg !51
  %7 = icmp ne i32 %6, 7, !dbg !53
  br i1 %7, label %8, label %9, !dbg !54

8:                                                ; preds = %0
  call void @reach_error(), !dbg !55
  br label %9, !dbg !55

9:                                                ; preds = %8, %0
  %10 = load i32, ptr %2, align 4, !dbg !56
  %11 = sext i32 %10 to i64, !dbg !58
  %12 = getelementptr inbounds [100 x i32], ptr @p2a_mem0, i64 0, i64 %11, !dbg !58
  %13 = load i32, ptr %12, align 4, !dbg !58
  %14 = icmp ne i32 %13, 0, !dbg !59
  br i1 %14, label %15, label %16, !dbg !60

15:                                               ; preds = %9
  call void @reach_error(), !dbg !61
  br label %16, !dbg !61

16:                                               ; preds = %15, %9
  ret i32 0, !dbg !62
}

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn }

!llvm.dbg.cu = !{!19}
!llvm.module.flags = !{!27, !28, !29, !30, !31, !32, !33}
!llvm.ident = !{!34}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 7, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "ptr2arr/region_false.c", directory: "/t", checksumkind: CSK_MD5, checksum: "622dbf7c809694cc8f1363bcd1653e74")
!3 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 16, elements: !5)
!4 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!5 = !{!6}
!6 = !DISubrange(count: 2)
!7 = !DIGlobalVariableExpression(var: !8, expr: !DIExpression())
!8 = distinct !DIGlobalVariable(scope: null, file: !2, line: 7, type: !9, isLocal: true, isDefinition: true)
!9 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 32, elements: !10)
!10 = !{!11}
!11 = !DISubrange(count: 4)
!12 = !DIGlobalVariableExpression(var: !13, expr: !DIExpression())
!13 = distinct !DIGlobalVariable(scope: null, file: !2, line: 7, type: !14, isLocal: true, isDefinition: true)
!14 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 96, elements: !15)
!15 = !{!16}
!16 = !DISubrange(count: 12)
!17 = !DIGlobalVariableExpression(var: !18, expr: !DIExpression())
!18 = distinct !DIGlobalVariable(name: "p2a_mem0_free", scope: !19, file: !2, line: 9, type: !24, isLocal: false, isDefinition: true)
!19 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !20, splitDebugInlining: false, nameTableKind: None)
!20 = !{!0, !7, !12, !17, !21}
!21 = !DIGlobalVariableExpression(var: !22, expr: !DIExpression())
!22 = distinct !DIGlobalVariable(name: "p2a_mem0", scope: !19, file: !2, line: 8, type: !23, isLocal: false, isDefinition: true)
!23 = !DICompositeType(tag: DW_TAG_array_type, baseType: !24, size: 3200, elements: !25)
!24 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!25 = !{!26}
!26 = !DISubrange(count: 100)
!27 = !{i32 7, !"Dwarf Version", i32 5}
!28 = !{i32 2, !"Debug Info Version", i32 3}
!29 = !{i32 1, !"wchar_size", i32 4}
!30 = !{i32 8, !"PIC Level", i32 2}
!31 = !{i32 7, !"PIE Level", i32 2}
!32 = !{i32 7, !"uwtable", i32 2}
!33 = !{i32 7, !"frame-pointer", i32 2}
!34 = !{!"clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)"}
!35 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 7, type: !36, scopeLine: 7, spFlags: DISPFlagDefinition, unit: !19)
!36 = !DISubroutineType(types: !37)
!37 = !{null}
!38 = !DILocation(line: 7, column: 22, scope: !35)
!39 = distinct !DISubprogram(name: "__p2a_arbitrary_p2a_mem0", scope: !2, file: !2, line: 10, type: !36, scopeLine: 10, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19)
!40 = !DILocation(line: 10, column: 39, scope: !39)
!41 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 11, type: !42, scopeLine: 11, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19, retainedNodes: !44)
!42 = !DISubroutineType(types: !43)
!43 = !{!24}
!44 = !{}
!45 = !DILocation(line: 12, column: 3, scope: !41)
!46 = !DILocation(line: 13, column: 15, scope: !41)
!47 = !DILocalVariable(name: "p", scope: !41, file: !2, line: 14, type: !24)
!48 = !DILocation(line: 14, column: 7, scope: !41)
!49 = !DILocation(line: 14, column: 11, scope: !41)
!50 = !DILocation(line: 15, column: 17, scope: !41)
!51 = !DILocation(line: 16, column: 7, scope: !52)
!52 = distinct !DILexicalBlock(scope: !41, file: !2, line: 16, column: 7)
!53 = !DILocation(line: 16, column: 19, scope: !52)
!54 = !DILocation(line: 16, column: 7, scope: !41)
!55 = !DILocation(line: 16, column: 25, scope: !52)
!56 = !DILocation(line: 17, column: 16, scope: !57)
!57 = distinct !DILexicalBlock(scope: !41, file: !2, line: 17, column: 7)
!58 = !DILocation(line: 17, column: 7, scope: !57)
!59 = !DILocation(line: 17, column: 19, scope: !57)
!60 = !DILocation(line: 17, column: 7, scope: !41)
!61 = !DILocation(line: 17, column: 25, scope: !57)
!62 = !DILocation(line: 18, column: 3, scope: !41)
