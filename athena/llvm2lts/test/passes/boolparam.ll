; ModuleID = 'passes/boolparam.c'
source_filename = "passes/boolparam.c"
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

; Function Attrs: nocallback noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @__VERIFIER_assert(i1 noundef zeroext %0) #0 !dbg !31 {
  %2 = alloca i8, align 1
  %3 = zext i1 %0 to i8
  store i8 %3, ptr %2, align 1
    #dbg_declare(ptr %2, !36, !DIExpression(), !37)
  %4 = load i8, ptr %2, align 1, !dbg !38
  %5 = trunc i8 %4 to i1, !dbg !38
  br i1 %5, label %7, label %6, !dbg !40

6:                                                ; preds = %1
  call void @reach_error(), !dbg !41
  call void @abort() #5, !dbg !43
  unreachable, !dbg !43

7:                                                ; preds = %1
  ret void, !dbg !44
}

; Function Attrs: noreturn nounwind
declare void @abort() #2

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !45 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !49, !DIExpression(), !50)
  %3 = call i32 @__VERIFIER_nondet_int(), !dbg !51
  store i32 %3, ptr %2, align 4, !dbg !50
  %4 = load i32, ptr %2, align 4, !dbg !52
  %5 = icmp sge i32 %4, 0, !dbg !53
  br i1 %5, label %9, label %6, !dbg !54

6:                                                ; preds = %0
  %7 = load i32, ptr %2, align 4, !dbg !55
  %8 = icmp slt i32 %7, 0, !dbg !56
  br label %9, !dbg !54

9:                                                ; preds = %6, %0
  %10 = phi i1 [ true, %0 ], [ %8, %6 ]
  call void @__VERIFIER_assert(i1 noundef zeroext %10), !dbg !57
  ret i32 0, !dbg !58
}

declare i32 @__VERIFIER_nondet_int() #3

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { nocallback noreturn nounwind }
attributes #5 = { noreturn nounwind }

!llvm.dbg.cu = !{!17}
!llvm.module.flags = !{!19, !20, !21, !22, !23, !24, !25}
!llvm.ident = !{!26}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 3, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "passes/boolparam.c", directory: "/home/grafen/fptprove/athena/llvm2lts/test", checksumkind: CSK_MD5, checksum: "4b3daf9c945326cdcfdb2d8d9421d801")
!3 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 16, elements: !5)
!4 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_signed_char)
!5 = !{!6}
!6 = !DISubrange(count: 2)
!7 = !DIGlobalVariableExpression(var: !8, expr: !DIExpression())
!8 = distinct !DIGlobalVariable(scope: null, file: !2, line: 3, type: !9, isLocal: true, isDefinition: true)
!9 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 32, elements: !10)
!10 = !{!11}
!11 = !DISubrange(count: 4)
!12 = !DIGlobalVariableExpression(var: !13, expr: !DIExpression())
!13 = distinct !DIGlobalVariable(scope: null, file: !2, line: 3, type: !14, isLocal: true, isDefinition: true)
!14 = !DICompositeType(tag: DW_TAG_array_type, baseType: !4, size: 96, elements: !15)
!15 = !{!16}
!16 = !DISubrange(count: 12)
!17 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "Ubuntu clang version 19.1.1 (1ubuntu1~24.04.2)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !18, splitDebugInlining: false, nameTableKind: None)
!18 = !{!0, !7, !12}
!19 = !{i32 7, !"Dwarf Version", i32 5}
!20 = !{i32 2, !"Debug Info Version", i32 3}
!21 = !{i32 1, !"wchar_size", i32 4}
!22 = !{i32 8, !"PIC Level", i32 2}
!23 = !{i32 7, !"PIE Level", i32 2}
!24 = !{i32 7, !"uwtable", i32 2}
!25 = !{i32 7, !"frame-pointer", i32 2}
!26 = !{!"Ubuntu clang version 19.1.1 (1ubuntu1~24.04.2)"}
!27 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 3, type: !28, scopeLine: 3, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17)
!28 = !DISubroutineType(types: !29)
!29 = !{null}
!30 = !DILocation(line: 3, column: 26, scope: !27)
!31 = distinct !DISubprogram(name: "__VERIFIER_assert", scope: !2, file: !2, line: 6, type: !32, scopeLine: 6, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!32 = !DISubroutineType(types: !33)
!33 = !{null, !34}
!34 = !DIBasicType(name: "_Bool", size: 8, encoding: DW_ATE_boolean)
!35 = !{}
!36 = !DILocalVariable(name: "cond", arg: 1, scope: !31, file: !2, line: 6, type: !34)
!37 = !DILocation(line: 6, column: 30, scope: !31)
!38 = !DILocation(line: 6, column: 43, scope: !39)
!39 = distinct !DILexicalBlock(scope: !31, file: !2, line: 6, column: 42)
!40 = !DILocation(line: 6, column: 42, scope: !31)
!41 = !DILocation(line: 6, column: 51, scope: !42)
!42 = distinct !DILexicalBlock(scope: !39, file: !2, line: 6, column: 49)
!43 = !DILocation(line: 6, column: 66, scope: !42)
!44 = !DILocation(line: 6, column: 77, scope: !31)
!45 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 7, type: !46, scopeLine: 7, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!46 = !DISubroutineType(types: !47)
!47 = !{!48}
!48 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!49 = !DILocalVariable(name: "x", scope: !45, file: !2, line: 7, type: !48)
!50 = !DILocation(line: 7, column: 22, scope: !45)
!51 = !DILocation(line: 7, column: 26, scope: !45)
!52 = !DILocation(line: 7, column: 69, scope: !45)
!53 = !DILocation(line: 7, column: 71, scope: !45)
!54 = !DILocation(line: 7, column: 76, scope: !45)
!55 = !DILocation(line: 7, column: 79, scope: !45)
!56 = !DILocation(line: 7, column: 81, scope: !45)
!57 = !DILocation(line: 7, column: 51, scope: !45)
!58 = !DILocation(line: 7, column: 87, scope: !45)
