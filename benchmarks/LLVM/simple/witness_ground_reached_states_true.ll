; ModuleID = 'witness_ground_reached_states_true.c'
source_filename = "witness_ground_reached_states_true.c"
target datalayout = "e-m:e-p:32:32-p270:32:32-p271:32:32-p272:64:64-i128:128-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12
@g = dso_local global i32 0, align 4, !dbg !17

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !31 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #3, !dbg !34
  unreachable, !dbg !34
}

; Function Attrs: nocallback noreturn nounwind
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @__VERIFIER_assert(i32 noundef %0) #0 !dbg !35 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
    #dbg_declare(ptr %2, !39, !DIExpression(), !40)
  %3 = load i32, ptr %2, align 4, !dbg !41
  %4 = icmp ne i32 %3, 0, !dbg !43
  br i1 %4, label %7, label %5, !dbg !44

5:                                                ; preds = %1
  br label %6, !dbg !45

6:                                                ; preds = %5
    #dbg_label(!46, !48)
  call void @reach_error(), !dbg !49
  call void @abort() #4, !dbg !51
  unreachable, !dbg !51

7:                                                ; preds = %1
  ret void, !dbg !52
}

; Function Attrs: noreturn nounwind
declare void @abort() #2

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !53 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !56, !DIExpression(), !57)
  store i32 0, ptr %2, align 4, !dbg !57
  br label %3, !dbg !58

3:                                                ; preds = %6, %0
  %4 = load i32, ptr %2, align 4, !dbg !59
  %5 = icmp slt i32 %4, 5, !dbg !60
  br i1 %5, label %6, label %11, !dbg !58

6:                                                ; preds = %3
  %7 = load i32, ptr @g, align 4, !dbg !61
  %8 = add nsw i32 %7, 2, !dbg !63
  store i32 %8, ptr @g, align 4, !dbg !64
  %9 = load i32, ptr %2, align 4, !dbg !65
  %10 = add nsw i32 %9, 1, !dbg !66
  store i32 %10, ptr %2, align 4, !dbg !67
  br label %3, !dbg !58, !llvm.loop !68

11:                                               ; preds = %3
  %12 = load i32, ptr @g, align 4, !dbg !70
  %13 = icmp eq i32 %12, 10, !dbg !71
  %14 = zext i1 %13 to i32, !dbg !71
  call void @__VERIFIER_assert(i32 noundef %14), !dbg !72
  ret i32 0, !dbg !73
}

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="i686" "target-features"="+cmov,+cx8,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="i686" "target-features"="+cmov,+cx8,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="i686" "target-features"="+cmov,+cx8,+x87" "tune-cpu"="generic" }
attributes #3 = { nocallback noreturn nounwind }
attributes #4 = { noreturn nounwind }

!llvm.dbg.cu = !{!19}
!llvm.module.flags = !{!22, !23, !24, !25, !26, !27, !28, !29}
!llvm.ident = !{!30}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 3, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "witness_ground_reached_states_true.c", directory: ".", checksumkind: CSK_MD5, checksum: "1014e965d4328973387158910c519925")
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
!17 = !DIGlobalVariableExpression(var: !18, expr: !DIExpression())
!18 = distinct !DIGlobalVariable(name: "g", scope: !19, file: !2, line: 5, type: !21, isLocal: false, isDefinition: true)
!19 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "Ubuntu clang version 19.1.7 (++20250114103320+cd708029e0b2-1~exp1~20250114103432.75)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !20, splitDebugInlining: false, nameTableKind: None)
!20 = !{!0, !7, !12, !17}
!21 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!22 = !{i32 1, !"NumRegisterParameters", i32 0}
!23 = !{i32 7, !"Dwarf Version", i32 5}
!24 = !{i32 2, !"Debug Info Version", i32 3}
!25 = !{i32 1, !"wchar_size", i32 4}
!26 = !{i32 8, !"PIC Level", i32 2}
!27 = !{i32 7, !"PIE Level", i32 2}
!28 = !{i32 7, !"uwtable", i32 2}
!29 = !{i32 7, !"frame-pointer", i32 2}
!30 = !{!"Ubuntu clang version 19.1.7 (++20250114103320+cd708029e0b2-1~exp1~20250114103432.75)"}
!31 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 3, type: !32, scopeLine: 3, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19)
!32 = !DISubroutineType(types: !33)
!33 = !{null}
!34 = !DILocation(line: 3, column: 26, scope: !31)
!35 = distinct !DISubprogram(name: "__VERIFIER_assert", scope: !2, file: !2, line: 4, type: !36, scopeLine: 4, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19, retainedNodes: !38)
!36 = !DISubroutineType(types: !37)
!37 = !{null, !21}
!38 = !{}
!39 = !DILocalVariable(name: "cond", arg: 1, scope: !35, file: !2, line: 4, type: !21)
!40 = !DILocation(line: 4, column: 28, scope: !35)
!41 = !DILocation(line: 4, column: 42, scope: !42)
!42 = distinct !DILexicalBlock(scope: !35, file: !2, line: 4, column: 40)
!43 = !DILocation(line: 4, column: 41, scope: !42)
!44 = !DILocation(line: 4, column: 40, scope: !35)
!45 = !DILocation(line: 4, column: 49, scope: !42)
!46 = !DILabel(scope: !47, name: "ERROR", file: !2, line: 4)
!47 = distinct !DILexicalBlock(scope: !42, file: !2, line: 4, column: 49)
!48 = !DILocation(line: 4, column: 51, scope: !47)
!49 = !DILocation(line: 4, column: 59, scope: !50)
!50 = distinct !DILexicalBlock(scope: !47, file: !2, line: 4, column: 58)
!51 = !DILocation(line: 4, column: 73, scope: !50)
!52 = !DILocation(line: 4, column: 85, scope: !35)
!53 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 6, type: !54, scopeLine: 6, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19, retainedNodes: !38)
!54 = !DISubroutineType(types: !55)
!55 = !{!21}
!56 = !DILocalVariable(name: "i", scope: !53, file: !2, line: 7, type: !21)
!57 = !DILocation(line: 7, column: 7, scope: !53)
!58 = !DILocation(line: 8, column: 3, scope: !53)
!59 = !DILocation(line: 8, column: 10, scope: !53)
!60 = !DILocation(line: 8, column: 12, scope: !53)
!61 = !DILocation(line: 8, column: 23, scope: !62)
!62 = distinct !DILexicalBlock(scope: !53, file: !2, line: 8, column: 17)
!63 = !DILocation(line: 8, column: 25, scope: !62)
!64 = !DILocation(line: 8, column: 21, scope: !62)
!65 = !DILocation(line: 8, column: 34, scope: !62)
!66 = !DILocation(line: 8, column: 36, scope: !62)
!67 = !DILocation(line: 8, column: 32, scope: !62)
!68 = distinct !{!68, !58, !69}
!69 = !DILocation(line: 8, column: 41, scope: !53)
!70 = !DILocation(line: 9, column: 21, scope: !53)
!71 = !DILocation(line: 9, column: 23, scope: !53)
!72 = !DILocation(line: 9, column: 3, scope: !53)
!73 = !DILocation(line: 10, column: 3, scope: !53)
