; ModuleID = 'translate/switch_true.c'
source_filename = "translate/switch_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12
@g = dso_local global i32 3, align 4, !dbg !17

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !30 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #4, !dbg !33
  unreachable, !dbg !33
}

; Function Attrs: noreturn
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @__VERIFIER_assert(i32 noundef %0) #0 !dbg !34 {
  %2 = alloca i32, align 4
  store i32 %0, ptr %2, align 4
    #dbg_declare(ptr %2, !38, !DIExpression(), !39)
  %3 = load i32, ptr %2, align 4, !dbg !40
  %4 = icmp ne i32 %3, 0, !dbg !40
  br i1 %4, label %6, label %5, !dbg !42

5:                                                ; preds = %1
  call void @reach_error(), !dbg !43
  call void @abort() #5, !dbg !45
  unreachable, !dbg !45

6:                                                ; preds = %1
  ret void, !dbg !46
}

; Function Attrs: noreturn nounwind
declare void @abort() #2

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !47 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !50, !DIExpression(), !51)
  %4 = call i32 @__VERIFIER_nondet_int(), !dbg !52
  store i32 %4, ptr %2, align 4, !dbg !51
  %5 = load i32, ptr %2, align 4, !dbg !53
  switch i32 %5, label %8 [
    i32 0, label %6
    i32 1, label %7
  ], !dbg !54

6:                                                ; preds = %0
  store i32 10, ptr @g, align 4, !dbg !55
  br label %9, !dbg !57

7:                                                ; preds = %0
  store i32 20, ptr @g, align 4, !dbg !58
  br label %9, !dbg !59

8:                                                ; preds = %0
  store i32 30, ptr @g, align 4, !dbg !60
  br label %9, !dbg !61

9:                                                ; preds = %8, %7, %6
    #dbg_declare(ptr %3, !62, !DIExpression(), !63)
  %10 = load i32, ptr %2, align 4, !dbg !64
  %11 = icmp sgt i32 %10, 5, !dbg !65
  br i1 %11, label %12, label %14, !dbg !64

12:                                               ; preds = %9
  %13 = load i32, ptr @g, align 4, !dbg !66
  br label %15, !dbg !64

14:                                               ; preds = %9
  br label %15, !dbg !64

15:                                               ; preds = %14, %12
  %16 = phi i32 [ %13, %12 ], [ 0, %14 ], !dbg !64
  store i32 %16, ptr %3, align 4, !dbg !63
  %17 = load i32, ptr %3, align 4, !dbg !67
  %18 = icmp eq i32 %17, 0, !dbg !68
  br i1 %18, label %22, label %19, !dbg !69

19:                                               ; preds = %15
  %20 = load i32, ptr %3, align 4, !dbg !70
  %21 = icmp eq i32 %20, 30, !dbg !71
  br label %22, !dbg !69

22:                                               ; preds = %19, %15
  %23 = phi i1 [ true, %15 ], [ %21, %19 ]
  %24 = zext i1 %23 to i32, !dbg !69
  call void @__VERIFIER_assert(i32 noundef %24), !dbg !72
  ret i32 0, !dbg !73
}

declare i32 @__VERIFIER_nondet_int() #3

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { noreturn }
attributes #5 = { noreturn nounwind }

!llvm.dbg.cu = !{!19}
!llvm.module.flags = !{!22, !23, !24, !25, !26, !27, !28}
!llvm.ident = !{!29}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 6, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "translate/switch_true.c", directory: "/w", checksumkind: CSK_MD5, checksum: "377c42759b348ddc9135039ef9ef61ea")
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
!17 = !DIGlobalVariableExpression(var: !18, expr: !DIExpression())
!18 = distinct !DIGlobalVariable(name: "g", scope: !19, file: !2, line: 8, type: !21, isLocal: false, isDefinition: true)
!19 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !20, splitDebugInlining: false, nameTableKind: None)
!20 = !{!0, !7, !12, !17}
!21 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!22 = !{i32 7, !"Dwarf Version", i32 5}
!23 = !{i32 2, !"Debug Info Version", i32 3}
!24 = !{i32 1, !"wchar_size", i32 4}
!25 = !{i32 8, !"PIC Level", i32 2}
!26 = !{i32 7, !"PIE Level", i32 2}
!27 = !{i32 7, !"uwtable", i32 2}
!28 = !{i32 7, !"frame-pointer", i32 2}
!29 = !{!"Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)"}
!30 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 6, type: !31, scopeLine: 6, spFlags: DISPFlagDefinition, unit: !19)
!31 = !DISubroutineType(types: !32)
!32 = !{null}
!33 = !DILocation(line: 6, column: 22, scope: !30)
!34 = distinct !DISubprogram(name: "__VERIFIER_assert", scope: !2, file: !2, line: 7, type: !35, scopeLine: 7, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19, retainedNodes: !37)
!35 = !DISubroutineType(types: !36)
!36 = !{null, !21}
!37 = !{}
!38 = !DILocalVariable(name: "cond", arg: 1, scope: !34, file: !2, line: 7, type: !21)
!39 = !DILocation(line: 7, column: 28, scope: !34)
!40 = !DILocation(line: 7, column: 41, scope: !41)
!41 = distinct !DILexicalBlock(scope: !34, file: !2, line: 7, column: 40)
!42 = !DILocation(line: 7, column: 40, scope: !34)
!43 = !DILocation(line: 7, column: 49, scope: !44)
!44 = distinct !DILexicalBlock(scope: !41, file: !2, line: 7, column: 47)
!45 = !DILocation(line: 7, column: 64, scope: !44)
!46 = !DILocation(line: 7, column: 75, scope: !34)
!47 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 9, type: !48, scopeLine: 9, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !19, retainedNodes: !37)
!48 = !DISubroutineType(types: !49)
!49 = !{!21}
!50 = !DILocalVariable(name: "k", scope: !47, file: !2, line: 10, type: !21)
!51 = !DILocation(line: 10, column: 7, scope: !47)
!52 = !DILocation(line: 10, column: 11, scope: !47)
!53 = !DILocation(line: 11, column: 11, scope: !47)
!54 = !DILocation(line: 11, column: 3, scope: !47)
!55 = !DILocation(line: 11, column: 26, scope: !56)
!56 = distinct !DILexicalBlock(scope: !47, file: !2, line: 11, column: 14)
!57 = !DILocation(line: 11, column: 32, scope: !56)
!58 = !DILocation(line: 11, column: 49, scope: !56)
!59 = !DILocation(line: 11, column: 55, scope: !56)
!60 = !DILocation(line: 11, column: 73, scope: !56)
!61 = !DILocation(line: 11, column: 79, scope: !56)
!62 = !DILocalVariable(name: "m", scope: !47, file: !2, line: 12, type: !21)
!63 = !DILocation(line: 12, column: 7, scope: !47)
!64 = !DILocation(line: 12, column: 11, scope: !47)
!65 = !DILocation(line: 12, column: 13, scope: !47)
!66 = !DILocation(line: 12, column: 19, scope: !47)
!67 = !DILocation(line: 13, column: 21, scope: !47)
!68 = !DILocation(line: 13, column: 23, scope: !47)
!69 = !DILocation(line: 13, column: 28, scope: !47)
!70 = !DILocation(line: 13, column: 31, scope: !47)
!71 = !DILocation(line: 13, column: 33, scope: !47)
!72 = !DILocation(line: 13, column: 3, scope: !47)
!73 = !DILocation(line: 14, column: 3, scope: !47)
