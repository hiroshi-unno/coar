; ModuleID = 'intmodes/conversion_true.c'
source_filename = "intmodes/conversion_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !29 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #4, !dbg !32
  unreachable, !dbg !32
}

; Function Attrs: noreturn
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local void @__VERIFIER_assert(i32 noundef %0) #0 !dbg !33 {
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
  %3 = alloca i8, align 1
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !50, !DIExpression(), !51)
  %7 = call i32 @__VERIFIER_nondet_int(), !dbg !52
  store i32 %7, ptr %2, align 4, !dbg !51
  %8 = load i32, ptr %2, align 4, !dbg !53
  %9 = icmp eq i32 %8, 200, !dbg !54
  %10 = zext i1 %9 to i32, !dbg !54
  call void @__VERIFIER_assume(i32 noundef %10), !dbg !55
    #dbg_declare(ptr %3, !56, !DIExpression(), !58)
  %11 = load i32, ptr %2, align 4, !dbg !59
  %12 = trunc i32 %11 to i8, !dbg !59
  store i8 %12, ptr %3, align 1, !dbg !58
    #dbg_declare(ptr %4, !60, !DIExpression(), !61)
  %13 = load i8, ptr %3, align 1, !dbg !62
  %14 = sext i8 %13 to i32, !dbg !62
  store i32 %14, ptr %4, align 4, !dbg !61
  %15 = load i32, ptr %4, align 4, !dbg !63
  %16 = icmp eq i32 %15, -56, !dbg !64
  %17 = zext i1 %16 to i32, !dbg !64
  call void @__VERIFIER_assert(i32 noundef %17), !dbg !65
    #dbg_declare(ptr %5, !66, !DIExpression(), !67)
  %18 = call i32 @__VERIFIER_nondet_int(), !dbg !68
  store i32 %18, ptr %5, align 4, !dbg !67
  %19 = load i32, ptr %5, align 4, !dbg !69
  %20 = icmp eq i32 %19, -7, !dbg !70
  %21 = zext i1 %20 to i32, !dbg !70
  call void @__VERIFIER_assume(i32 noundef %21), !dbg !71
  %22 = load i32, ptr %5, align 4, !dbg !72
  %23 = sdiv i32 %22, 2, !dbg !73
  %24 = icmp eq i32 %23, -3, !dbg !74
  br i1 %24, label %25, label %29, !dbg !75

25:                                               ; preds = %0
  %26 = load i32, ptr %5, align 4, !dbg !76
  %27 = srem i32 %26, 2, !dbg !77
  %28 = icmp eq i32 %27, -1, !dbg !78
  br label %29

29:                                               ; preds = %25, %0
  %30 = phi i1 [ false, %0 ], [ %28, %25 ], !dbg !79
  %31 = zext i1 %30 to i32, !dbg !75
  call void @__VERIFIER_assert(i32 noundef %31), !dbg !80
    #dbg_declare(ptr %6, !81, !DIExpression(), !82)
  %32 = load i32, ptr %5, align 4, !dbg !83
  store i32 %32, ptr %6, align 4, !dbg !82
  %33 = load i32, ptr %6, align 4, !dbg !84
  %34 = udiv i32 %33, 2, !dbg !85
  %35 = icmp eq i32 %34, 2147483644, !dbg !86
  %36 = zext i1 %35 to i32, !dbg !86
  call void @__VERIFIER_assert(i32 noundef %36), !dbg !87
  ret i32 0, !dbg !88
}

declare i32 @__VERIFIER_nondet_int() #3

declare void @__VERIFIER_assume(i32 noundef) #3

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { noreturn }
attributes #5 = { noreturn nounwind }

!llvm.dbg.cu = !{!17}
!llvm.module.flags = !{!21, !22, !23, !24, !25, !26, !27}
!llvm.ident = !{!28}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 6, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "intmodes/conversion_true.c", directory: "/d", checksumkind: CSK_MD5, checksum: "c42603452850f802adea5bb19ed9bc60")
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
!17 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, retainedTypes: !18, globals: !20, splitDebugInlining: false, nameTableKind: None)
!18 = !{!19}
!19 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!20 = !{!0, !7, !12}
!21 = !{i32 7, !"Dwarf Version", i32 5}
!22 = !{i32 2, !"Debug Info Version", i32 3}
!23 = !{i32 1, !"wchar_size", i32 4}
!24 = !{i32 8, !"PIC Level", i32 2}
!25 = !{i32 7, !"PIE Level", i32 2}
!26 = !{i32 7, !"uwtable", i32 2}
!27 = !{i32 7, !"frame-pointer", i32 2}
!28 = !{!"clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)"}
!29 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 6, type: !30, scopeLine: 6, spFlags: DISPFlagDefinition, unit: !17)
!30 = !DISubroutineType(types: !31)
!31 = !{null}
!32 = !DILocation(line: 6, column: 22, scope: !29)
!33 = distinct !DISubprogram(name: "__VERIFIER_assert", scope: !2, file: !2, line: 7, type: !34, scopeLine: 7, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !37)
!34 = !DISubroutineType(types: !35)
!35 = !{null, !36}
!36 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!37 = !{}
!38 = !DILocalVariable(name: "cond", arg: 1, scope: !33, file: !2, line: 7, type: !36)
!39 = !DILocation(line: 7, column: 28, scope: !33)
!40 = !DILocation(line: 7, column: 41, scope: !41)
!41 = distinct !DILexicalBlock(scope: !33, file: !2, line: 7, column: 40)
!42 = !DILocation(line: 7, column: 40, scope: !33)
!43 = !DILocation(line: 7, column: 49, scope: !44)
!44 = distinct !DILexicalBlock(scope: !41, file: !2, line: 7, column: 47)
!45 = !DILocation(line: 7, column: 64, scope: !44)
!46 = !DILocation(line: 7, column: 75, scope: !33)
!47 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 11, type: !48, scopeLine: 11, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !37)
!48 = !DISubroutineType(types: !49)
!49 = !{!36}
!50 = !DILocalVariable(name: "v", scope: !47, file: !2, line: 12, type: !36)
!51 = !DILocation(line: 12, column: 7, scope: !47)
!52 = !DILocation(line: 12, column: 11, scope: !47)
!53 = !DILocation(line: 13, column: 21, scope: !47)
!54 = !DILocation(line: 13, column: 23, scope: !47)
!55 = !DILocation(line: 13, column: 3, scope: !47)
!56 = !DILocalVariable(name: "c", scope: !47, file: !2, line: 14, type: !57)
!57 = !DIBasicType(name: "signed char", size: 8, encoding: DW_ATE_signed_char)
!58 = !DILocation(line: 14, column: 15, scope: !47)
!59 = !DILocation(line: 14, column: 19, scope: !47)
!60 = !DILocalVariable(name: "i", scope: !47, file: !2, line: 15, type: !36)
!61 = !DILocation(line: 15, column: 7, scope: !47)
!62 = !DILocation(line: 15, column: 11, scope: !47)
!63 = !DILocation(line: 16, column: 21, scope: !47)
!64 = !DILocation(line: 16, column: 23, scope: !47)
!65 = !DILocation(line: 16, column: 3, scope: !47)
!66 = !DILocalVariable(name: "a", scope: !47, file: !2, line: 17, type: !36)
!67 = !DILocation(line: 17, column: 7, scope: !47)
!68 = !DILocation(line: 17, column: 11, scope: !47)
!69 = !DILocation(line: 18, column: 21, scope: !47)
!70 = !DILocation(line: 18, column: 23, scope: !47)
!71 = !DILocation(line: 18, column: 3, scope: !47)
!72 = !DILocation(line: 19, column: 21, scope: !47)
!73 = !DILocation(line: 19, column: 23, scope: !47)
!74 = !DILocation(line: 19, column: 27, scope: !47)
!75 = !DILocation(line: 19, column: 33, scope: !47)
!76 = !DILocation(line: 19, column: 36, scope: !47)
!77 = !DILocation(line: 19, column: 38, scope: !47)
!78 = !DILocation(line: 19, column: 42, scope: !47)
!79 = !DILocation(line: 0, scope: !47)
!80 = !DILocation(line: 19, column: 3, scope: !47)
!81 = !DILocalVariable(name: "w", scope: !47, file: !2, line: 20, type: !19)
!82 = !DILocation(line: 20, column: 16, scope: !47)
!83 = !DILocation(line: 20, column: 34, scope: !47)
!84 = !DILocation(line: 21, column: 21, scope: !47)
!85 = !DILocation(line: 21, column: 23, scope: !47)
!86 = !DILocation(line: 21, column: 28, scope: !47)
!87 = !DILocation(line: 21, column: 3, scope: !47)
!88 = !DILocation(line: 22, column: 3, scope: !47)
