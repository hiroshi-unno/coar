; ModuleID = 'intmodes/bitconst_true.c'
source_filename = "intmodes/bitconst_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

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
  %3 = alloca i32, align 4
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !48, !DIExpression(), !49)
  %4 = call i32 @__VERIFIER_nondet_int(), !dbg !50
  store i32 %4, ptr %2, align 4, !dbg !49
    #dbg_declare(ptr %3, !51, !DIExpression(), !53)
  %5 = call i32 @__VERIFIER_nondet_uint(), !dbg !54
  store i32 %5, ptr %3, align 4, !dbg !53
  %6 = load i32, ptr %2, align 4, !dbg !55
  %7 = and i32 %6, 7, !dbg !56
  %8 = icmp sle i32 %7, 7, !dbg !57
  %9 = zext i1 %8 to i32, !dbg !57
  call void @__VERIFIER_assert(i32 noundef %9), !dbg !58
  %10 = load i32, ptr %2, align 4, !dbg !59
  %11 = ashr i32 %10, 1, !dbg !60
  %12 = mul nsw i32 %11, 2, !dbg !61
  %13 = load i32, ptr %2, align 4, !dbg !62
  %14 = and i32 %13, 1, !dbg !63
  %15 = add nsw i32 %12, %14, !dbg !64
  %16 = load i32, ptr %2, align 4, !dbg !65
  %17 = icmp eq i32 %15, %16, !dbg !66
  %18 = zext i1 %17 to i32, !dbg !66
  call void @__VERIFIER_assert(i32 noundef %18), !dbg !67
  %19 = load i32, ptr %2, align 4, !dbg !68
  %20 = or i32 %19, 1, !dbg !69
  %21 = load i32, ptr %2, align 4, !dbg !70
  %22 = and i32 %21, -2, !dbg !71
  %23 = sub nsw i32 %20, %22, !dbg !72
  %24 = icmp eq i32 %23, 1, !dbg !73
  %25 = zext i1 %24 to i32, !dbg !73
  call void @__VERIFIER_assert(i32 noundef %25), !dbg !74
  %26 = load i32, ptr %2, align 4, !dbg !75
  %27 = icmp slt i32 %26, 0, !dbg !77
  br i1 %27, label %28, label %33, !dbg !78

28:                                               ; preds = %0
  %29 = load i32, ptr %2, align 4, !dbg !79
  %30 = ashr i32 %29, 3, !dbg !80
  %31 = icmp slt i32 %30, 0, !dbg !81
  %32 = zext i1 %31 to i32, !dbg !81
  call void @__VERIFIER_assert(i32 noundef %32), !dbg !82
  br label %33, !dbg !82

33:                                               ; preds = %28, %0
  %34 = load i32, ptr %3, align 4, !dbg !83
  %35 = lshr i32 %34, 31, !dbg !84
  %36 = icmp ule i32 %35, 1, !dbg !85
  %37 = zext i1 %36 to i32, !dbg !85
  call void @__VERIFIER_assert(i32 noundef %37), !dbg !86
  %38 = load i32, ptr %3, align 4, !dbg !87
  %39 = and i32 %38, 255, !dbg !88
  %40 = load i32, ptr %3, align 4, !dbg !89
  %41 = and i32 %40, -256, !dbg !90
  %42 = add i32 %39, %41, !dbg !91
  %43 = load i32, ptr %3, align 4, !dbg !92
  %44 = icmp eq i32 %42, %43, !dbg !93
  %45 = zext i1 %44 to i32, !dbg !93
  call void @__VERIFIER_assert(i32 noundef %45), !dbg !94
  %46 = load i32, ptr %3, align 4, !dbg !95
  %47 = xor i32 %46, 5, !dbg !96
  %48 = xor i32 %47, 5, !dbg !97
  %49 = load i32, ptr %3, align 4, !dbg !98
  %50 = icmp eq i32 %48, %49, !dbg !99
  %51 = zext i1 %50 to i32, !dbg !99
  call void @__VERIFIER_assert(i32 noundef %51), !dbg !100
  ret i32 0, !dbg !101
}

declare i32 @__VERIFIER_nondet_int() #3

declare i32 @__VERIFIER_nondet_uint() #3

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
!2 = !DIFile(filename: "intmodes/bitconst_true.c", directory: "/d", checksumkind: CSK_MD5, checksum: "9c889e8798095a639cedcae63635b5bd")
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
!17 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, globals: !18, splitDebugInlining: false, nameTableKind: None)
!18 = !{!0, !7, !12}
!19 = !{i32 7, !"Dwarf Version", i32 5}
!20 = !{i32 2, !"Debug Info Version", i32 3}
!21 = !{i32 1, !"wchar_size", i32 4}
!22 = !{i32 8, !"PIC Level", i32 2}
!23 = !{i32 7, !"PIE Level", i32 2}
!24 = !{i32 7, !"uwtable", i32 2}
!25 = !{i32 7, !"frame-pointer", i32 2}
!26 = !{!"clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)"}
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
!45 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 10, type: !46, scopeLine: 10, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!46 = !DISubroutineType(types: !47)
!47 = !{!34}
!48 = !DILocalVariable(name: "x", scope: !45, file: !2, line: 11, type: !34)
!49 = !DILocation(line: 11, column: 7, scope: !45)
!50 = !DILocation(line: 11, column: 11, scope: !45)
!51 = !DILocalVariable(name: "u", scope: !45, file: !2, line: 12, type: !52)
!52 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!53 = !DILocation(line: 12, column: 16, scope: !45)
!54 = !DILocation(line: 12, column: 20, scope: !45)
!55 = !DILocation(line: 13, column: 22, scope: !45)
!56 = !DILocation(line: 13, column: 24, scope: !45)
!57 = !DILocation(line: 13, column: 29, scope: !45)
!58 = !DILocation(line: 13, column: 3, scope: !45)
!59 = !DILocation(line: 14, column: 22, scope: !45)
!60 = !DILocation(line: 14, column: 24, scope: !45)
!61 = !DILocation(line: 14, column: 30, scope: !45)
!62 = !DILocation(line: 14, column: 37, scope: !45)
!63 = !DILocation(line: 14, column: 39, scope: !45)
!64 = !DILocation(line: 14, column: 34, scope: !45)
!65 = !DILocation(line: 14, column: 47, scope: !45)
!66 = !DILocation(line: 14, column: 44, scope: !45)
!67 = !DILocation(line: 14, column: 3, scope: !45)
!68 = !DILocation(line: 15, column: 22, scope: !45)
!69 = !DILocation(line: 15, column: 24, scope: !45)
!70 = !DILocation(line: 15, column: 32, scope: !45)
!71 = !DILocation(line: 15, column: 34, scope: !45)
!72 = !DILocation(line: 15, column: 29, scope: !45)
!73 = !DILocation(line: 15, column: 40, scope: !45)
!74 = !DILocation(line: 15, column: 3, scope: !45)
!75 = !DILocation(line: 16, column: 7, scope: !76)
!76 = distinct !DILexicalBlock(scope: !45, file: !2, line: 16, column: 7)
!77 = !DILocation(line: 16, column: 9, scope: !76)
!78 = !DILocation(line: 16, column: 7, scope: !45)
!79 = !DILocation(line: 16, column: 33, scope: !76)
!80 = !DILocation(line: 16, column: 35, scope: !76)
!81 = !DILocation(line: 16, column: 41, scope: !76)
!82 = !DILocation(line: 16, column: 14, scope: !76)
!83 = !DILocation(line: 17, column: 22, scope: !45)
!84 = !DILocation(line: 17, column: 24, scope: !45)
!85 = !DILocation(line: 17, column: 31, scope: !45)
!86 = !DILocation(line: 17, column: 3, scope: !45)
!87 = !DILocation(line: 18, column: 22, scope: !45)
!88 = !DILocation(line: 18, column: 24, scope: !45)
!89 = !DILocation(line: 18, column: 36, scope: !45)
!90 = !DILocation(line: 18, column: 38, scope: !45)
!91 = !DILocation(line: 18, column: 33, scope: !45)
!92 = !DILocation(line: 18, column: 51, scope: !45)
!93 = !DILocation(line: 18, column: 48, scope: !45)
!94 = !DILocation(line: 18, column: 3, scope: !45)
!95 = !DILocation(line: 19, column: 23, scope: !45)
!96 = !DILocation(line: 19, column: 25, scope: !45)
!97 = !DILocation(line: 19, column: 31, scope: !45)
!98 = !DILocation(line: 19, column: 40, scope: !45)
!99 = !DILocation(line: 19, column: 37, scope: !45)
!100 = !DILocation(line: 19, column: 3, scope: !45)
!101 = !DILocation(line: 20, column: 3, scope: !45)
