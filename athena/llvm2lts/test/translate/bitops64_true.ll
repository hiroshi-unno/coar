; ModuleID = 'bitops64_true.c'
source_filename = "bitops64_true.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !29 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #5, !dbg !32
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
  call void @abort() #6, !dbg !45
  unreachable, !dbg !45

6:                                                ; preds = %1
  ret void, !dbg !46
}

; Function Attrs: noreturn nounwind
declare void @abort() #2

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !47 {
  %1 = alloca i32, align 4
  %2 = alloca i64, align 8
  %3 = alloca i16, align 2
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !50, !DIExpression(), !52)
  %4 = call i64 @__VERIFIER_nondet_ulong(), !dbg !53
  store i64 %4, ptr %2, align 8, !dbg !52
    #dbg_declare(ptr %3, !54, !DIExpression(), !55)
  %5 = call zeroext i16 @__VERIFIER_nondet_ushort(), !dbg !56
  store i16 %5, ptr %3, align 2, !dbg !55
  %6 = load i16, ptr %3, align 2, !dbg !57
  %7 = call i16 @llvm.bswap.i16(i16 %6), !dbg !58
  %8 = zext i16 %7 to i32, !dbg !58
  %9 = load i16, ptr %3, align 2, !dbg !59
  %10 = zext i16 %9 to i32, !dbg !59
  %11 = shl i32 %10, 8, !dbg !60
  %12 = load i16, ptr %3, align 2, !dbg !61
  %13 = zext i16 %12 to i32, !dbg !61
  %14 = ashr i32 %13, 8, !dbg !62
  %15 = or i32 %11, %14, !dbg !63
  %16 = trunc i32 %15 to i16, !dbg !64
  %17 = zext i16 %16 to i32, !dbg !64
  %18 = icmp eq i32 %8, %17, !dbg !65
  %19 = zext i1 %18 to i32, !dbg !65
  call void @__VERIFIER_assert(i32 noundef %19), !dbg !66
  %20 = load i64, ptr %2, align 8, !dbg !67
  %21 = call i64 @llvm.ctpop.i64(i64 %20), !dbg !68
  %22 = trunc i64 %21 to i32, !dbg !68
  %23 = icmp sle i32 %22, 64, !dbg !69
  %24 = zext i1 %23 to i32, !dbg !69
  call void @__VERIFIER_assert(i32 noundef %24), !dbg !70
  %25 = load i64, ptr %2, align 8, !dbg !71
  %26 = icmp ne i64 %25, 0, !dbg !73
  br i1 %26, label %27, label %33, !dbg !74

27:                                               ; preds = %0
  %28 = load i64, ptr %2, align 8, !dbg !75
  %29 = call i64 @llvm.ctlz.i64(i64 %28, i1 true), !dbg !76
  %30 = trunc i64 %29 to i32, !dbg !76
  %31 = icmp slt i32 %30, 64, !dbg !77
  %32 = zext i1 %31 to i32, !dbg !77
  call void @__VERIFIER_assert(i32 noundef %32), !dbg !78
  br label %33, !dbg !78

33:                                               ; preds = %27, %0
  ret i32 0, !dbg !79
}

declare i64 @__VERIFIER_nondet_ulong() #3

declare zeroext i16 @__VERIFIER_nondet_ushort() #3

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i16 @llvm.bswap.i16(i16) #4

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.ctpop.i64(i64) #4

; Function Attrs: nocallback nofree nosync nounwind speculatable willreturn memory(none)
declare i64 @llvm.ctlz.i64(i64, i1 immarg) #4

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { noreturn nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #4 = { nocallback nofree nosync nounwind speculatable willreturn memory(none) }
attributes #5 = { noreturn }
attributes #6 = { noreturn nounwind }

!llvm.dbg.cu = !{!17}
!llvm.module.flags = !{!21, !22, !23, !24, !25, !26, !27}
!llvm.ident = !{!28}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 4, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "bitops64_true.c", directory: "/w", checksumkind: CSK_MD5, checksum: "bda411182931c31d2b8ef3a6b73838bf")
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
!17 = distinct !DICompileUnit(language: DW_LANG_C11, file: !2, producer: "Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, retainedTypes: !18, globals: !20, splitDebugInlining: false, nameTableKind: None)
!18 = !{!19}
!19 = !DIBasicType(name: "unsigned short", size: 16, encoding: DW_ATE_unsigned)
!20 = !{!0, !7, !12}
!21 = !{i32 7, !"Dwarf Version", i32 5}
!22 = !{i32 2, !"Debug Info Version", i32 3}
!23 = !{i32 1, !"wchar_size", i32 4}
!24 = !{i32 8, !"PIC Level", i32 2}
!25 = !{i32 7, !"PIE Level", i32 2}
!26 = !{i32 7, !"uwtable", i32 2}
!27 = !{i32 7, !"frame-pointer", i32 2}
!28 = !{!"Ubuntu clang version 19.1.7 (++20250804090312+cd708029e0b2-1~exp1~20250804210325.79)"}
!29 = distinct !DISubprogram(name: "reach_error", scope: !2, file: !2, line: 4, type: !30, scopeLine: 4, spFlags: DISPFlagDefinition, unit: !17)
!30 = !DISubroutineType(types: !31)
!31 = !{null}
!32 = !DILocation(line: 4, column: 22, scope: !29)
!33 = distinct !DISubprogram(name: "__VERIFIER_assert", scope: !2, file: !2, line: 5, type: !34, scopeLine: 5, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !37)
!34 = !DISubroutineType(types: !35)
!35 = !{null, !36}
!36 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!37 = !{}
!38 = !DILocalVariable(name: "cond", arg: 1, scope: !33, file: !2, line: 5, type: !36)
!39 = !DILocation(line: 5, column: 28, scope: !33)
!40 = !DILocation(line: 5, column: 41, scope: !41)
!41 = distinct !DILexicalBlock(scope: !33, file: !2, line: 5, column: 40)
!42 = !DILocation(line: 5, column: 40, scope: !33)
!43 = !DILocation(line: 5, column: 49, scope: !44)
!44 = distinct !DILexicalBlock(scope: !41, file: !2, line: 5, column: 47)
!45 = !DILocation(line: 5, column: 64, scope: !44)
!46 = !DILocation(line: 5, column: 75, scope: !33)
!47 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 8, type: !48, scopeLine: 8, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !37)
!48 = !DISubroutineType(types: !49)
!49 = !{!36}
!50 = !DILocalVariable(name: "y", scope: !47, file: !2, line: 9, type: !51)
!51 = !DIBasicType(name: "unsigned long", size: 64, encoding: DW_ATE_unsigned)
!52 = !DILocation(line: 9, column: 17, scope: !47)
!53 = !DILocation(line: 9, column: 21, scope: !47)
!54 = !DILocalVariable(name: "h", scope: !47, file: !2, line: 10, type: !19)
!55 = !DILocation(line: 10, column: 18, scope: !47)
!56 = !DILocation(line: 10, column: 22, scope: !47)
!57 = !DILocation(line: 11, column: 39, scope: !47)
!58 = !DILocation(line: 11, column: 21, scope: !47)
!59 = !DILocation(line: 11, column: 63, scope: !47)
!60 = !DILocation(line: 11, column: 65, scope: !47)
!61 = !DILocation(line: 11, column: 74, scope: !47)
!62 = !DILocation(line: 11, column: 76, scope: !47)
!63 = !DILocation(line: 11, column: 71, scope: !47)
!64 = !DILocation(line: 11, column: 45, scope: !47)
!65 = !DILocation(line: 11, column: 42, scope: !47)
!66 = !DILocation(line: 11, column: 3, scope: !47)
!67 = !DILocation(line: 12, column: 41, scope: !47)
!68 = !DILocation(line: 12, column: 21, scope: !47)
!69 = !DILocation(line: 12, column: 44, scope: !47)
!70 = !DILocation(line: 12, column: 3, scope: !47)
!71 = !DILocation(line: 13, column: 7, scope: !72)
!72 = distinct !DILexicalBlock(scope: !47, file: !2, line: 13, column: 7)
!73 = !DILocation(line: 13, column: 9, scope: !72)
!74 = !DILocation(line: 13, column: 7, scope: !47)
!75 = !DILocation(line: 13, column: 48, scope: !72)
!76 = !DILocation(line: 13, column: 33, scope: !72)
!77 = !DILocation(line: 13, column: 51, scope: !72)
!78 = !DILocation(line: 13, column: 15, scope: !72)
!79 = !DILocation(line: 14, column: 3, scope: !47)
