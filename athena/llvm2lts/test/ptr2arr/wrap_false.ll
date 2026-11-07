; ModuleID = 'ptr2arr/wrap_false.c'
source_filename = "ptr2arr/wrap_false.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1, !dbg !0
@.str.1 = private unnamed_addr constant [4 x i8] c"t.c\00", align 1, !dbg !7
@.str.2 = private unnamed_addr constant [12 x i8] c"reach_error\00", align 1, !dbg !12

; Function Attrs: noinline nounwind uwtable
define dso_local void @reach_error() #0 !dbg !27 {
  call void @__assert_fail(ptr noundef @.str, ptr noundef @.str.1, i32 noundef 3, ptr noundef @.str.2) #3, !dbg !30
  unreachable, !dbg !30
}

; Function Attrs: noreturn
declare void @__assert_fail(ptr noundef, ptr noundef, i32 noundef, ptr noundef) #1

; Function Attrs: noinline nounwind uwtable
define dso_local zeroext i8 @__p2a_wrap_u8(i8 noundef zeroext %0) #0 !dbg !31 {
  %2 = alloca i8, align 1
  store i8 %0, ptr %2, align 1
    #dbg_declare(ptr %2, !36, !DIExpression(), !37)
  %3 = load i8, ptr %2, align 1, !dbg !38
  ret i8 %3, !dbg !39
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !40 {
  %1 = alloca i32, align 4
  %2 = alloca i8, align 1
  %3 = alloca i8, align 1
  store i32 0, ptr %1, align 4
    #dbg_declare(ptr %2, !44, !DIExpression(), !45)
  %4 = call zeroext i8 @__VERIFIER_nondet_uchar(), !dbg !46
  store i8 %4, ptr %2, align 1, !dbg !45
  %5 = load i8, ptr %2, align 1, !dbg !47
  %6 = zext i8 %5 to i32, !dbg !47
  %7 = icmp ne i32 %6, 255, !dbg !49
  br i1 %7, label %8, label %9, !dbg !50

8:                                                ; preds = %0
  store i32 0, ptr %1, align 4, !dbg !51
  br label %20, !dbg !51

9:                                                ; preds = %0
    #dbg_declare(ptr %3, !52, !DIExpression(), !53)
  %10 = load i8, ptr %2, align 1, !dbg !54
  %11 = zext i8 %10 to i32, !dbg !54
  %12 = add nsw i32 %11, 1, !dbg !55
  %13 = trunc i32 %12 to i8, !dbg !54
  %14 = call zeroext i8 @__p2a_wrap_u8(i8 noundef zeroext %13), !dbg !56
  store i8 %14, ptr %3, align 1, !dbg !53
  %15 = load i8, ptr %3, align 1, !dbg !57
  %16 = zext i8 %15 to i32, !dbg !57
  %17 = icmp eq i32 %16, 0, !dbg !59
  br i1 %17, label %18, label %19, !dbg !60

18:                                               ; preds = %9
  call void @reach_error(), !dbg !61
  br label %19, !dbg !61

19:                                               ; preds = %18, %9
  store i32 0, ptr %1, align 4, !dbg !62
  br label %20, !dbg !62

20:                                               ; preds = %19, %8
  %21 = load i32, ptr %1, align 4, !dbg !63
  ret i32 %21, !dbg !63
}

declare zeroext i8 @__VERIFIER_nondet_uchar() #2

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { noreturn "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { noreturn }

!llvm.dbg.cu = !{!17}
!llvm.module.flags = !{!19, !20, !21, !22, !23, !24, !25}
!llvm.ident = !{!26}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(scope: null, file: !2, line: 6, type: !3, isLocal: true, isDefinition: true)
!2 = !DIFile(filename: "ptr2arr/wrap_false.c", directory: "/t", checksumkind: CSK_MD5, checksum: "111e91d25a1ca2f1c18a1f863e99c7af")
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
!31 = distinct !DISubprogram(name: "__p2a_wrap_u8", scope: !2, file: !2, line: 7, type: !32, scopeLine: 7, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!32 = !DISubroutineType(types: !33)
!33 = !{!34, !34}
!34 = !DIBasicType(name: "unsigned char", size: 8, encoding: DW_ATE_unsigned_char)
!35 = !{}
!36 = !DILocalVariable(name: "v", arg: 1, scope: !31, file: !2, line: 7, type: !34)
!37 = !DILocation(line: 7, column: 43, scope: !31)
!38 = !DILocation(line: 7, column: 55, scope: !31)
!39 = !DILocation(line: 7, column: 48, scope: !31)
!40 = distinct !DISubprogram(name: "main", scope: !2, file: !2, line: 8, type: !41, scopeLine: 8, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !17, retainedNodes: !35)
!41 = !DISubroutineType(types: !42)
!42 = !{!43}
!43 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!44 = !DILocalVariable(name: "x", scope: !40, file: !2, line: 9, type: !34)
!45 = !DILocation(line: 9, column: 17, scope: !40)
!46 = !DILocation(line: 9, column: 21, scope: !40)
!47 = !DILocation(line: 10, column: 7, scope: !48)
!48 = distinct !DILexicalBlock(scope: !40, file: !2, line: 10, column: 7)
!49 = !DILocation(line: 10, column: 9, scope: !48)
!50 = !DILocation(line: 10, column: 7, scope: !40)
!51 = !DILocation(line: 10, column: 17, scope: !48)
!52 = !DILocalVariable(name: "y", scope: !40, file: !2, line: 11, type: !34)
!53 = !DILocation(line: 11, column: 17, scope: !40)
!54 = !DILocation(line: 11, column: 35, scope: !40)
!55 = !DILocation(line: 11, column: 37, scope: !40)
!56 = !DILocation(line: 11, column: 21, scope: !40)
!57 = !DILocation(line: 12, column: 7, scope: !58)
!58 = distinct !DILexicalBlock(scope: !40, file: !2, line: 12, column: 7)
!59 = !DILocation(line: 12, column: 9, scope: !58)
!60 = !DILocation(line: 12, column: 7, scope: !40)
!61 = !DILocation(line: 12, column: 15, scope: !58)
!62 = !DILocation(line: 13, column: 3, scope: !40)
!63 = !DILocation(line: 14, column: 1, scope: !40)
