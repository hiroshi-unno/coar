; ModuleID = 'scope/randtime.c'
source_filename = "scope/randtime.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !15 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  store i32 0, ptr %1, align 4
  %3 = call i64 @time(ptr noundef null) #3, !dbg !20
  %4 = trunc i64 %3 to i32, !dbg !21
  call void @srand(i32 noundef %4) #3, !dbg !22
    #dbg_declare(ptr %2, !23, !DIExpression(), !24)
  %5 = call i32 @rand() #3, !dbg !25
  store i32 %5, ptr %2, align 4, !dbg !24
  %6 = load i32, ptr %2, align 4, !dbg !26
  %7 = icmp slt i32 %6, 0, !dbg !28
  br i1 %7, label %8, label %9, !dbg !29

8:                                                ; preds = %0
  call void @reach_error(), !dbg !30
  br label %9, !dbg !30

9:                                                ; preds = %8, %0
  ret i32 0, !dbg !31
}

; Function Attrs: nocallback nounwind
declare void @srand(i32 noundef) #1

; Function Attrs: nocallback nounwind
declare i64 @time(ptr noundef) #1

; Function Attrs: nocallback nounwind
declare i32 @rand() #1

declare void @reach_error() #2

attributes #0 = { noinline nounwind uwtable "frame-pointer"="all" "min-legal-vector-width"="0" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { nocallback nounwind "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { "frame-pointer"="all" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cmov,+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #3 = { nocallback nounwind }

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!7, !8, !9, !10, !11, !12, !13}
!llvm.ident = !{!14}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, retainedTypes: !2, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "scope/randtime.c", directory: "/home/grafen/fptprove/athena/llvm2lts/test", checksumkind: CSK_MD5, checksum: "b2750553b2d68313cd2aae22ad5f5779")
!2 = !{!3, !4}
!3 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!4 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !5, size: 64)
!5 = !DIDerivedType(tag: DW_TAG_typedef, name: "time_t", file: !1, line: 3, baseType: !6)
!6 = !DIBasicType(name: "long", size: 64, encoding: DW_ATE_signed)
!7 = !{i32 7, !"Dwarf Version", i32 5}
!8 = !{i32 2, !"Debug Info Version", i32 3}
!9 = !{i32 1, !"wchar_size", i32 4}
!10 = !{i32 8, !"PIC Level", i32 2}
!11 = !{i32 7, !"PIE Level", i32 2}
!12 = !{i32 7, !"uwtable", i32 2}
!13 = !{i32 7, !"frame-pointer", i32 2}
!14 = !{!"clang version 19.1.7 (/home/runner/work/llvm-project/llvm-project/clang cd708029e0b2869e80abe31ddb175f7c35361f90)"}
!15 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 8, type: !16, scopeLine: 8, flags: DIFlagPrototyped, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !19)
!16 = !DISubroutineType(types: !17)
!17 = !{!18}
!18 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!19 = !{}
!20 = !DILocation(line: 9, column: 23, scope: !15)
!21 = !DILocation(line: 9, column: 9, scope: !15)
!22 = !DILocation(line: 9, column: 3, scope: !15)
!23 = !DILocalVariable(name: "r", scope: !15, file: !1, line: 10, type: !18)
!24 = !DILocation(line: 10, column: 7, scope: !15)
!25 = !DILocation(line: 10, column: 11, scope: !15)
!26 = !DILocation(line: 11, column: 7, scope: !27)
!27 = distinct !DILexicalBlock(scope: !15, file: !1, line: 11, column: 7)
!28 = !DILocation(line: 11, column: 9, scope: !27)
!29 = !DILocation(line: 11, column: 7, scope: !15)
!30 = !DILocation(line: 11, column: 14, scope: !27)
!31 = !DILocation(line: 12, column: 3, scope: !15)
