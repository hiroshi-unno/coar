; A datatype declared in a `declare-datatypes` group, used as the ELEMENT SORT OF AN ARRAY inside a
; selector of another member of that same group.  The reader refuses it with
;
;     Failure "P is not defined"
;
; although SMT-LIB declares all the sorts of a group together, so every member is in scope in every
; body.  The sibling file next to this one, which differs only in that the selector's sort IS the
; group member rather than containing it, is read and answers `sat` -- which is the whole content of
; the defect: the group's members are consulted at the HEAD of a selector's sort expression and
; nowhere inside it, so any sort built over a sibling (an array of it, and presumably a
; parameterised datatype applied to it) falls through to the general sort reader, which is looking
; at an environment the group has not been added to yet.
;
; Reduced from a Rust program compiled by Thrust -- `let mut v = Vec::new(); v.push((11, 23));` --
; whose encoding puts `Tuple<Int-Int>` under the `Array` that represents the vector, in the same
; group as the `Mut` and `Tuple` wrappers around it.  Z3 reads that file and answers `sat`.
;
; expected: sat   (I x := the element read at 0 has a non-negative first projection)
(set-logic HORN)
(declare-datatypes ((P 0) (Q 0)) (
  ( (mkP (p0 Int)) )
  ( (mkQ (q0 (Array Int P))) )
))
(declare-fun I (Q) Bool)
(assert (forall ((x Q)) (=> (= (p0 (select (q0 x) 0)) 0) (I x))))
(assert (forall ((x Q)) (=> (I x) (>= (p0 (select (q0 x) 0)) 0))))
(check-sat)
