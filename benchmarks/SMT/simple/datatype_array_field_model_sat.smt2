; Correct answer: sat, with values for both w0 and w1.
; Require both decoded bindings as well as sat: a datatype registered only while encoding a
; selector field once made the model lose them.
(declare-datatype Payload ((payload (value Int))))
(declare-datatype Wrap ((wrap (field (Array Bool Payload)))))
(declare-const w0 Wrap)
(declare-const w1 Wrap)
(assert (distinct w0 w1))
(check-sat)
(get-model)
