(set-logic QF_LIA)





(declare-fun block_Source_1 () Bool)

(assert (= block_Source_1 true))

(assert block_Source_1)
(check-sat)
(get-model)
