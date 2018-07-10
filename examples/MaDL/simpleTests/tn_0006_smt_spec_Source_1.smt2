(set-logic QF_LIA)





(declare-fun block_Source_1 () Bool)
(declare-fun idle_Source_3 () Bool)

(assert (= block_Source_1 idle_Source_3))


(assert (= idle_Source_3 false))

(assert block_Source_1)
(check-sat)
(get-model)
