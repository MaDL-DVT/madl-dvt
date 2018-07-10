(set-logic QF_LIA)





(declare-fun block_Source_1 () Bool)
(declare-fun idle_Source_2 () Bool)

(assert (= block_Source_1 idle_Source_2))


(assert (= idle_Source_2 false))

(assert block_Source_1)
(check-sat)
(get-model)
