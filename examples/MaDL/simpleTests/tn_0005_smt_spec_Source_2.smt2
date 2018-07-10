(set-logic QF_LIA)





(declare-fun block_Source_2 () Bool)
(declare-fun idle_Source_1 () Bool)

(assert (= block_Source_2 idle_Source_1))


(assert (= idle_Source_1 false))

(assert block_Source_2)
(check-sat)
(get-model)
