(set-logic QF_LIA)





(declare-fun block_Source_3 () Bool)
(declare-fun idle_Source_1 () Bool)
(declare-fun idle_Source_2 () Bool)

(assert (= block_Source_3 (and idle_Source_1 idle_Source_2)))


(assert (= idle_Source_1 false))


(assert (= idle_Source_2 false))

(assert block_Source_3)
(check-sat)
(get-model)
