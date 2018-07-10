(set-logic QF_LIA)





(declare-fun block_Queue_1 () Bool)
(declare-fun block_Queue_2 () Bool)
(declare-fun block_Source_1 () Bool)
(declare-fun Queue_2 () Int) (assert (<= 0 Queue_2)) (assert (<= Queue_2 2))

(assert (= block_Source_1 (and (= 2 (* 1 Queue_2)) block_Queue_2)))


(assert (= block_Queue_1 false))

(declare-fun Queue_1 () Int) (assert (<= 0 Queue_1)) (assert (<= Queue_1 2))

(assert (= block_Queue_2 (and (= 2 (* 1 Queue_1)) (>= (* 1 Queue_2) 1) block_Queue_1)))

(assert block_Source_1)
(check-sat)
(get-model)
