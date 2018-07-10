(set-logic QF_LIA)





(declare-fun block_Queue_1 () Bool)
(declare-fun block_Queue_2 () Bool)
(declare-fun block_Source_1 () Bool)
(declare-fun idle_Queue_3 () Bool)
(declare-fun idle_Source_2 () Bool)
(declare-fun Queue_2 () Int) (assert (<= 0 Queue_2)) (assert (<= Queue_2 2))

(assert (= block_Source_1 (and (= 2 (* 1 Queue_2)) block_Queue_2)))

(declare-fun Queue_1 () Int) (assert (<= 0 Queue_1)) (assert (<= Queue_1 2))

(assert (= block_Queue_2 (and (>= (* 1 Queue_2) 1) (or (and (= 2 (* 1 Queue_1)) block_Queue_1) idle_Queue_3))))


(assert (= block_Queue_1 false))


(assert (= idle_Source_2 false))

(declare-fun Queue_3 () Int) (assert (<= 0 Queue_3)) (assert (<= Queue_3 2))

(assert (= idle_Queue_3 (and (= (* 1 Queue_3) 0) idle_Source_2)))

(assert block_Source_1)
(check-sat)
(get-model)
