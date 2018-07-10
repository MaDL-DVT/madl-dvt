(set-logic QF_LIA)





(declare-fun block_Queue_1 () Bool)
(declare-fun block_Queue_2 () Bool)
(declare-fun block_Queue_3 () Bool)
(declare-fun block_Queue_4 () Bool)
(declare-fun block_Source_1 () Bool)
(declare-fun idle_Queue_1.b<> () Bool)
(declare-fun idle_Queue_1.r<> () Bool)
(declare-fun idle_Queue_3 () Bool)
(declare-fun idle_Queue_4 () Bool)
(declare-fun idle_Source_1.b<> () Bool)
(declare-fun idle_Source_1.r<> () Bool)
(declare-fun Queue_1 () Int) (assert (<= 0 Queue_1)) (assert (<= Queue_1 2))

(assert (= block_Source_1 (and (= 2 (* 1 Queue_1)) block_Queue_1)))

(declare-fun Queue_3 () Int) (assert (<= 0 Queue_3)) (assert (<= Queue_3 2))
(declare-fun Queue_4 () Int) (assert (<= 0 Queue_4)) (assert (<= Queue_4 2))
(declare-fun Queue_1.b<> () Int) (assert (>= Queue_1.b<> 0))
(declare-fun Queue_1.r<> () Int) (assert (>= Queue_1.r<> 0))
(assert (= Queue_1 (+ Queue_1.b<> Queue_1.r<>)))

(assert (= block_Queue_1 (or (and (= 2 (* 1 Queue_3)) (>= (* 1 Queue_1.r<>) 1) block_Queue_3) (and (= 2 (* 1 Queue_4)) (>= (* 1 Queue_1.b<>) 1) block_Queue_4))))

(declare-fun Queue_2 () Int) (assert (<= 0 Queue_2)) (assert (<= Queue_2 2))

(assert (= block_Queue_3 (and (>= (* 1 Queue_3) 1) (or (and (= 2 (* 1 Queue_2)) block_Queue_2) idle_Queue_4))))


(assert (= block_Queue_4 (and (>= (* 1 Queue_4) 1) (or (and (= 2 (* 1 Queue_2)) block_Queue_2) idle_Queue_3))))


(assert (= block_Queue_2 false))


(assert (= idle_Queue_1.b<> (or (and (= (* 1 Queue_1.b<>) 0) idle_Source_1.b<>) (and (= 2 (* 1 Queue_3)) (>= (* 1 Queue_1.r<>) 1) block_Queue_3))))


(assert (= idle_Queue_1.r<> (or (and (= (* 1 Queue_1.r<>) 0) idle_Source_1.r<>) (and (= 2 (* 1 Queue_4)) (>= (* 1 Queue_1.b<>) 1) block_Queue_4))))


(assert (= idle_Source_1.b<> (and (= 2 (* 1 Queue_1)) block_Queue_1)))


(assert (= idle_Source_1.r<> (and (= 2 (* 1 Queue_1)) block_Queue_1)))


(assert (= idle_Queue_3 (and (= (* 1 Queue_3) 0) idle_Queue_1.r<>)))


(assert (= idle_Queue_4 (and (= (* 1 Queue_4) 0) idle_Queue_1.b<>)))

(assert block_Source_1)
(check-sat)
(get-model)
