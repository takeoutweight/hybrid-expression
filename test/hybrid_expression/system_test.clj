(ns hybrid-expression.system-test
  (:require [hybrid-expression.system :refer :all]
            [clojure.test :refer :all]
            #_[taoensso.tufte :as tufte :refer (profiled profile)])
  (:refer-clojure :exclude [sequence]))

(defn approx-=
  [a b]
  (let [eps 0.000000000001]
    (< (Math/abs (- a b)) eps)))

(deftest state-api
  (let [state {:flows {:dog {:cat {:france 4 :dance 3}}}}]
    (is (= 3 (get-resource state [:dog :cat :dance])))
    (is (= (delete-resource state [:dog :cat :dance])
           {:flows {:dog {:cat {:france 4}}}}))
    (is (= (-> state
               (delete-resource [:dog :cat :dance])
               (delete-resource [:dog :cat :france]))
           {:flows {}}))))

(deftest test-time-of-condition
  (let [a (additive-hybrid [[[:A] -1]])
        init-state (-> empty-state
                       (set-flow-offset [:A] 10)
                       ((:init a)))]
    (is (approx-= 7.0 (second (time-of-condition init-state (->Equals? [:A] 3)))))))

(deftest preserve-fractional-bigdec
  (let [a (additive-hybrid [[[:A] -1]])
        init-state (-> empty-state
                       (set-flow-offset [:A] 10)
                       ((:init a)))]
    (is (= 7 (second (time-of-condition init-state (->Equals? [:A] 3))))
        "No bigdecs used, but we have exact equality"))
  (let [a (additive-hybrid [[[:A] -3]])
        init-state (-> empty-state
                       (set-flow-offset [:A] 10)
                       ((:init a)))]
    (is (= 7/3 (second (time-of-condition init-state (->Equals? [:A] 3))))
        "No bigdecs used, but we drop to rationals"))
  (let [a (additive-hybrid [[[:A] -1M]])
        init-state (-> empty-state
                       (set-flow-offset [:A] 10M)
                       ((:init a)))]
    (is (= 7M (second (time-of-condition init-state (->Equals? [:A] 3M))))
        "preserves bigdec time"))
  (let [a (additive-hybrid [[[:A] -3M]])
        init-state (-> empty-state
                       (set-flow-offset [:A] 10M)
                       ((:init a)))]
    (is (= 7/3 (second (time-of-condition init-state (->Equals? [:A] 3M))))
        "switches to rational if necessary")))

(deftest test-strict-par
  (let [a (additive-hybrid [[[:A] -1] [[:S] -1]])
        b (additive-hybrid [[[:B] -1] [[:S] -1]])
        c (scale-additive (additive-hybrid [[[:C] -1] [[:S] -1]]) 2.0)
        p (strict-par [a b c])
        init-state (-> empty-state
                       (set-flow-offset [:A] 10)
                       (set-flow-offset [:B] 20)
                       (set-flow-offset [:C] 40)
                       (set-flow-offset [:S] 60)
                       ((:init p)))
        final-state (-> init-state (steady-state))]
    (is (approx-= (get-flow-offset final-state [:A]) 0.0))
    (is (approx-= (get-in final-state [:flows :B :offset]) 3.333333333333333))
    (is (approx-= (get-in final-state [:flows :C :offset]) 6.666666666666666)))

  (let [h (strict-par [(timer 1) (timer 2) (timer 3)])
        init-state ((:init h) empty-state)
        final-state (steady-state init-state)]
    (is (approx-= (get final-state :time) 3)
        "Timers run together, in parallel"))

  (let [h (strict-par [])
        init-state ((:init h) empty-state)
        final-state (steady-state init-state)]
    (is (= true (get-resource final-state (:terminated h)))
        "zero-branch par has terminated.")
    (is (approx-= (get final-state :time) 0)
        "No time has passed")))

(deftest test-additive-sequence
  (let [a (additive-hybrid [[[:A] -1] [[:P] -1] [[:PP] 1]])
        b (additive-hybrid [[[:A] -1] [[:Q] -1] [[:QQ] 1]])
        p (sequence-hybrid'
           [(hfn [state]
                 (-> state
                     (set-flow-offset [:A] 10)
                     (set-flow-offset [:P] 5)
                     (set-flow-offset [:Q] 10)))
            a
            (hfn [state]
                 (-> state
                     (update-flow-offset [:A] + 1)))
            b])
        init-state (-> empty-state
                       ((:init p)))
        final-state (-> init-state (steady-state))
        final-offsets (get-dir-offset final-state [])]
    (is (approx-= (:A final-offsets) 0))
    (is (approx-= (:PP final-offsets) 5))
    (is (approx-= (:QQ final-offsets) 6))))

(deftest test-nested
  (let [a (additive-hybrid [[[:A :AA] -1] [[:S :SS] 1]])
        init-state (-> empty-state
                       (set-flow-offset [:A :AA] 10)
                       (set-flow-offset [:S :SS] 0)
                       ((:init a)))
        final-state (-> init-state (steady-state))]
    (is (approx-= (get-flow-offset final-state [:A :AA]) 0.0))
    (is (approx-= (get-flow-offset final-state [:S :SS]) 10.0))))

(deftest test-sequence
  (let [h (reduce sequence-hybrid [(timer 1) (timer 2) (timer 3)])
        init-state ((:init h) empty-state)
        final-state (steady-state init-state)]
    (is (approx-= (get final-state :time) 6)
        "Timers run one after another"))

  (let [sp (reduce sequence-hybrid
                   [(transition->hybrid (fn [state] (set-flow-offset state [:A] 10)))
                    (strict-par [(additive-hybrid [[[:A] -1]])
                                 (additive-hybrid [[[:A] -1]])])
                    (transition->hybrid (fn [state] (set-flow-offset state [:A] 123)))])
        init-state (->  empty-state
                        ((:init sp)))
        final-state (steady-state init-state)]
    (is (approx-= 123 (get-flow-offset final-state [:A]))
        "Effect of second transition doesn't interfere with additive bit.")
    (is (approx-= 5.0 (:time final-state))
        "we can sequence instantaneous events before and after strict-par")))

(deftest test-sequence-prime
  (let [h (sequence-hybrid' [(timer 1) (timer 2) (timer 3)])
        init-state ((:init h) empty-state)
        final-state (steady-state init-state)]
    (is (approx-= (get final-state :time) 6)
        "Timers run one after another"))

  (let [sp (sequence-hybrid'
            [(transition->hybrid (fn [state] (set-flow-offset state [:A] 10)))
             (strict-par [(additive-hybrid [[[:A] -1]])
                          (additive-hybrid [[[:A] -1]])])
             (transition->hybrid (fn [state] (set-flow-offset state [:A] 123)))])
        final-state (->  empty-state
                         ((:init sp))
                         (steady-state))]
    (is (approx-= 123 (get-flow-offset final-state [:A]))
        "Effect of second transition doesn't interfere with additive bit.")
    (is (approx-= 5.0 (:time final-state))
        "we can sequence instantaneous events before and after strict-par")))

(deftest test-timers
  (let [h (sequence-hybrid (strict-par [(at-time 1)
                                        (at-time 3)
                                        (at-time 2)])
                           (timer 4))
        state1 (-> empty-state ((:init h)) (steady-state))]
    (is (approx-= 7 (:time state1))
        "timers delay properly after absolute at-timers")
    (let [h2 (sequence-hybrid h (at-time 9))
          state2 (-> empty-state ((:init h2)) (steady-state))]
      (is (approx-= 9 (:time state2))
          "absolute at-timers can come after relative delayed timers and are still absolute."))))

(deftest test-impulse
  (let [m (impulse-list [[0,100] [10,200]] [:out])
        state ((:init m) (-> empty-state
                             (set-resource [:out] 0)))
        final-state (-> state
                        (steady-state))]
    (is (approx-= (get-in final-state [:flows :out]) 300))
    (is (approx-= (get-in final-state [:time]) 10)))
  (let [out [:out]
        h (strict-par [(impulse-list [[1 1] [1 1]] out)
                       (impulse-list [[1 2] [1 2]] out)])
        init-state (-> empty-state
                       (set-resource out 0)
                       ((:init h)))]
    (is (= 3 (get-resource (run init-state 1) out)))
    (is (= 6 (get-resource (run init-state 2) out)))))

(deftest test-timed-transition
  (let [init-state (-> empty-state
                       ((:init
                         (timed-transition 10
                                           (fn [state]
                                             (set-resource state [:did-the-thing] true))))))
        final-state (steady-state init-state)]
    (is (= nil (get-resource init-state [:did-the-thing])))
    (is (= true (get-resource final-state [:did-the-thing])))
    (is (approx-= 10 (get-in final-state [:time]))))

  (let [out [:out]
        a (do-at-time 1 (fn [state] (update-resource state out conj :A)))
        b (do-at-time 2 (fn [state] (update-resource state out conj :B)))
        init-state (-> empty-state
                       (set-resource out [])
                       ((:init (strict-par [a b]))))
        final-state (steady-state init-state)]
    (is (= [:A :B] (get-resource final-state out)))
    (is (approx-= 2 (get-in final-state [:time])))))

(deftest test-growth
  (let [final-state (-> empty-state
                        (set-flow-offset [:A] 100)
                        (set-flow-growth [:A] :a 0.1)
                        (run 2))]
    (is (approx-= (get-flow-offset final-state [:A]) 121))))

(deftest test-instant-ordering
  (let [out [:out]
        a #(timed-transition 1 (fn [state] (update-resource state out conj :A)))
        b #(timed-transition 1 (fn [state] (update-resource state out conj :B)))
        c #(timed-transition 1 (fn [state] (update-resource state out conj :C)))
        h (sequence-hybrid
           (strict-par [(reduce sequence-hybrid [(a) (a) (a)])
                        (sequence-hybrid (b) (b))
                        (sequence-hybrid (c) (c))])
           (strict-par [(sequence-hybrid (b) (b))
                        (sequence-hybrid (c) (c))]))
        init-state (-> empty-state
                       (set-resource out [])
                       ((:init h)))
        final-state (steady-state init-state)]
    (is (= (get-resource final-state out)
           [:A :B :C :A :B :C :A :B :C :B :C])
        "strict-par preserves top-to-bottom ordering of instantaneous events"))
  (let [out [:out]
        sq (sequence-hybrid (transition->hybrid (fn [state] (update-resource state out conj :A)))
                            (transition->hybrid (fn [state] (update-resource state out conj :B))))
        pr (strict-par [sq
                        (transition->hybrid (fn [state] (update-resource state out conj :C)))])
        init-state (-> empty-state
                       (set-resource out [])
                       ((:init pr)))
        final-state (steady-state init-state)]
    (is (= (get-resource final-state out)
           [:A :B :C])
        "The strict-par's second branch doesn't pre-empt the instantaneous sequencing of the first branch")))

(deftest test-repeat
  (let [out [:out]
        sq (repeat-hybrid (sequence-hybrid (timer 1)
                                           (transition->hybrid (fn [state] (update-resource state out inc)))))
        init-state (-> empty-state
                       (set-resource out 0)
                       ((:init sq)))
        final-state (run init-state 42)]
    (is (= 42 (get-resource final-state out)))))

;; Spot-checking asymptotics manually

;; 1000 "Elapsed time: 145.559063 msecs"
;; 10000 "Elapsed time: 1545.801996 msecs"
(defn test-sequence-asymptotics
  "Should grow linearly"
  [n]
  (let [out [:out]
        sq (sequence-hybrid'
            (repeatedly
             n
             #(sequence-hybrid (timer 1)
                               (transition->hybrid (fn [state] (update-resource state out inc)))) ))
        init-state (time (-> empty-state
                             (set-resource out 0)
                             ((:init sq))))
        final-state (time (run init-state n))]
    (get-resource final-state out)))

;; 100 "Elapsed time: 16.015727 msecs"
;; 1000 "Elapsed time: 164.19755 msecs"
(defn test-flowsum-asymptotics
  "Should grow linearly, i.e. proportionally to the number of non-stationary
  FlowSums, not total flowsums in the state."
  [n]
  (let [as (map (fn [idx] (sequence-hybrid
                           (hfn [state] (-> state
                                            (set-flow-offset [:in idx] 1)))
                           (additive-hybrid [[[:in idx] -1] [[:out] 1]])))
                (range n))
        h (sequence-hybrid' as)
        init-state (-> empty-state
                       (set-flow-offset [:out] 0)
                       ((:init h)))
        final-state (time (-> init-state (steady-state)))]
    (get-flow-offset final-state [:out])))

;;  1000  "Elapsed time:  28.313707 msecs"
;; 10000  "Elapsed time: 327.519595 msecs"
(defn test-parallel-jump-asymptotics
  "Should grow linearly w.r.t. number of jumps"
  [n]
  (let [sp (strict-par (for [t (range n)]
                         (at-time t)))
        init-state (-> empty-state
                       ((:init sp)))
        final-state (time (-> init-state (steady-state)))]
    (:time final-state)))

;; 100   "Elapsed time:   8.422763 msecs"
;; 1000  "Elapsed time:  58.813679 msecs"
;; 10000 "Elapsed time: 577.393626 msecs"
(defn test-heavily-shared-additive-asymptotics
  [n]
  (let [h (sequence-hybrid'
           [(hfn [state] (set-flow-offset state [:A] n))
            (strict-par (for [t (range n)]
                          (additive-hybrid [[[:A] -1]])))])
        init-state (-> empty-state
                       ((:init h)))
        final-state (time (-> init-state (steady-state)))]
    (:time final-state)))

;; Just to compared w/ shared additive
;; 100 "Elapsed time: 18.601745 msecs"
;; 500 "Elapsed time: 98.751613 msecs"
(defn test-unshared-additive-asymptotics
  [n]
  (let [h (strict-par (for [t (range n)]
                        (sequence-hybrid'
                         [(hfn [state] (set-flow-offset state [t] 1))
                          (additive-hybrid [[[t] -1]])])))
        init-state (-> empty-state
                       ((:init h)))
        final-state (time (-> init-state (steady-state)))]
    (:time final-state)))

#_
(tufte/add-basic-println-handler! {})
#_
(profile {} (test-heavily-shared-additive-asymptotics 1000))
