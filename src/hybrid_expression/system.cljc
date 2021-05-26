(ns hybrid-expression.system
  (:require [clojure.core :as c]
            #_[clojure.spec :as s]
            [clojure.set :as set]
            [clojure.data.avl :as avl]
            [clojure.data.priority-map :as pm]
            [hybrid-expression.resource-supply :as rs]
            #_[taoensso.tufte :as tufte :refer (defnp p profiled profile)]
            #_[clojure.core.typed :as t])
  (:refer-clojure :exclude [sequence]))

;; Erase tufte usage
(do
  (defmacro defnp [& args]
    `(defn ~@args))
  (defmacro p [label arg]
    arg))

#?(:cljs (enable-console-print!))

;;;;;;;;;;;;;;;;;;;; Core Types ;;;;;;;;;;;;;;;;;;;;

;;; A linear differential equation for a single dimension:
;;; These are kept super restricted for now so I don't need to get out my
;;; eigenvectors - Just an multiplicative growth term and a constant additive
;;; term. Variables can only refer to themselves. Let's use nil
;;; instead if 0 for "n/a" since that's little safer to test for equality than
;;; Real 0.0
#_(t/ann-record FlowTerm [growth :- (t/Option Double) additive :- (t/Option Double)])
(defrecord FlowTerm [growth additive])

;;; Contains a map of {labels FlowCondition}, representing the
;;; ordinary-differential linear system.

#_(t/ann-record FlowSum [terms :- (t/Map t/Keyword FlowTerm)
                         offset :- Double
                         last-refresh :- Double
                         summed-grow :- Double
                         summed-additive :- Double])
(defrecord FlowSum [terms offset last-refresh summed-growth summed-additive])


;;;;;;;;;;;;;;;;;;;; Helpers ;;;;;;;;;;;;;;;;;;;;

;; We want to allow "enriched values" in automata like provenance-tracking
;; values. this lets us forget the extra structure and deal with the raw value.
(defprotocol GetVal
  (get-val [t]))

(extend-protocol GetVal
  nil
  (get-val [t] nil)
  Object
  (get-val [t] t))

#_(t/ann safe+ (t/Fn [-> ]
                   [(t/Option Double) -> (t/Option Double)]
                   [(t/Option Double) (t/Option Double) -> (t/Option Double)]))
(defn safe+
  "handles nil as zero"
  ([] nil)
  ([a] a)
  ([a b] (if (nil? a)
           b
           (+ a (or b 0.0)))))

(defn promoting-divide
  "promotes bigdecs to rationals if we hit a repeating decimal
  expansion, so bigdecs can be used throughout"
  [numerator denominator]
  (try (/ numerator denominator)
       (catch java.lang.ArithmeticException e
         (/ (rationalize numerator)
            (rationalize denominator)))))

(defn promoting-+
  "promotes bigdecs to rationals if we hit a repeating decimal
  expansion, so bigdecs can be used throughout"
  [& args]
  (try (apply + args)
       (catch java.lang.ArithmeticException e
         (apply + (map rationalize args)))))

(defn reduce'
  "same as reduce but convenient arg order for ->"
  [s f args]
  (reduce f s args))

;;;  FlowSum -> FlowTerm
#_(t/ann ^:no-check sum-flow [FlowSum -> FlowTerm])
(defnp sum-flow
  "Erases the labels and sums all the terms in the linear system."
  [flowsum]
  (let [flows (vals (:terms flowsum))
        r (->FlowTerm (:summed-growth flowsum)
                      (:summed-additive flowsum))]
    r))

;;; conditions
#_(t/defalias Resource (t/HVec t/Any))
#_(t/ann-record IsZero? [variable :- Resource])
(defrecord IsZero? [variable])
#_(t/ann-record Equals? [variable :- Resource target :- t/Any])
(defrecord Equals? [variable target])
(defrecord TimeEquals? [target])

;; Condition, number, [int], state -> state
;; fire-time is absolute time, so sort order can be stable
;; (defrecord Jump [instant callback])

;;;;;;;;;;;;;;;;;;;; Core state API ;;;;;;;;;;;;;;;;;;;;
(def default-api ::default)

(defn lexi-sort [v1 v2]
  (let [c1 (count v1)
        c2 (count v2)]
    (loop [idx 0]
      (if (= idx c1)
        (if (= idx c2)
          0 ; both equal
          -1) ; v1 shorter and sharing a prefix
        (if (= idx c2)
          1 ; v2 shorter and sharing a prefix
          (if (< (nth v1 idx) (nth v2 idx))
            -1
            (if (< (nth v2 idx) (nth v1 idx))
              1
              (recur (inc idx)))))))))

(defn timed-jump-condition-sort
  "sorts by fire-time, then by instant (but this is for disambiguation, we need
  to resort-by instant again when considering non-time-sorted jumps).

  The ::split-marker is lower than all same-timed events."
  [a b]
  (let [c (compare (::fire-time a) (::fire-time b))]
    (case c
      0 (if (= ::split-marker (::sortable-jump-condition a))
          (if (= ::split-marker (::sortable-jump-condition b))
            0
            -1)
          (if (= ::split-marker (::sortable-jump-condition b))
            1
            (let [c2 (compare (hash a) (hash b))]
              (case c2
                0 (if (= a b)
                    0
                    (throw (ex-info "collision on sorting jump conditions" {:a a :b b}))) ;; dubious, but Avl uses the sort order to determine set identity
                c2))))
      c)))

(defn active-lexi-jump-sort
  "compares two jumps based on instant."
  [a b]
  (lexi-sort (::instant a)
             (::instant b)))

(comment 
(s/def ::variable (s/or :regular (s/coll-of (s/or :int int? :keyword keyword?)
                                            :kind-of vector?)
                        :time #{::time}))
(s/def ::target number?)
(s/def ::IsZero (s/keys :req-un [::variable]))
(s/def ::Equals (s/keys :req-un [::variable ::target]))
(s/def ::TimeEquals (s/keys :req-un [::target]))
(s/def ::split-marker #{::split-marker})
(s/def ::jump-condition (s/or :is-zero ::IsZero
                              :equals ::Equals
                              :time-equals ::TimeEquals))
(s/def ::state (s/keys :req [::jump-conditions
                             ::active-jump-conditions
                             ::timed-jump-conditions]))
(s/def ::instant (s/coll-of int? :kind-of vector?))
(s/def ::transition (s/fspec :args (s/cat :state ::state) :ret ::state))
(s/def ::jump (s/keys :req [::instant ::transition]))
(s/def ::jumps (s/coll-of ::jump :kind-of set?))
(s/def ::stage #{:active :timed :inactive})
(s/def ::jump-conditions (s/map-of ::variable
                                   (s/map-of ::jump-condition
                                             (s/keys :req [::jumps ::stage])
                                             :conform-keys true)
                                   :conform-keys true))
(s/def ::timed-jump-conditions (s/map-of ::jump-condition number? :conform-keys true)
  ;; The old avl way
  #_(s/def ::fire-time number?)
  #_(s/def ::sortable-jump-condition (s/or :normal-jump ::jump-condition
                                           :split-marker ::split-marker))
  #_(s/coll-of (s/keys :req [::sortable-jump-condition
                             ::fire-time]) :kind-of set?))
(s/def ::active-jump-conditions (s/map-of ::jump-condition ::jumps
                                          :conform-keys true))

(s/fdef add-jumps
  :args (s/cat :state ::state :condtn ::jump-condition :jumps ::jumps :caller-label (s/? any?))
  :ret ::state)
)

(def empty-state
  {:flows {} :time 0 :step 0 :state-api default-api
   ::jump-conditions {}
   ::active-jump-conditions (pm/priority-map-keyfn-by #(::instant (first %)) lexi-sort)
   ::timed-jump-conditions (pm/priority-map)})

(defn api-dispatch [state & args] (get state :state-api default-api))

(defn post-update-fn
  "Hook for a function run after every update function. Intended for things like
  state predicates during testing."
  [state]
  (if (:post-update-fn state)
    ((:post-update-fn state) state)
    state))

;; This is most likely not the best way to do this - placeholder representing
;; "modularity!" for now.  Gives the operators needed to do possibly
;; enriched-api calcs w/ `evolve-state`.
(defmulti  get-arithmetic api-dispatch)
(defmethod get-arithmetic default-api
  [state] {:+ +
           :* *
           :pow (fn [base exp] (Math/pow base exp))})

(defmulti  get-resource api-dispatch)
(defmethod get-resource default-api
  [state path]
  (get-in state (concat [:flows] path)))

;; The interval over which we rely on explicit instant labels to sort. Doesn't
;; imply time runs at this resolution; just how eagerly to break ties for callbacks via instant labels.
(def instant-epsilon 0.0000001)

(defnp time-of-condition
  "returns [:timed timestep] or [:active] or [:inactive]. Timestpes are absolute time so we can
  keep a stable sort."
  [state condition & [negative-additive-slope?]]
  (let [[rtag rnum]
        ,(condp instance? condition
           IsZero? (time-of-condition state (->Equals? (:variable condition) 0) :negative-additive-slope)
           Equals? (let [ ;_ (prn {:state state :condition (:variable condition)})
                         varstate (get-val (get-resource state (:variable condition)))
                         target (:target condition)
                         constant-ret #(if (= % target) [:active] [:inactive])] ;; TODO make double-safe
                     (if (instance? FlowSum varstate)
                       ,(let [flowterm (sum-flow varstate)
                              growth (if (= 0 (:growth flowterm)) nil (:growth flowterm))
                              slope (if (= 0 (:additive flowterm)) nil (:additive flowterm)) ;; TODO Make these double-safe and compare to some epsilon
                              offset (get-val (:offset varstate))]
                          (if (some? growth)
                            (throw (ex-info "TODO: Not solving for growth yet." {:varstate varstate}))
                            (if (and (some? slope)
                                     (if negative-additive-slope? (< slope 0) true))
                              (do
                                #_(prn "delta-x" target offset slope varstate)
                                (let [delta-x (promoting-divide (- target offset) slope)]
                                  [:timed (promoting-+ delta-x (or (:last-refresh varstate) 0))]))
                              (constant-ret offset))))
                       (constant-ret varstate)))
           TimeEquals? [:timed (:target condition)])]
    (if (and (= :timed rtag)
             (< rnum (+ (:time state) instant-epsilon)))
      [:active]
      [rtag rnum])))

(defn watched-var
  [condtn]
  (condp instance? condtn
    IsZero? (:variable condtn)
    Equals? (:variable condtn)
    TimeEquals? ::time))

(defn add-jumps
  "A jump is a state transition that activates on a particular condition at a particular instant.
  The transition is a pure function of the state that returns a modified state."
  [state condtn jumps & [caller-label]]
  (p [::add-jump caller-label]
    (let [w-var (watched-var condtn)
          prev-stage (get-in state [::jump-conditions w-var condtn ::stage])
          state
          ,(case prev-stage
             nil (let [[next-stage maybe-next-time] (time-of-condition state condtn)]
                   (cond-> (assoc-in state
                                     [::jump-conditions w-var condtn]
                                     {::jumps jumps
                                      ::stage next-stage})
                     ;; inactive, no need to do anything
                     (= :timed next-stage)
                     (assoc-in [::timed-jump-conditions condtn] maybe-next-time)
                     (= :active next-stage)
                     (assoc-in [::active-jump-conditions condtn]
                               (if (instance? clojure.data.avl.AVLSet jumps)
                                 (do
                                   #_(prn "Re-using pre-sorted jumps" (count jumps))
                                   jumps)
                                 (do
                                   #_(prn "sorting" (count jumps) "jumps")
                                   (apply avl/sorted-set-by active-lexi-jump-sort jumps))))))
             :inactive (update-in state [::jump-conditions w-var condtn ::jumps] set/union jumps)
             :timed    (update-in state [::jump-conditions w-var condtn ::jumps] set/union jumps)
             :active (-> state
                         (update-in [::jump-conditions w-var condtn ::jumps] set/union jumps)
                         (update-in [::active-jump-conditions condtn]
                                    (fn [existing-jumps]
                                      (apply conj existing-jumps jumps)))))]
      (-> state
          (post-update-fn)))))

(defn add-jump
  "A jump is a state transition that activates on a particular condition.
  The transition is a pure function of the state that returns a modified state."
  [state path instant condtn transition & [caller-label]]
  #_(prn "add-jump at " (:time state) path instant condtn)
  (add-jumps state condtn #{{::instant instant ::transition transition}} caller-label))

(defnp refresh-watching-jumps
  "Remove the jump-condition from the state so it can be re-added with an updated state."
  [state path & [caller-label]]
  (reduce (fn [state [jump-condition {:keys [::jumps ::stage]}]]
            (let [state (update-in state [::jump-conditions path] dissoc jump-condition)]
              (case stage
                :active (let [sorted-jumps (get-in state [::active-jump-conditions jump-condition])]
                          #_(prn "trying to preserve sorting of" (count sorted-jumps) ":" (type sorted-jumps))
                          (-> state
                              (update ::active-jump-conditions dissoc jump-condition)
                              (add-jumps jump-condition sorted-jumps [::refresh-watching caller-label])))
                :timed  (-> state
                            (update ::timed-jump-conditions  dissoc jump-condition)
                            (add-jumps jump-condition jumps [::refresh-watching caller-label]))
                (add-jumps state jump-condition jumps [::refresh-watching caller-label])))
            #_(prn "refreshing " jump-condition))
          state
          (get-in state [::jump-conditions path])))

(declare refresh-flow)
(declare get-offset-recursive)

(defmulti  get-flow-offset api-dispatch)
(defmethod get-flow-offset default-api
  [state path]
  (let [flow (get-in state (concat [:flows] path))]
    (-> flow
        (refresh-flow (:time state))
        (:offset))))

(defmulti get-dir-offset
  "gets an entire state directory, recursively erasing any FlowSums and
  replacing them with their offset values."
  api-dispatch)
(defmethod get-dir-offset default-api
  [state path]
  (-> (get-in state (concat [:flows] path))
      (get-offset-recursive (:time state))))

(defmulti  update-resource api-dispatch)
(defmethod update-resource default-api
  [state path f & args]
  #_(prn "update-resource" path)
  (-> (apply update-in state (concat [:flows] path) f args)
      (refresh-watching-jumps path ::update-resource)
      (post-update-fn)))

(defnp update-flow-offset
  [state path f & args]
  (let [state (update-in state (concat [:flows] path) refresh-flow (:time state))]
    #_(prn "update-flow-offset" path)
    (-> (apply update-in state (concat [:flows] path [:offset]) f args)
        (refresh-watching-jumps path ::update-flow-offset)
        (post-update-fn))))

(declare delete-resource)
(defnp delete-empty-subdirs
  "recursively delete empty subdirectories starting at path"
  [state path]
  (-> (if (and (seq path)
               (empty? (get-val (get-resource state path))))
        (delete-resource state path)
        state)
      (post-update-fn)))

(defnp set-resource
  "set resources to a raw value, (i.e. not a FlowSum offset that can
  continuously change over time)"
  [state & path-vals]
  (assert (even? (count path-vals)) "even number of path/val pairs must be supplied")
  #_(prn "set-resource" path-vals)
  (-> (reduce (fn [state [path val]]
                ;; Just in case we /do/ set a FlowSum w/ this api call --
                ;; currently the only way to set values in ome transactional
                ;; batch:
                (let [val' (if (instance? FlowSum val)
                             (assoc val :last-refresh (:time state))
                             val)]
                  (-> state
                      (assoc-in (concat [:flows] path) val')
                      (refresh-watching-jumps path ::set-resource))))
              state
              (partition 2 path-vals))
      (post-update-fn)))

(defnp set-flow-offset
  [state path offset]
  #_(prn "set-flow-offset" path offset)
  (when-not (number? offset) (throw (ex-info "must supply number for set-flow-offset" {:path path :offset offset})))
  (let [existing (get-val (get-resource state path))
        new (cond
              (nil? existing)
              ,(assoc-in state (concat [:flows] path)
                         (->FlowSum {} offset (:time state) 0 0))
              (instance? FlowSum existing)
              ,(-> state
                   (assoc-in (concat [:flows] path [:offset]) offset)
                   (assoc-in (concat [:flows] path [:last-refresh]) (:time state)))
              :else
              (throw (ex-info "Resource not a FlowSum" {:existing existing})))]
    (-> new
        (refresh-watching-jumps path ::set-flow-offset)
        (post-update-fn))))

;; Maybe we should separate add-flow and set-flow? This does both.
(defnp set-flow-additive
  "Defaults to offset 0 if the flow hasn't been initialized."
  [state path termkey slope]
  (let [fpath (concat [:flows] path)
        existing (get-in state fpath)
        new (cond
              (nil? existing)
              ,(assoc-in state fpath
                         (->FlowSum {termkey (->FlowTerm 0 slope)} 0 (:time state) 0 slope))
              (instance? FlowSum existing)
              ,(-> state
                   (update-in fpath refresh-flow (:time state))
                   (assoc-in (concat fpath [:terms termkey])
                             (->FlowTerm 0 slope))
                   (update-in (concat fpath [:summed-additive]) + slope))
              :else
              (throw (ex-info "Resource not a FlowSum" {:existing existing})))]
    #_(prn "set-flow-additive" path slope (get-in new fpath))
    (-> new
        (refresh-watching-jumps path ::set-flow-additive)
        (post-update-fn))))

(defnp delete-flow-additive
  "removes an additive component from a FlowSum."
  [state path termkey]
  (let [fpath (concat [:flows] path)
        new (-> state
                (update-in fpath refresh-flow (:time state))
                (update-in (concat fpath [:terms]) dissoc termkey))]
    (-> new
        (refresh-watching-jumps path ::delete-flow-additive)
        (post-update-fn))))

(defnp set-flow-growth
  "Defaults to offset 0 if the flow hasn't been initialized."
  [state path termkey growth]
  #_(prn "set-flow-growth" path)
  (let [fpath (concat [:flows] path)
        existing (get-in state fpath)
        new (cond
              (nil? existing)
              ,(assoc-in state fpath
                         (->FlowSum {termkey (->FlowTerm growth 0)} 0 (:time state) growth 0))
              (instance? FlowSum existing)
              ,(-> state
                   (update-in fpath refresh-flow (:time state))
                   (assoc-in (concat fpath [:terms termkey])
                             (->FlowTerm growth 0))
                   (update-in (concat fpath [:summed-growth]) + growth))
              :else
              (throw (ex-info "Resource not a FlowSum" {:existing existing})))]
    (-> new
        (refresh-watching-jumps path ::set-flow-growth)
        (post-update-fn))))

(defnp delete-resource
  "Deletes a resource or subdir of resources, as well as the parent directory if it is empty."
  [state path]
  (-> state
      (update-in (concat [:flows] (butlast path)) dissoc (last path))
      (delete-empty-subdirs (butlast path))
      (post-update-fn)))

;; Q: Should termkeys be paths for uniformity? or is raw keywords more accurate as they can't nest?
(defnp delete-flow-term
  "Deletes a particular additive term from the resource."
  [state path termkey]
  (let [fpath (concat [:flows] path)
        old-term (get-in state (concat fpath [:terms termkey]))]
    #_(prn "delete-flow-term " old-term "from" (get-in state (concat fpath)))
    (assert (some? old-term))
    (let [state (-> state
                    (update-in (concat fpath) refresh-flow (:time state))
                    (update-in (concat fpath [:summed-additive]) - (:additive old-term))
                    (update-in (concat fpath [:summed-growth])   - (:growth old-term))
                    (update-in (concat fpath [:terms]) dissoc termkey))]
      #_(prn "after deletion " (get-in state fpath))
      (-> state
          (refresh-watching-jumps path ::delete-flow-term)
          (post-update-fn)))))

(defn time-til-condition
  "returns a timestep or nil for never. We also can return a negative time,
  which represents never as well (the only time the condition is true is in the
  past, not now).

  Just supports linear flow for now, but you can see how this could solve for
  different flavours of trajectories, becoming a multimethod or somesuch."
  [state condition & [negative-additive-slope?]]
  (condp instance? condition
    IsZero? (time-til-condition state (->Equals? (:variable condition) 0) :negative-additive-slope)
    Equals? (let [;_ (prn {:state state :condition (:variable condition)})
                  varstate (get-val (get-resource state (:variable condition)))
                  target (:target condition)
                  constant-ret #(if (= % target) 0.0 nil)] ;; TODO make double-safe
              (if (instance? FlowSum varstate)
                ,(let [flowterm (sum-flow varstate)
                       growth (if (= 0 (:growth flowterm)) nil (:growth flowterm))
                       dx (if (= 0 (:additive flowterm)) nil (:additive flowterm))  ;; TODO Make these double-safe and compare to some epsilon
                       offset (get-val (:offset varstate))]
                   (if (some? growth)
                     (throw (ex-info "TODO: Not solving for growth yet." {:varstate varstate}))
                     (if (and (some? dx)
                              (if negative-additive-slope? (< dx 0) true))
                       (let [delta (promoting-divide (- target offset) dx)]
                         (- (promoting-+ delta (or (:last-refresh varstate) 0))
                            (or (:time state) 0)))
                       (constant-ret offset))))
                (constant-ret varstate)))
    TimeEquals? (- (:target condition) (:time state))))

(defn dissoc-in-if-empty
  "(dissoc-in-if-empty {:cat {:flat []}} [:cat :flat]) => {:cat {}}"
  [m ks]
  (if (= 1 (count ks))
    (if (empty? (get-in m ks))
      (dissoc m (last ks))
      m)
    (if (empty? (get-in m ks))
      (update-in m (butlast ks) dissoc (last ks))
      m)))

;; used in scale-additive to remove alternate termination conditions when the first one fires
;; to replace delete-jump which worked by key
;; removing a jump that's gone is a noop - is this a good idea?
(defn remove-jump
  [state condtn jump]
  (let [w-var (watched-var condtn)]
    #_(prn "removing" w-var condtn jump)
    (if (nil? (get-in state [::jump-conditions w-var condtn ::jumps jump]))
      state
      (let [stage (get-in state [::jump-conditions w-var condtn ::stage])
            #_ (prn "jumps now0"  (get-in state [::jump-conditions w-var]))
            state (update-in state [::jump-conditions w-var condtn ::jumps] disj jump)
            last-jump? (empty? (get-in state [::jump-conditions w-var condtn ::jumps]))
            #_ (prn "jumps now1"  (get-in state [::jump-conditions w-var]))
            state (cond-> state
                    last-jump?
                    (update-in [::jump-conditions w-var] dissoc condtn))
            state (dissoc-in-if-empty state [::jump-conditions w-var])]
        #_(prn "jumps now2" (get-in state [::jump-conditions]))
        (case stage
          :active (cond-> (update-in state [::active-jump-conditions condtn] disj jump)
                    last-jump?
                    (update-in [::active-jump-conditions] dissoc condtn))
          :timed (cond-> state
                   last-jump?
                   (update ::timed-jump-conditions dissoc condtn))
          state)))))

;; NOOP - in case we decide to go back to not automatically activated fired
;; jumps, marks the places in the core abstractions we'd have to revisit. If you
;; really need to delete jumps, use remove-jump
(defmacro delete-jump
  [state path]
  state)

;; TODO Revist resource-supply ideas with this use-case in mind. It's pretty identical.
(defn next-instant
  "Instants are lexicographically sorted lists of Nats.
  This fn is the logical next-time of an instantanteous moment
  [0 0 1] -> [0 0 2]"
  [instant]
  (if (some? instant)
    (update instant (dec (count instant)) inc)
    [0]))

(defn split-instant
  "Create a new subdivision of the instant
  [0 0 1] -> [0 0 1 0]"
  [instant]
  (if (some? instant)
    (vec (concat instant [0]))
    [0]))

(defn fresh-instants
  "infinite sequences of fresh instants given a unique prefix"
  [instant]
  (iterate next-instant (split-instant instant)))

;;;;;;;;;;;;;;;;;;;; Some basic hybrid automata building blocks ;;;;;;;;;;;;;;;;;;;;

(def skip-hybrid
  "Does nothing but terminates immediately. An identity for sequence-hybrid."
  (let [term-path [(keyword (gensym "skip-"))]]
    {:init (fn [state & [instant]] (set-resource state term-path true))
     :terminated term-path}))

;; TODO probably better to take a list like all other combinators.
(defn sequence-hybrid
  [a b]
  (when (nil? (:terminated a))
    (throw (ex-info "Error: trying to sequence something after a certainly-nonterminating expression" {:hybrid a})))
  (let [jump-path-1 [(keyword (gensym "sequence-jump-1-"))]
        jump-path-2 [(keyword (gensym "sequence-jump-2-"))]
        term-path [(keyword (gensym "sequence-term-"))]]
    {:init (fn [state & [instant]]
             #_(prn "sequence-hybrid init called at " (:time state))
             (let [[i1 i2 i3 i4] (fresh-instants instant)
                   ;; we could save some code and just re-use (:terminated b) as
                   ;; our termination signal, but that doesn't work well with
                   ;; the "proper-tail call" optimization of repeat-hybrid.
                   terminate (fn [state]
                               (-> state
                                   (delete-resource (:terminated b))
                                   (delete-jump jump-path-2)
                                   (set-resource term-path true)))
                   transition (fn [state]
                                (let [state (-> state
                                                (delete-resource (:terminated a)) ;; Q: Here the sequencing "owns" the automaton. The finishing of the same machine can't be observed by two things. Depends on how I want to view automaton identity
                                                (delete-jump jump-path-1)
                                                ((:init b) i3))]
                                  (if (= true (get-resource state (:terminated b)))
                                    (terminate state)
                                    (add-jump state
                                              jump-path-2
                                              i4
                                              (->Equals? (:terminated b) true)
                                              terminate
                                              ::sequence-hybrid-transition))))
                   state (-> state
                             (set-resource term-path false)
                             ((:init a) i1))]
               ;; :inits are currently strict and can pre-empt the jump
               ;; trampoline, so here we make sure if we should run immediately
               ;; we do, so that we don't miss an immediate transition. There's
               ;; probably a more principled way trampoline ALL :inits via the
               ;; jumps to avoid this sort of care.
               (if (= true (get-resource state (:terminated a)))
                 (do #_(prn "early-a terminated")
                   (transition state))
                 (add-jump state
                           jump-path-1
                           i2
                           (->Equals? (:terminated a) true)
                           transition
                           ::sequence-hybrid-init))))
     :terminated term-path}))

(defn sequence-hybrid'
  "Takes a list of hybrids and sequences them. (This is intended to replace the
  other sequence-hybrid fn)"
  [hs]
  (let [non-terminators (->> (map vector (range) (butlast hs))
                             (filter (fn [[idx h]] (nil? (:terminated h)))))
        _ (when (not (empty? non-terminators))
            (throw (ex-info "Error: trying to sequence something after certainly-nonterminating expression"
                            {:non-terminators non-terminators})))
        hs-path [(keyword (gensym "sequence-hs-"))]
        jump-path [(keyword (gensym "sequence-jump-1-"))]
        term-path [(keyword (gensym "sequence-term-"))]]
    (cond
      (empty? hs) skip-hybrid
      (empty? (next hs)) (first hs)
      :else
      {:init (fn [state & [instant]]
               (let [;; we could save some code and just re-use (:terminated b) as
                     ;; our termination signal, but that doesn't work well with
                     ;; the "proper-tail call" optimization of repeat-hybrid.
                     terminate (fn [state]
                                 (-> state
                                     (delete-resource hs-path)
                                     (set-resource term-path true)))
                     transition (fn transition [state]
                                  (let [[[ia a] [ib b]] (get-resource state hs-path)
                                        [ib1 ib2] (fresh-instants ib)
                                        state (-> state
                                                  (update-resource hs-path next)
                                                  (delete-resource (:terminated a))
                                                  (delete-jump jump-path))]
                                    (if (nil? b)
                                      (terminate state)
                                      (let [state (-> state
                                                      ((:init b) ib1))]
                                        (if (= true (get-resource state (:terminated b)))
                                          (recur state)
                                          (add-jump state
                                                    jump-path
                                                    ib2
                                                    (->Equals? (:terminated b) true)
                                                    transition
                                                    ::sequence-hybrid-p-transition))))))
                     hs-list (map vector (fresh-instants instant) hs)
                     [[ia a]] hs-list
                     [ia1 ia2] (fresh-instants ia)
                     state (-> state
                               (set-resource hs-path hs-list)
                               (set-resource term-path false)
                               ((:init a) ia1))]
                 ;; :inits are currently strict and can pre-empt the jump
                 ;; trampoline, so here we make sure if we should run immediately
                 ;; we do, so that we don't miss an immediate transition. There's
                 ;; probably a more principled way trampoline ALL :inits via the
                 ;; jumps to avoid this sort of care.
                 (if (= true (get-resource state (:terminated a)))
                   (transition state)
                   (add-jump state
                             jump-path
                             ia2
                             (->Equals? (:terminated a) true)
                             transition
                             ::sequence-hybrid-p-init))))
       :terminated term-path})))

(defn repeat-hybrid
  "Sequentially repeats the hybrid indefinitely. Never terminates."
  [hybrid]
  (when (nil? (:terminated hybrid))
    (throw (ex-info "Error: trying to repeat a certainly-nonterminating expression" {:hybrid hybrid})))
  (let [jump-path [(keyword (gensym "repeat-jump-"))]]
    {:init (fn [state & [instant]]
             (let [[i1 i2] (fresh-instants instant)
                   transition (fn transition [state]
                                (-> state
                                    ((:init hybrid) i1)  ;; this is sort of an implicit proper-tail-call optimization. Is it always safe to treat machines as re-entrant like this?
                                    (add-jump jump-path
                                              i2
                                              (->Equals? (:terminated hybrid) true)
                                              transition
                                              ::repeat-hybrd-transition)))]
               ;; :inits are currently strict and can pre-empt the jump trampoline:
               (loop [state ((:init hybrid) state i1)]
                 (if (= true (get-resource state (:terminated hybrid)))
                   (recur (do
                            #_(prn "Early-repeat recur")
                            (transition state)))
                   (do
                     #_(prn "adding repeat-hybrid jump" jump-path i2)
                     (add-jump state
                               jump-path
                               i2
                               (->Equals? (:terminated hybrid) true)
                               transition
                               ::repeat-hybrd-init))))))}))

;; We don't remember the original scale so we could lose precision if we iterate
;; this - could think about making it more numerically stable if that were a
;; use-case.
(defn scale-additive
  [hybrid alpha]
  (assert (pos? alpha) "Only positive scaling is correct, currently.") ; Negative scaling means different jumps would have to be installed to stop at hitting zero.
  (let [flow-constraints' (map (fn [[resource additive]]
                                 [resource
                                  (* alpha additive)
                                  [(gensym "scale-jump")]])
                               (:flow-constraints hybrid))
        flowkey (keyword (gensym "scale-flow"))
        term-path [(keyword (gensym "scale-term"))]
        mk-terminate
        ,(fn [instants-constraints]
           (fn term-fn [state]
             #_(prn "terminating additive " term-path)
             (-> state
                 (reduce' (fn [s [instant [resource additive jump-path]]]
                            #_(prn "deleting key" flowkey "w.r.t" flow-constraints')
                            (-> s
                                (delete-flow-term resource flowkey)
                                (remove-jump (->IsZero? resource) {::instant instant
                                                                   ::transition term-fn})
                                (delete-jump jump-path)))
                          instants-constraints)
                 (set-resource term-path true))))]
    {:init (fn [state & [instant]]
             (p ::scale-additive-init
               (let [instants-constraints (map vector
                                               (fresh-instants instant)
                                               flow-constraints')
                     term-fn (mk-terminate instants-constraints)]
                 (-> (reduce (fn [state [instant [resource additive jump-path]]]
                               (let [state (set-flow-additive state resource flowkey additive)]
                                 (if (neg? additive) ; only stop-on-zero if we're moving downard in that resource.
                                   (add-jump state jump-path instant (->IsZero? resource) term-fn ::scale-additive)
                                   state)))
                             state
                             instants-constraints)
                     (set-resource term-path false)))))
     :flow-constraints flow-constraints'
     :terminated term-path}))

(defn additive-hybrid
  "For scaling only the additive flow constraints - not the jump conditions.

  flow-constraints is a list of [[variable] 4] pairs i.e. resources as vectors.

  These are hard-coded to be \"stop when a resource hits 0\" for illustrative
  purposes, but we can support more fancy jump constraints.

  Right now scale is a static parameter - we could consider supplying scale from
  a Resource too."
  [flow-constraints]
  (scale-additive {:flow-constraints flow-constraints} 1))

;; like sequence-hybrid, this could be optimized by being more specific about
;; the triggering predicates. This approach is more general than we need.
(defn strict-par
  "combines (just additive for now) hybrids in parallel. Strict because this
  combination terminates when ALL composed hybrids terminate."
  [hybrids]
  (let [jump-paths (repeatedly #(vector (keyword (gensym "strict-par-jump-"))))
        term-path [(keyword (gensym "strict-par-term-"))]
        counter-path [(keyword (gensym "strict-par-counter-"))]
        terminate (fn [state]
                    ;; collapse all individual terminated resources
                    #_(prn "Terminating strict-par")
                    (-> state
                        (reduce' (fn [state [h jump-path]]
                                   (-> state
                                       (delete-resource (:terminated h))
                                       (delete-jump jump-path)))
                                 (map vector hybrids jump-paths))
                        (set-resource term-path true)))]
    {:init (if (empty? hybrids)
             ;; Immediate termination for no-branch strict-par.
             (fn [state & [instant]]
               (set-resource state term-path true))
             (fn [state & [instant]]
               (-> (reduce
                    (fn [state [h jump-path instant]]
                      (let [[i1 i2] (fresh-instants instant)]
                        (-> ((:init h) state i1)
                            (add-jump
                             jump-path
                             i2
                             (->Equals? (:terminated h) true)
                             (fn [state]
                               #_(prn "decrementing counter" (get-resource state counter-path))
                               (let [state (update-resource state counter-path dec)]
                                 ;; If "I" terminate, look for termination from all my parallel siblings. This could be a 2-watch situation and optimized in lots of ways. Simple for now.
                                 ;; Remember term resources currently hold raw values - not FlowSums
                                 (if #_(every? (fn [h] (get-val (get-resource state (:terminated h)))) hybrids)
                                     (= 0 (get-resource state counter-path))
                                     (terminate state)
                                     ;; only the last one fired terminates
                                     (delete-jump state jump-path))))
                             ::strict-par))))
                    (-> state
                        (set-resource counter-path (count hybrids)))
                    (map vector hybrids jump-paths (fresh-instants instant)))
                   (set-resource term-path false))))
     :hybrids hybrids
     :terminated term-path}))

(defn timer
  "A countdown timer"
  [delay]
  (let [timer-path [(keyword (gensym "timer-"))]
        jump-path [(keyword (gensym "timer-jump-"))]
        term-path [(keyword (gensym "timer-term-"))]
        done (fn [state]
               #_(prn "timer is done at" (:time state))
               (-> state
                   (delete-resource timer-path)
                   (delete-jump jump-path)
                   (set-resource term-path true)))]
    {:init (fn [state & [instant]]
             (p ::timer-init
               #_(prn "timer init called at" (:time state))
               (-> state
                   (set-flow-additive timer-path :t -1)
                   (set-flow-offset   timer-path delay)
                   (add-jump jump-path instant (->IsZero? timer-path) done ::timer)
                   (set-resource term-path false))))
     :terminated term-path}))

(defn at-time
  "A hybrid that terminates at the given absolute time.
  Throws an exception if the hybrid tries to run when the target time has
  already passed."
  [time]
  (let [term-path [(keyword (gensym "at-time-term-"))]
        jump-path [(keyword (gensym "at-time-jump-"))]
        done (fn [state]
               (-> state
                   (delete-jump jump-path)
                   (set-resource term-path true)))]
    {:init (fn [state & [instant]]
             (when (< time (:time state)) (throw (ex-info "at-time has already passed." {:at-time time :state-time (:time state)})))
             (-> state
                 (add-jump jump-path instant (->TimeEquals? time) done ::at-time)
                 (set-resource term-path false)))
     :terminated term-path}))

(defn impulse-list
  "positive integer offsets from the previous entry.
  [[0,$400],[4,$400]]. Generates a cumulative staircase signal.
  FIXME: this generaes an implicit 1 step time gap between entries, probably not expected
  Could be generalized to any integration of a sequence of impulses

  output is just a keyword - not a vector (so needs to be updated if we do
  nested states)"
  [schedule output-path]
  #_(prn "impulse-list" schedule output-path)
  (let [term  [(keyword (gensym "integrate-gterm-"))]
        timer [(keyword (gensym "integrate-timer-"))]
        sched [(keyword (gensym "integrate-sched-"))]
        jump-path [(keyword (gensym "integrate-jump-"))]
        terminate (fn [state] (-> state
                                  (set-resource term true)
                                  (delete-resource sched)  ;; TODO this manual garbage collection should come for free.
                                  (delete-resource timer)
                                  (delete-jump jump-path)))
        mk-jump-cb (fn mk-jump-cb [instant]
                     (fn [state]
                       (if (seq (get-val (get-resource state sched)))
                         (let [{:keys [+]} (get-arithmetic state)
                               ;; _ (prn "next-step impulse" (get-val (get-resource state sched)))
                               [[delay amount] & next-pay] (get-val (get-resource state sched))
                               jump-path-cb [(keyword (gensym "integrate-jump-"))]
                               state' (-> (if (instance? FlowSum (get-val (get-resource state output-path)))
                                            (update-flow-offset state output-path + amount)
                                            (update-resource    state output-path + amount))
                                          (add-jump jump-path-cb instant (->IsZero? timer) (mk-jump-cb instant) ::impulse-list-transition)
                                          (set-resource sched (vec next-pay)))]
                           (if (seq next-pay)
                             (-> state'
                                 (set-flow-offset timer (ffirst next-pay)))
                             (terminate state')))
                         (terminate state))))]
    {:init (fn [state & [instant]]
             (p ::impulse-list-init
               (-> state
                   (set-resource term false)
                   (set-resource sched schedule)
                   (set-flow-offset   timer (ffirst schedule))
                   (set-flow-additive timer :t -1)
                   (add-jump jump-path instant (->IsZero? timer) (mk-jump-cb instant) ::impulse-list-init))))
     :terminated [term]}))

;; a mode is quite possibly a better name than transition.
;; I was thinking: transition : [mode1 : Mode -> mode2 : Mode] -- these are NOT the arrows of hybrid automata in my mind.
;; (I was thinking of jump-constraints as different, but there is a bit of risk of people conflating them)
;; [[State -> State] -> Hybrid]
(defn transition->hybrid
  "An instantaneous transition that updates the state and terminates"
  [transition]
  (let [term [(keyword (gensym "transition->hybrid-"))]]
    {:init (fn [state & [instant]]
             (-> state
                 (transition)
                 (set-resource term true)))
     :terminated term}))

(defmacro hfn
  "Paren-saving macro.
  Expands (hfn [state] state) to (transition->hybrid (fn [state] state))"
  [state-argvec & body]
  `(transition->hybrid (fn ~state-argvec ~@body)))

(defn timed-transition
  "Hybrid that fires the transition function after `duration` time has passed.

  [Double [State -> State] -> Hybrid]"
  [duration transition]
  (sequence-hybrid (timer duration) (transition->hybrid transition)))

(defn do-at-time
  "Hybrid that does a transition to happen at the specified time.

  [Double [State -> State] -> Hybrid]"
  [time transition]
  (sequence-hybrid (at-time time) (transition->hybrid transition)))

;;;;;;;;;;;;;;;;;;;; Evolving hybrid automata state ;;;;;;;;;;;;;;;;;;;;

(def jump-filtered (atom 0))
(def jump-sorted (atom 0))

(defn jump-timetable
  "sorts the jumps condition by time-til-condition, breaking close ties by the instant label"
  [state]
  #_(let [jumps (count (:jumps state))]
      (when (<= 0 jumps) (prn "Jumps: " jumps " state " #_state)))
  (let [upcoming (->> (for [[jump-label [instant condtn cb]] (:jumps state)]
                        [(time-til-condition state condtn) instant condtn cb jump-label]))
        _ (swap! jump-filtered + (count upcoming))
        have-times (filter (fn [[time _ _ _]] (some? time)) upcoming)
        _ (swap! jump-sorted + (count have-times))
        chronological (sort-by (fn [[time _ _ _]] time) have-times)
        base-time (ffirst chronological)]
    (if (nil? base-time)
      []
      (let [cutoff (+ base-time instant-epsilon)]
        (->> chronological
             (take-while (fn [[time _ _ _]] (< time cutoff)))
             (sort (fn [[_ i1 _ _] [_ i2 _ _]] (lexi-sort i1 i2))))))))

(defnp refresh-flow
  "updates the offset of a flow to the given absolute-time t"
  [flow absolute-t]
  (-> (if (or (empty? (:terms flow)) ;; A constant never needs to be refreshed.
              (= (:last-refresh flow) absolute-t)) ;; already been calculated
        flow
        (let [delta-t (- absolute-t (or (:last-refresh flow) 0))
              ;; {:keys [+ * pow]} (get-arithmetic state) NOTE - doesn't work w/ swappable arith yet
              sumf (sum-flow flow)]
          (-> flow
              (update :offset
                      (fn [offset]
                        (let [ret (if (or (= 0 (:growth sumf)) (nil? (:growth sumf))) ;; TODO re-think how we're dealing with nil as "definitely zero" I think using 0 is ok here.
                                    (+ offset (* delta-t (or (:additive sumf) 0)))
                                    (if (or (= 0 (:additive sumf)) (nil? (:additive sumf)))
                                      (* offset (Math/pow (+ 1 (:growth sumf)) delta-t))
                                      (throw (ex-info "TODO: exponential growth mixed with constant growth"
                                                      {:growth (:growth sumf)
                                                       :flow flow}))))]
                          (when (nil? ret)
                            (throw (ex-info  "NIL offset" {})))
                          ret))))))
      (assoc :last-refresh absolute-t)))

(defn get-offset-recursive
  [elt absolute-t]
  (cond
    (instance? FlowSum elt) (:offset (refresh-flow elt absolute-t))
    (and (map? elt) (not (record? elt)))
    ,(into {} (for [[key subelt] elt] [key (get-offset-recursive subelt absolute-t)]))
    :else elt))

;; We use negative integers for globalish instants. We could instead subdivide
;; once at the toplevel if that turned out to be nicer for some reason.
(def global-clock-instant
  [-1])

(defnp queue-next-timed-jumps
  "When there are no active jumps, find the next timed jump move
  to ::active-jump-conditions (doesn't fire any jumps). There must be queued timed-jumps"
  [state]
  (assert (empty? (::active-jump-conditions state)))
  (assert (not (empty? (::timed-jump-conditions state))))
  (let [[jump-condition fire-time] (peek (::timed-jump-conditions state))
        fire-cutoff (when fire-time (+ fire-time instant-epsilon))]
    (loop [state state]
      (let [[jump-condition fire-time] (peek (::timed-jump-conditions state))]
        (if (and (some? fire-time)
                 (< fire-time fire-cutoff))
          (let [w-var (watched-var jump-condition)
                jumps (get-in state [::jump-conditions w-var jump-condition ::jumps])]
            #_(prn "adding" jumps )
            (recur
             (-> state
                 (assoc :time fire-time)
                 (update ::timed-jump-conditions pop)
                 (assoc-in [::jump-conditions w-var jump-condition ::stage] :active)
                 (assoc-in [::active-jump-conditions jump-condition]
                           (do
                             #_(prn "activating and sorting" (count jumps))
                             (apply avl/sorted-set-by active-lexi-jump-sort jumps))))))
          (do
            #_(prn "done queuing: "  (::timed-jump-conditions state) "->" (::active-jump-conditions state))
            state))))))

(defnp fire-immediate-jumps
  "runs all the active jumps until quiescence. If there are no timed jumps
  waiting after all immediate jumps are fired, sets :steady-state to true."
  [state]
  (loop [state state]
    (if (empty? (::active-jump-conditions state))
      (if (empty? (::timed-jump-conditions state))
        (assoc state :steady-state true)
        state)
      (let [[jump-condition jumps] (peek (::active-jump-conditions state))
            next-jump (first jumps)
            next-jumps (disj jumps next-jump)
            w-var (watched-var jump-condition)]
        #_(prn "firing immediate jumps: " jump-condition jumps)
        (recur (-> (if (empty? next-jumps)
                     (-> state
                         (update-in [::jump-conditions w-var] dissoc jump-condition)
                         (dissoc-in-if-empty [::jump-conditions w-var])
                         (update-in [::active-jump-conditions] dissoc jump-condition))
                     (-> state
                         (assoc-in [::jump-conditions w-var jump-condition ::jumps] next-jumps)
                         (assoc-in [::active-jump-conditions jump-condition] next-jumps)))
                   ((::transition next-jump))))))))

(defnp steady-state
  "Run next-jump until there are no more valid jumps. Not guaranteed to terminate for arbitrary machines."
  [state]
  (loop [state state]
    (let [state (fire-immediate-jumps state)]
      (if (:steady-state state)
        state
        (recur (queue-next-timed-jumps state))))))

(defn run
  "run hybrid for t units of time"
  [state time]
  (let [clock (timer time)
        clock-done? (fn [state] (get-val (get-resource state [(first (:terminated clock))])))]
    (loop [state ((:init clock) state global-clock-instant)]
      (let [state (fire-immediate-jumps state)]
        (if (clock-done? state)
          (update-in state [:flows] dissoc (first (:terminated clock)))
          (recur (queue-next-timed-jumps state)))))))
