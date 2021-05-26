(ns hybrid-expression.resource-supply
  "resource supplies are functions like:
  (rs init) ; anonymously named resource
  (rs init suffix) ; resource with specific name

  Resource supplies will throw an exception if you ask for a name that collides
  with a pre-existing name. To avoid this you you can create namespaces via
  `subdir`, which returns a nested supply:
  (subdir rs)
  (subdir rs suffix)

  This approach is an tlternative to gensyms or raw refs for implementing
  resources. Resource names come via same hierarchical philosophy as friendly
  ids. Internally, names are vectors of indices a la `get-in`, but hopefully
  this remains opaque to clients.")

(def subdir-counter-key (Object.))
(def root-name (Object.))

;;; The only time we turn this off is when we're defining the global root in this
;;; file. Otherwise the `subdir` will complain that our global root conflicts
;;; with the subdir reserved for the global root.
(def ^:dynamic unsafe-to-shadow-global-root true)

;;; Every namespace environment will have a "tmp" subdir reserved for globally
;;; defined resources. This means if you want to do gensym-style "just make me a
;;; fresh identifer" we can support that everywhere.
(def global-root-subdir-name :tmp)

(defn swap-in!
  "mirrors update-in but w/ swap!. Different than (swap! x update-in ...) as it
  returns just the focused value, not the entire new structure held by the
  atom."
  [atom address update-fn]
  (-> (swap! atom update-in address update-fn)
      (get-in address)))

;;; Built these as functions to save an explicit argument for the common use
;;; case (give me a new name) could be more explicitly object-ey if that turned
;;; out ot make sense.
(defn subdir
  "Makes a resource-supply located in a \"subdirectory\" with its own namespace.

  You can subdir into the same namespace twice - you don't get two fresh
  subdirectories sharing the same subdir-name.

  Calling w/o subdir-name guarantees a fresh subdir (or raises an exception if
  we can't provide one)"
  [parent-supply & [requested-subdir-name]]
  (let [suffix-counters (:suffix-counters (meta parent-supply))
        parent-path     (:subdir-path     (meta parent-supply))
        resources (:resources (meta parent-supply))
        subdir-name (if (nil? requested-subdir-name)
                      (swap-in! suffix-counters (concat [:root] parent-path [subdir-counter-key])
                                (fn [cntr] (if (nil? cntr) 0 (inc cntr))))
                      requested-subdir-name)
        subdir-path (if (= root-name subdir-name)
                      []
                      (conj parent-path subdir-name))]
    (swap-in! resources subdir-path
              (fn [existing]
                (cond
                  (and (some? existing) (nil? requested-subdir-name))
                  ,(throw (ex-info "subdir/resource exists" {:subdir-path subdir-path}))
                  (= existing :resource)
                  ,(throw (ex-info "Resource name conflicts with subdir name" {:subdir-path subdir-path}))
                  (and unsafe-to-shadow-global-root
                       (= subdir-path [global-root-subdir-name]))
                  ,(throw (ex-info "Global subdir conflicts with subdir name" {:subdir-path subdir-path}))
                  (nil? existing)
                  ,{}
                  :else existing)))
    (->
     (fn
       ([init] (let [suffix (swap-in! suffix-counters (concat [:root] subdir-path [subdir-counter-key])
                                      (fn [cntr] (if (nil? cntr) 0 (inc cntr))))
                     resource (-> (conj subdir-path suffix)
                                  (with-meta {:init-val init}))]
                 (when (get-in @resources resource) ; could happen if someone picks 0 as a name and then tries to generate a fresh incrementing id etc.
                   (throw (ex-info "Resource name collision!" {:resource resource})))
                 (swap! resources assoc-in resource :resource)
                 resource))
       ([init suffix] (let [resource (-> (conj subdir-path suffix)
                                         (with-meta {:init-val init}))]
                        (when (get-in @resources resource)
                          #_(throw (ex-info "Resource name collision!" {:resource resource})))
                        (swap! resources assoc-in resource :resource)
                        resource)))
     (with-meta (meta parent-supply))
     (vary-meta assoc :subdir-path subdir-path))))

(defn rget
  "finds the resource - throws an exception if it hasn't been declared.
  works on read-only directories (but is unecessary, as this has the same
  semantics as direct invocation)"
  [dir suffix]
  (let [dir (or (:writeable-dir (meta dir)) dir)
        res (get-in @(:resources (meta dir)) (concat (:subdir-path (meta dir)) [suffix]) ::not-found)]
    (cond
      (= ::not-found res)
      ,(throw (ex-info (str "Resource " (vec (concat (:subdir-path (meta dir)) [suffix])) " not found.") {:dir dir :suffix suffix}))
      (= :resource res)
      ,(vec (concat (:subdir-path (meta dir)) [suffix]))
      :else (throw (ex-info (str "Not a resource: " (vec (concat (:subdir-path (meta dir)) [suffix]))) {:dir dir :suffix suffix})))))

(defn rnew
  "creates a new resource under the given directory.
  Works with 'read-only' dirs as well as regular dirs."
  [dir init suffix]
  (let [dir (or (:writeable-dir (meta dir)) dir)]
    (dir init suffix)))

;;; this would be slicker if this was the default mode of directories I think. (this allows us to use that syntax - we can see if we like it)
(defn read-only
  "makes the dir rget the names (i.e. invocation no longer creates new resources
  but rather fetches existing resources)."
  [dir]
  (with-meta
    (fn [resource] (rget dir resource))
    {:writeable-dir dir}))

(defn ls-resources
  "lists all resources in a directory. (doesn't list subdirectories)
  works on writable or read-only directories"
  [dir]
  (let [dir (or (:writeable-dir (meta dir)) dir)]
    (let [contains (get-in @(:resources (meta dir)) (:subdir-path (meta dir)))]
      (for [[k v] contains :when (= :resource v)]
        (vec (concat (:subdir-path (meta dir)) [k]))))))

(defn ls-subdirs
  "lists all subdirectories in a directory. (doesn't list resources) currently
  you can't ls the global root.  works on writable or read-only
  directories. (and returns read-only subdirectories if passed a read-only
  subdir)"
  [dir]
  (let [[dir read-only?] (if-let [wd (:writeable-dir (meta dir))]
                           [wd true]
                           [dir false])]
    (let [contains (get-in @(:resources (meta dir)) (:subdir-path (meta dir)))]
      (for [[k v] contains :when (map? v)]
        (if read-only?
          (read-only (subdir dir k))
          (subdir dir k))))))

(defn new-root
  "Creates a new resource naming environment. All unique suffixes
  are set to 0."
  []
  (let [root-id (Object.) ; Just make sure folks aren't accidentally mix-n-matching different roots.
        suffix-counters (atom {:root {}})
        resources (atom {global-root-subdir-name {}})]
    (subdir (with-meta () {:root-id root-id
                           :suffix-counters suffix-counters
                           :subdir-path []
                           :resources resources})
            root-name)))

(defn fork-root
  "creates a new namespace from the root of dir. Shares everything from the old
  namespace (but changes to this one won't merge back to the parent.)
  (returns the new namespace root - not the equivalent subdirectory in the new
  namespace.)"
  [dir]
  (let [root-id (Object.) ; Just make sure folks aren't accidentally mix-n-matching different roots.
        suffix-counters (atom @(:suffix-counters (meta dir)))
        resources (atom @(:resources (meta dir)))]
    (subdir (with-meta () {:root-id root-id
                           :suffix-counters suffix-counters
                           :subdir-path []
                           :resources resources})
            root-name)))

(def global-root
  "A global namespace anyone can write to."
  (let [nr (new-root)]
    (binding [unsafe-to-shadow-global-root false]
      (subdir nr global-root-subdir-name))))

(defn subdir?
  [dir]
  (let [let [dir (or (:writeable-dir (meta dir)) dir)]]
    (and (fn? dir)
         (:subdir-path (meta dir)))))

(defn subdir-path
  [dir]
  (let [dir (or (:writeable-dir (meta dir)) dir)]
    (:subdir-path (meta dir))))
