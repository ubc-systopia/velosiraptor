;;(set-option :auto_config false)
;;;;(set-option :smt.mbqi false)
;;;;(set-option :smt.delay_units true)
;;
;;;; Function-Def crate::test
;;(set-option :sat.euf true)
;;(set-option :tactic.default_tactic sat)
;;(set-option :smt.ematching false)
;;(set-option :smt.case_split 0)
;;(push)
 (declare-const x~2@0 (_ BitVec 64))
 (declare-const y~4@0 (_ BitVec 64))
 (assert
  true
 )
 ;; bitvector ensures not satisfied
 (declare-const %%location_label%%0 Bool)
 (declare-const %%query%% Bool)
 (assert
  (=>
   %%query%%
   (not (=>
     %%location_label%%0
     (=>
      (bvult y~4@0 #x0000000000000040)
      (= (bvlshr x~2@0 y~4@0) (bvudiv x~2@0 (bvshl #x0000000000000001 y~4@0)))
 )))))
 (get-info :version)
 (assert
  %%query%%
 )
 (set-option :rlimit 600000000)
 (check-sat)
 (set-option :rlimit 0)
 (get-info :reason-unknown)
;;(pop)