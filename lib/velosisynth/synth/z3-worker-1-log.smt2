

(reset)


(set-option :produce-unsat-cores true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Type Definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sort Num () (_ BitVec 64))
(define-sort Addr_t () (_ BitVec 64))
(define-sort VAddr_t () (_ BitVec 64))
(define-sort PAddr_t () (_ BitVec 64))
(define-sort Size_t () (_ BitVec 64))
(define-sort Flags_t () (_ BitVec 64))
;; Type constraints Addr_t
(define-fun Addr_t.assms ((v Addr_t)) Bool
  true
)

;; Type constraints VAddr_t
(define-fun VAddr_t.assms ((v VAddr_t)) Bool
  (and 
    (bvuge 
      v
      #x0000000000000000
    )
    (bvule 
      v
      #x0000000000000fff
    )
  )
)

;; Type constraints PAddr_t
(define-fun PAddr_t.assms ((v PAddr_t)) Bool
  (and 
    (bvuge 
      v
      #x0000000000000000
    )
    (bvule 
      v
      #x00000000ffffffff
    )
  )
)

;; Type constraints Flags_t
(define-fun Flags_t.assms ((v Flags_t)) Bool
  true
)

;; Type constraints Size_t
(define-fun Size_t.assms ((v Size_t)) Bool
  (and 
    (bvuge 
      v
      #x0000000000000000
    )
    (bvule 
      v
      #x0000000000001000
    )
  )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Constants for unit X86PageTableEntry
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun PAGE_SIZE () Num
  #x0000000000001000
)

(define-fun PAGE_SIZE_LARGE () Num
  #x0000000000200000
)

; flags for unit X86PageTableEntry (SrcLoc { context: Some("../../examples/x86_pt.vrs"), line: 47, column: 5 }
(declare-fun Flags.writable.get! (Flags_t) Num)

(assert 
  (forall (
    (flgs@ Flags_t)) 
    (! 
      (= 
        (Flags.writable.get! 
          flgs@
        )
        (bvand 
          (bvlshr 
            flgs@
            #x0000000000000000
          )
          #x0000000000000001
        )
      ):pattern (Flags.writable.get! flgs@))

  )
)
(declare-fun Flags.readable.get! (Flags_t) Num)

(assert 
  (forall (
    (flgs@ Flags_t)) 
    (! 
      (= 
        (Flags.readable.get! 
          flgs@
        )
        (bvand 
          (bvlshr 
            flgs@
            #x0000000000000001
          )
          #x0000000000000001
        )
      ):pattern (Flags.readable.get! flgs@))

  )
)
(declare-fun Flags.devicemem.get! (Flags_t) Num)

(assert 
  (forall (
    (flgs@ Flags_t)) 
    (! 
      (= 
        (Flags.devicemem.get! 
          flgs@
        )
        (bvand 
          (bvlshr 
            flgs@
            #x0000000000000002
          )
          #x0000000000000001
        )
      ):pattern (Flags.devicemem.get! flgs@))

  )
)
(declare-fun Flags.usermode.get! (Flags_t) Num)

(assert 
  (forall (
    (flgs@ Flags_t)) 
    (! 
      (= 
        (Flags.usermode.get! 
          flgs@
        )
        (bvand 
          (bvlshr 
            flgs@
            #x0000000000000003
          )
          #x0000000000000001
        )
      ):pattern (Flags.usermode.get! flgs@))

  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; State Fields
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Type for the StateField.pte_t
(define-sort StateField.pte_t () Num)
; Accessors for StateField.pte.state.pte.present
(declare-fun StateField.pte.present.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.present.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000000
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.present.get! x@))

  )
)
(declare-fun StateField.pte.present.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.present.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffffe
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000000
          )
        )
      ):pattern (StateField.pte.present.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.writable
(declare-fun StateField.pte.writable.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.writable.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000001
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.writable.get! x@))

  )
)
(declare-fun StateField.pte.writable.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.writable.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffffd
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000001
          )
        )
      ):pattern (StateField.pte.writable.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.usermode
(declare-fun StateField.pte.usermode.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.usermode.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000002
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.usermode.get! x@))

  )
)
(declare-fun StateField.pte.usermode.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.usermode.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffffb
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000002
          )
        )
      ):pattern (StateField.pte.usermode.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.writethrough
(declare-fun StateField.pte.writethrough.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.writethrough.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000003
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.writethrough.get! x@))

  )
)
(declare-fun StateField.pte.writethrough.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.writethrough.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffff7
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000003
          )
        )
      ):pattern (StateField.pte.writethrough.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.nocache
(declare-fun StateField.pte.nocache.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.nocache.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000004
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.nocache.get! x@))

  )
)
(declare-fun StateField.pte.nocache.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.nocache.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffffffffffef
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000004
          )
        )
      ):pattern (StateField.pte.nocache.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.accessed
(declare-fun StateField.pte.accessed.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.accessed.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000005
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.accessed.get! x@))

  )
)
(declare-fun StateField.pte.accessed.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.accessed.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffffffffffdf
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000005
          )
        )
      ):pattern (StateField.pte.accessed.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.dirty
(declare-fun StateField.pte.dirty.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.dirty.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000006
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.dirty.get! x@))

  )
)
(declare-fun StateField.pte.dirty.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.dirty.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffffffffffbf
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000006
          )
        )
      ):pattern (StateField.pte.dirty.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.pat
(declare-fun StateField.pte.pat.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.pat.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000007
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.pat.get! x@))

  )
)
(declare-fun StateField.pte.pat.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.pat.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffffffffff7f
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000007
          )
        )
      ):pattern (StateField.pte.pat.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.global
(declare-fun StateField.pte.global.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.global.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000008
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.global.get! x@))

  )
)
(declare-fun StateField.pte.global.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.global.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffeff
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000008
          )
        )
      ):pattern (StateField.pte.global.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.ignored
(declare-fun StateField.pte.ignored.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.ignored.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000009
          )
          #x0000000000000007
        )
      ):pattern (StateField.pte.ignored.get! x@))

  )
)
(declare-fun StateField.pte.ignored.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.ignored.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffff1ff
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000007
            )
            #x0000000000000009
          )
        )
      ):pattern (StateField.pte.ignored.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.base
(declare-fun StateField.pte.base.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.base.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x000000000000000c
          )
          #x00000000000fffff
        )
      ):pattern (StateField.pte.base.get! x@))

  )
)
(declare-fun StateField.pte.base.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.base.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffff00000fff
          )
          (bvshl 
            (bvand 
              v@
              #x00000000000fffff
            )
            #x000000000000000c
          )
        )
      ):pattern (StateField.pte.base.set! x@ v@))

  )
)
; Type for the StateField.cr4_t
(define-sort StateField.cr4_t () Num)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; State
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; State Definition, ../../examples/x86_pt.vrs:72:13
(declare-datatypes ((State_t 0)) (
  ((State (State.pte StateField.pte_t) (State.cr4 StateField.cr4_t)))))
(define-fun State.pte.get! ((s@ State_t)) StateField.pte_t
  (State.pte 
    s@
  )
)

(define-fun State.cr4.get! ((s@ State_t)) StateField.cr4_t
  (State.cr4 
    s@
  )
)

(define-fun State.pte.set! ((s@ State_t) (v@ StateField.pte_t)) State_t
  (State 
    v@
    (State.cr4.get! 
      s@
    )
  )
)

(define-fun State.cr4.set! ((s@ State_t) (v@ StateField.cr4_t)) State_t
  (State 
    (State.pte.get! 
      s@
    )
    v@
  )
)

(define-fun State.pte.present.get! ((st State_t)) Num
  (StateField.pte.present.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.present.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.present.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.writable.get! ((st State_t)) Num
  (StateField.pte.writable.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.writable.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.writable.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.usermode.get! ((st State_t)) Num
  (StateField.pte.usermode.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.usermode.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.usermode.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.writethrough.get! ((st State_t)) Num
  (StateField.pte.writethrough.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.writethrough.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.writethrough.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.nocache.get! ((st State_t)) Num
  (StateField.pte.nocache.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.nocache.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.nocache.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.accessed.get! ((st State_t)) Num
  (StateField.pte.accessed.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.accessed.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.accessed.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.dirty.get! ((st State_t)) Num
  (StateField.pte.dirty.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.dirty.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.dirty.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.pat.get! ((st State_t)) Num
  (StateField.pte.pat.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.pat.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.pat.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.global.get! ((st State_t)) Num
  (StateField.pte.global.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.global.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.global.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.ignored.get! ((st State_t)) Num
  (StateField.pte.ignored.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.ignored.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.ignored.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.base.get! ((st State_t)) Num
  (StateField.pte.base.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.base.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.base.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Interface Fields
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Type for the IFaceField.pte_t
(define-sort IFaceField.pte_t () Num)
; Accessors for IFaceField.pte.interface.pte.present
(declare-fun IFaceField.pte.present.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.present.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000000
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.present.get! x@))

  )
)
(declare-fun IFaceField.pte.present.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.present.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffffe
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000000
          )
        )
      ):pattern (IFaceField.pte.present.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.writable
(declare-fun IFaceField.pte.writable.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.writable.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000001
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.writable.get! x@))

  )
)
(declare-fun IFaceField.pte.writable.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.writable.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffffd
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000001
          )
        )
      ):pattern (IFaceField.pte.writable.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.usermode
(declare-fun IFaceField.pte.usermode.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.usermode.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000002
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.usermode.get! x@))

  )
)
(declare-fun IFaceField.pte.usermode.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.usermode.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffffb
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000002
          )
        )
      ):pattern (IFaceField.pte.usermode.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.writethrough
(declare-fun IFaceField.pte.writethrough.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.writethrough.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000003
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.writethrough.get! x@))

  )
)
(declare-fun IFaceField.pte.writethrough.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.writethrough.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffff7
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000003
          )
        )
      ):pattern (IFaceField.pte.writethrough.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.nocache
(declare-fun IFaceField.pte.nocache.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.nocache.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000004
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.nocache.get! x@))

  )
)
(declare-fun IFaceField.pte.nocache.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.nocache.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffffffffffef
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000004
          )
        )
      ):pattern (IFaceField.pte.nocache.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.accessed
(declare-fun IFaceField.pte.accessed.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.accessed.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000005
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.accessed.get! x@))

  )
)
(declare-fun IFaceField.pte.accessed.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.accessed.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffffffffffdf
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000005
          )
        )
      ):pattern (IFaceField.pte.accessed.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.dirty
(declare-fun IFaceField.pte.dirty.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.dirty.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000006
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.dirty.get! x@))

  )
)
(declare-fun IFaceField.pte.dirty.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.dirty.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffffffffffbf
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000006
          )
        )
      ):pattern (IFaceField.pte.dirty.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.pat
(declare-fun IFaceField.pte.pat.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.pat.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000007
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.pat.get! x@))

  )
)
(declare-fun IFaceField.pte.pat.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.pat.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffffffffff7f
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000007
          )
        )
      ):pattern (IFaceField.pte.pat.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.global
(declare-fun IFaceField.pte.global.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.global.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000008
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.global.get! x@))

  )
)
(declare-fun IFaceField.pte.global.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.global.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffeff
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000008
          )
        )
      ):pattern (IFaceField.pte.global.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.ignored
(declare-fun IFaceField.pte.ignored.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.ignored.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000009
          )
          #x0000000000000007
        )
      ):pattern (IFaceField.pte.ignored.get! x@))

  )
)
(declare-fun IFaceField.pte.ignored.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.ignored.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffff1ff
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000007
            )
            #x0000000000000009
          )
        )
      ):pattern (IFaceField.pte.ignored.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.base
(declare-fun IFaceField.pte.base.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.base.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x000000000000000c
          )
          #x00000000000fffff
        )
      ):pattern (IFaceField.pte.base.get! x@))

  )
)
(declare-fun IFaceField.pte.base.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.base.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffff00000fff
          )
          (bvshl 
            (bvand 
              v@
              #x00000000000fffff
            )
            #x000000000000000c
          )
        )
      ):pattern (IFaceField.pte.base.set! x@ v@))

  )
)
; Type for the IFaceField.cr4_t
(define-sort IFaceField.cr4_t () Num)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Interface
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Interface Definition, ../../examples/x86_pt.vrs:94:17
(declare-datatypes ((IFace_t 0)) (
  ((IFace (IFace.pte IFaceField.pte_t) (IFace.cr4 IFaceField.cr4_t)))))
(define-fun IFace.pte.get! ((s@ IFace_t)) IFaceField.pte_t
  (IFace.pte 
    s@
  )
)

(define-fun IFace.cr4.get! ((s@ IFace_t)) IFaceField.cr4_t
  (IFace.cr4 
    s@
  )
)

(define-fun IFace.pte.set! ((s@ IFace_t) (v@ IFaceField.pte_t)) IFace_t
  (IFace 
    v@
    (IFace.cr4.get! 
      s@
    )
  )
)

(define-fun IFace.cr4.set! ((s@ IFace_t) (v@ IFaceField.cr4_t)) IFace_t
  (IFace 
    (IFace.pte.get! 
      s@
    )
    v@
  )
)

(define-fun IFace.pte.present.get! ((st IFace_t)) Num
  (IFaceField.pte.present.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.present.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.present.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.writable.get! ((st IFace_t)) Num
  (IFaceField.pte.writable.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.writable.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.writable.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.usermode.get! ((st IFace_t)) Num
  (IFaceField.pte.usermode.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.usermode.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.usermode.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.writethrough.get! ((st IFace_t)) Num
  (IFaceField.pte.writethrough.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.writethrough.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.writethrough.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.nocache.get! ((st IFace_t)) Num
  (IFaceField.pte.nocache.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.nocache.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.nocache.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.accessed.get! ((st IFace_t)) Num
  (IFaceField.pte.accessed.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.accessed.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.accessed.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.dirty.get! ((st IFace_t)) Num
  (IFaceField.pte.dirty.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.dirty.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.dirty.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.pat.get! ((st IFace_t)) Num
  (IFaceField.pte.pat.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.pat.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.pat.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.global.get! ((st IFace_t)) Num
  (IFaceField.pte.global.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.global.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.global.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.ignored.get! ((st IFace_t)) Num
  (IFaceField.pte.ignored.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.ignored.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.ignored.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.base.get! ((st IFace_t)) Num
  (IFaceField.pte.base.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.base.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.base.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Model Definition
(declare-datatypes ((Model_t 0)) (
  ((Model (Model.State State_t) (Model.IFace IFace_t)))))
(define-fun Model.State.get! ((s@ Model_t)) State_t
  (Model.State 
    s@
  )
)

(define-fun Model.IFace.get! ((s@ Model_t)) IFace_t
  (Model.IFace 
    s@
  )
)

(define-fun Model.State.set! ((s@ Model_t) (v@ State_t)) Model_t
  (Model 
    v@
    (Model.IFace.get! 
      s@
    )
  )
)

(define-fun Model.IFace.set! ((s@ Model_t) (v@ IFace_t)) Model_t
  (Model 
    (Model.State.get! 
      s@
    )
    v@
  )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Model State Accessors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; state field: state.pte
;----------------------------------------------------------------------------------------------------

(define-fun Model.State.pte.get! ((st Model_t)) StateField.pte_t
  (State.pte.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.set! ((st Model_t) (val StateField.pte_t)) Model_t
  (Model.State.set! 
    st
    (State.pte.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.present.get! ((st Model_t)) Num
  (State.pte.present.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.present.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.present.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.writable.get! ((st Model_t)) Num
  (State.pte.writable.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.writable.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.writable.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.usermode.get! ((st Model_t)) Num
  (State.pte.usermode.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.usermode.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.usermode.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.writethrough.get! ((st Model_t)) Num
  (State.pte.writethrough.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.writethrough.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.writethrough.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.nocache.get! ((st Model_t)) Num
  (State.pte.nocache.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.nocache.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.nocache.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.accessed.get! ((st Model_t)) Num
  (State.pte.accessed.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.accessed.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.accessed.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.dirty.get! ((st Model_t)) Num
  (State.pte.dirty.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.dirty.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.dirty.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.pat.get! ((st Model_t)) Num
  (State.pte.pat.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.pat.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.pat.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.global.get! ((st Model_t)) Num
  (State.pte.global.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.global.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.global.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.ignored.get! ((st Model_t)) Num
  (State.pte.ignored.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.ignored.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.ignored.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.base.get! ((st Model_t)) Num
  (State.pte.base.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.base.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.base.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)


; state field: state.cr4
;----------------------------------------------------------------------------------------------------

(define-fun Model.State.cr4.get! ((st Model_t)) StateField.cr4_t
  (State.cr4.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.cr4.set! ((st Model_t) (val StateField.cr4_t)) Model_t
  (Model.State.set! 
    st
    (State.cr4.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Model Interface Accessors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; interface field: interface.pte
;----------------------------------------------------------------------------------------------------

(define-fun Model.IFace.pte.get! ((st Model_t)) IFaceField.pte_t
  (IFace.pte.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.set! ((st Model_t) (val IFaceField.pte_t)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.present.get! ((st Model_t)) Num
  (IFace.pte.present.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.present.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.present.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.writable.get! ((st Model_t)) Num
  (IFace.pte.writable.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.writable.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.writable.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.usermode.get! ((st Model_t)) Num
  (IFace.pte.usermode.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.usermode.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.usermode.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.writethrough.get! ((st Model_t)) Num
  (IFace.pte.writethrough.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.writethrough.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.writethrough.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.nocache.get! ((st Model_t)) Num
  (IFace.pte.nocache.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.nocache.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.nocache.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.accessed.get! ((st Model_t)) Num
  (IFace.pte.accessed.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.accessed.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.accessed.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.dirty.get! ((st Model_t)) Num
  (IFace.pte.dirty.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.dirty.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.dirty.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.pat.get! ((st Model_t)) Num
  (IFace.pte.pat.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.pat.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.pat.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.global.get! ((st Model_t)) Num
  (IFace.pte.global.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.global.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.global.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.ignored.get! ((st Model_t)) Num
  (IFace.pte.ignored.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.ignored.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.ignored.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.base.get! ((st Model_t)) Num
  (IFace.pte.base.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.base.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.base.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)


; interface field: interface.cr4
;----------------------------------------------------------------------------------------------------

(define-fun Model.IFace.cr4.get! ((st Model_t)) IFaceField.cr4_t
  (IFace.cr4.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.cr4.set! ((st Model_t) (val IFaceField.cr4_t)) Model_t
  (Model.IFace.set! 
    st
    (IFace.cr4.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Actions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; interface field: interface.pte
;----------------------------------------------------------------------------------------------------

;; performs the write actions of interface.pte
(define-fun Model.IFace.pte.writeaction! ((st Model_t)) Model_t
  (let (
    (st_1 (Model.State.pte.set! 
      st
      (Model.IFace.pte.get! 
        st
      )
    ))
  ) st_1)
)

;; performs the write actions of interface.pte
(define-fun Model.IFace.pte.readaction! ((st Model_t)) Model_t
  (let (
    (st_1 (Model.IFace.pte.set! 
      st
      (Model.State.pte.get! 
        st
      )
    ))
  ) st_1)
)


; interface field: interface.cr4
;----------------------------------------------------------------------------------------------------

;; performs the write actions of interface.cr4
(define-fun Model.IFace.cr4.writeaction! ((st Model_t)) Model_t
  st
)

;; performs the write actions of interface.cr4
(define-fun Model.IFace.cr4.readaction! ((st Model_t)) Model_t
  st
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Methods
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Function: valid, ../../examples/x86_pt.vrs:121:5
(define-fun valid ((st Model_t)) Bool
  (= 
    (Model.State.pte.present.get! 
      st
    )
    #x0000000000000001
  )
)

;; Function Preconditions: valid, ../../examples/x86_pt.vrs:121:5
(define-fun valid.pre ((st!0 Model_t)) Bool
  true
)

;; Function Assumptions: valid, ../../examples/x86_pt.vrs:121:5
(define-fun valid.assms ((st!0 Model_t)) Bool
  true
)

;; Function: matchflags, ../../examples/x86_pt.vrs:127:5
(define-fun matchflags ((st Model_t) (flgs Flags_t)) Bool
  (and 
    (= 
      (Model.State.pte.writable.get! 
        st
      )
      (Flags.writable.get! 
        flgs
      )
    )
    (= 
      (Model.State.pte.global.get! 
        st
      )
      #x0000000000000000
    )
  )
)

;; Function Body part 0: matchflags, ../../examples/x86_pt.vrs:127:5
(define-fun matchflags.part.0 ((st!0 Model_t) (flgs Flags_t)) Bool
  (= 
    (Model.State.pte.writable.get! 
      st!0
    )
    (Flags.writable.get! 
      flgs
    )
  )
)

;; Function Body part 1: matchflags, ../../examples/x86_pt.vrs:127:5
(define-fun matchflags.part.1 ((st!0 Model_t) (flgs Flags_t)) Bool
  (= 
    (Model.State.pte.global.get! 
      st!0
    )
    #x0000000000000000
  )
)

;; Checking the matchflags function result
(define-fun matchflags.map.result.0 ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  (matchflags.part.0 
    st!0
    flgs
  )
)

;; Checking the matchflags function result
(define-fun matchflags.map.result.1 ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  (matchflags.part.1 
    st!0
    flgs
  )
)

;; Checking the matchflags function result
(define-fun matchflags.map.result ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  (matchflags 
    st!0
    flgs
  )
)

;; Checking the matchflags function result
(define-fun matchflags.protect.result.0 ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  (matchflags.part.0 
    st!0
    flgs
  )
)

;; Checking the matchflags function result
(define-fun matchflags.protect.result.1 ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  (matchflags.part.1 
    st!0
    flgs
  )
)

;; Checking the matchflags function result
(define-fun matchflags.protect.result ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  (matchflags 
    st!0
    flgs
  )
)

;; Function Preconditions part 0: matchflags, ../../examples/x86_pt.vrs:127:5
(define-fun matchflags.pre.0 ((st!0 Model_t) (flgs Flags_t)) Bool
  (= 
    (Model.State.pte.present.get! 
      st!0
    )
    #x0000000000000001
  )
)

;; Function Preconditions: matchflags, ../../examples/x86_pt.vrs:127:5
(define-fun matchflags.pre ((st!0 Model_t) (flgs Flags_t)) Bool
  (and 
    true
    (= 
      (Model.State.pte.present.get! 
        st!0
      )
      #x0000000000000001
    )
  )
)

;; Function Assumptions: matchflags, ../../examples/x86_pt.vrs:127:5
(define-fun matchflags.assms ((st!0 Model_t) (flgs Flags_t)) Bool
  (and 
    (and 
      true
      (Flags_t.assms 
        flgs
      )
    )
    (valid 
      st!0
    )
  )
)

;; Function: translate, ../../examples/x86_pt.vrs:140:5
(define-fun translate ((st Model_t) (va VAddr_t)) PAddr_t
  (bvadd 
    va
    (bvshl 
      (Model.State.pte.base.get! 
        st
      )
      #x000000000000000c
    )
  )
)

;; Checking the translate function result
(define-fun translate.map.result ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  (forall (
    (i!0 Size_t)) 
    (=> 
      (and 
        (bvuge 
          #x0000000000000000
          i!0
        )
        (bvult 
          i!0
          sz
        )
      )
      (= 
        (translate 
          st!0
          (bvadd 
            va
            i!0
          )
        )
        (bvadd 
          pa
          i!0
        )
      )
    )
  )
)

;; Checking the translate function result
(define-fun translate.protect.result ((st!0 Model_t) (st!1 Model_t) (va VAddr_t) (sz Size_t)) Bool
  (forall (
    (i!0 Size_t)) 
    (=> 
      (and 
        (bvuge 
          #x0000000000000000
          i!0
        )
        (bvult 
          i!0
          sz
        )
      )
      (= 
        (translate 
          st!0
          (bvadd 
            va
            i!0
          )
        )
        (translate 
          st!1
          (bvadd 
            va
            i!0
          )
        )
      )
    )
  )
)

;; Function Preconditions part 0: translate, ../../examples/x86_pt.vrs:140:5
(define-fun translate.pre.0 ((st!0 Model_t) (va VAddr_t)) Bool
  (= 
    (Model.State.pte.present.get! 
      st!0
    )
    #x0000000000000001
  )
)

;; Function Preconditions: translate, ../../examples/x86_pt.vrs:140:5
(define-fun translate.pre ((st!0 Model_t) (va VAddr_t)) Bool
  (and 
    true
    (= 
      (Model.State.pte.present.get! 
        st!0
      )
      #x0000000000000001
    )
  )
)

;; Function Assumptions: translate, ../../examples/x86_pt.vrs:140:5
(define-fun translate.assms ((st!0 Model_t) (va VAddr_t)) Bool
  (and 
    (and 
      true
      (VAddr_t.assms 
        va
      )
    )
    (bvult 
      va
      #x0000000000001000
    )
  )
)

; skipping method unmap, no body defined
;; Function Preconditions: unmap, ../../examples/x86_pt.vrs:148:5
(define-fun unmap.pre ((st!0 Model_t) (va VAddr_t) (sz Size_t)) Bool
  true
)

;; Function Assumptions: unmap, ../../examples/x86_pt.vrs:148:5
(define-fun unmap.assms ((st!0 Model_t) (va VAddr_t) (sz Size_t)) Bool
  (and 
    (and 
      (and 
        (and 
          true
          (VAddr_t.assms 
            va
          )
        )
        (Size_t.assms 
          sz
        )
      )
      (= 
        va
        #x0000000000000000
      )
    )
    (= 
      sz
      #x0000000000001000
    )
  )
)

; skipping method map, no body defined
;; Function Preconditions: map, ../../examples/x86_pt.vrs:154:5
(define-fun map.pre ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  true
)

;; Function Assumptions: map, ../../examples/x86_pt.vrs:154:5
(define-fun map.assms ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  (and 
    (and 
      (and 
        (and 
          (and 
            (and 
              (and 
                true
                (VAddr_t.assms 
                  va
                )
              )
              (Size_t.assms 
                sz
              )
            )
            (Flags_t.assms 
              flgs
            )
          )
          (PAddr_t.assms 
            pa
          )
        )
        (= 
          va
          #x0000000000000000
        )
      )
      (= 
        sz
        #x0000000000001000
      )
    )
    (= 
      (bvand 
        pa
        #x0000000000000fff
      )
      #x0000000000000000
    )
  )
)

; skipping method protect, no body defined
;; Function Preconditions: protect, ../../examples/x86_pt.vrs:167:5
(define-fun protect.pre ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t)) Bool
  true
)

;; Function Assumptions: protect, ../../examples/x86_pt.vrs:167:5
(define-fun protect.assms ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t)) Bool
  (and 
    (and 
      (and 
        true
        (VAddr_t.assms 
          va
        )
      )
      (Size_t.assms 
        sz
      )
    )
    (Flags_t.assms 
      flgs
    )
  )
)

; skipping method foo, no body defined
;; Function Preconditions: foo, ../../examples/x86_pt.vrs:171:5
(define-fun foo.pre ((st!0 Model_t) (va VAddr_t)) Bool
  true
)

;; Function Assumptions: foo, ../../examples/x86_pt.vrs:171:5
(define-fun foo.assms ((st!0 Model_t) (va VAddr_t)) Bool
  (and 
    (and 
      (and 
        (and 
          (and 
            (and 
              (and 
                true
                (VAddr_t.assms 
                  va
                )
              )
              (bvult 
                va
                #x0000000000000000
              )
            )
            (bvugt 
              va
              #x0000000000000000
            )
          )
          (bvult 
            va
            #x0000000000000000
          )
        )
        (or 
          (bvugt 
            va
            #x0000000000000000
          )
          (= 
            va
            #x0000000000000000
          )
        )
      )
      (not 
        (= 
          va
          #x0000000000000001
        )
      )
    )
    (not 
      (= 
        va
        #x0000000000000002
      )
    )
  )
)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (valid 
      st
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-1)

)
(assert 
  (! 
    (valid 
      st
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      va
      #x0000000000000000
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      sz
      #x0000000000001000
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      (bvand 
        pa
        #x0000000000000fff
      )
      #x0000000000000000
    ):named fn_2-2)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      va
      #x0000000000000000
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      sz
      #x0000000000001000
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      (bvand 
        pa
        #x0000000000000fff
      )
      #x0000000000000000
    ):named fn_2-2)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      va
      #x0000000000000000
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      sz
      #x0000000000001000
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      (bvand 
        pa
        #x0000000000000fff
      )
      #x0000000000000000
    ):named fn_2-2)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (valid 
      st
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      va
      #x0000000000000000
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (valid 
      st
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      sz
      #x0000000000001000
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (valid 
      st
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      (bvand 
        pa
        #x0000000000000fff
      )
      #x0000000000000000
    ):named fn_2-2)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-0)

)
(assert 
  (! 
    (valid 
      st
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (valid 
      st
    ):named fn_1-1)

)
(assert 
  (! 
    (valid 
      st
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      va
      #x0000000000000000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      va
      #x0000000000000000
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      va
      #x0000000000000000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      sz
      #x0000000000001000
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      va
      #x0000000000000000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      (bvand 
        pa
        #x0000000000000fff
      )
      #x0000000000000000
    ):named fn_2-2)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      sz
      #x0000000000001000
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      sz
      #x0000000000001000
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      sz
      #x0000000000001000
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      (bvand 
        pa
        #x0000000000000fff
      )
      #x0000000000000000
    ):named fn_2-2)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (bvand 
        pa
        #x0000000000000fff
      )
      #x0000000000000000
    ):named fn_1-2)

)
(assert 
  (! 
    (= 
      (bvand 
        pa
        #x0000000000000fff
      )
      #x0000000000000000
    ):named fn_2-2)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (valid 
      st
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-1)

)
(assert 
  (! 
    (valid 
      st
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      va
      #x0000000000000000
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      sz
      #x0000000000001000
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      va
      #x0000000000000000
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      sz
      #x0000000000001000
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      va
      #x0000000000000000
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      sz
      #x0000000000001000
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (valid 
      st
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      va
      #x0000000000000000
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (valid 
      st
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      sz
      #x0000000000001000
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-0)

)
(assert 
  (! 
    (valid 
      st
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (valid 
      st
    ):named fn_1-1)

)
(assert 
  (! 
    (valid 
      st
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      va
      #x0000000000000000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      va
      #x0000000000000000
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      va
      #x0000000000000000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      sz
      #x0000000000001000
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      sz
      #x0000000000001000
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      sz
      #x0000000000001000
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (valid 
      st
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-1)

)
(assert 
  (! 
    (valid 
      st
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-0)

)
(assert 
  (! 
    (valid 
      st
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (valid 
      st
    ):named fn_1-1)

)
(assert 
  (! 
    (valid 
      st
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_2-0)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (bvult 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)


(push)
(declare-const st Model_t)
(declare-const va VAddr_t)
(declare-const sz Size_t)
(declare-const flgs Flags_t)
(declare-const pa PAddr_t)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000001
    ):named fn_2-1)

)
(check-sat)
(get-unsat-core)
(pop)



(reset)


(set-option :produce-unsat-cores true)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Type Definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-sort Num () (_ BitVec 64))
(define-sort Addr_t () (_ BitVec 64))
(define-sort VAddr_t () (_ BitVec 64))
(define-sort PAddr_t () (_ BitVec 64))
(define-sort Size_t () (_ BitVec 64))
(define-sort Flags_t () (_ BitVec 64))
;; Type constraints Addr_t
(define-fun Addr_t.assms ((v Addr_t)) Bool
  true
)

;; Type constraints VAddr_t
(define-fun VAddr_t.assms ((v VAddr_t)) Bool
  (and 
    (bvuge 
      v
      #x0000000000000000
    )
    (bvule 
      v
      #x0000000000000fff
    )
  )
)

;; Type constraints PAddr_t
(define-fun PAddr_t.assms ((v PAddr_t)) Bool
  (and 
    (bvuge 
      v
      #x0000000000000000
    )
    (bvule 
      v
      #x00000000ffffffff
    )
  )
)

;; Type constraints Flags_t
(define-fun Flags_t.assms ((v Flags_t)) Bool
  true
)

;; Type constraints Size_t
(define-fun Size_t.assms ((v Size_t)) Bool
  (and 
    (bvuge 
      v
      #x0000000000000000
    )
    (bvule 
      v
      #x0000000000001000
    )
  )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Constants for unit X86PageTableEntry
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun PAGE_SIZE () Num
  #x0000000000001000
)

(define-fun PAGE_SIZE_LARGE () Num
  #x0000000000200000
)

; flags for unit X86PageTableEntry (SrcLoc { context: Some("../../examples/x86_pt.vrs"), line: 47, column: 5 }
(declare-fun Flags.writable.get! (Flags_t) Num)

(assert 
  (forall (
    (flgs@ Flags_t)) 
    (! 
      (= 
        (Flags.writable.get! 
          flgs@
        )
        (bvand 
          (bvlshr 
            flgs@
            #x0000000000000000
          )
          #x0000000000000001
        )
      ):pattern (Flags.writable.get! flgs@))

  )
)
(declare-fun Flags.readable.get! (Flags_t) Num)

(assert 
  (forall (
    (flgs@ Flags_t)) 
    (! 
      (= 
        (Flags.readable.get! 
          flgs@
        )
        (bvand 
          (bvlshr 
            flgs@
            #x0000000000000001
          )
          #x0000000000000001
        )
      ):pattern (Flags.readable.get! flgs@))

  )
)
(declare-fun Flags.devicemem.get! (Flags_t) Num)

(assert 
  (forall (
    (flgs@ Flags_t)) 
    (! 
      (= 
        (Flags.devicemem.get! 
          flgs@
        )
        (bvand 
          (bvlshr 
            flgs@
            #x0000000000000002
          )
          #x0000000000000001
        )
      ):pattern (Flags.devicemem.get! flgs@))

  )
)
(declare-fun Flags.usermode.get! (Flags_t) Num)

(assert 
  (forall (
    (flgs@ Flags_t)) 
    (! 
      (= 
        (Flags.usermode.get! 
          flgs@
        )
        (bvand 
          (bvlshr 
            flgs@
            #x0000000000000003
          )
          #x0000000000000001
        )
      ):pattern (Flags.usermode.get! flgs@))

  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; State Fields
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Type for the StateField.pte_t
(define-sort StateField.pte_t () Num)
; Accessors for StateField.pte.state.pte.present
(declare-fun StateField.pte.present.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.present.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000000
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.present.get! x@))

  )
)
(declare-fun StateField.pte.present.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.present.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffffe
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000000
          )
        )
      ):pattern (StateField.pte.present.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.writable
(declare-fun StateField.pte.writable.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.writable.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000001
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.writable.get! x@))

  )
)
(declare-fun StateField.pte.writable.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.writable.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffffd
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000001
          )
        )
      ):pattern (StateField.pte.writable.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.usermode
(declare-fun StateField.pte.usermode.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.usermode.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000002
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.usermode.get! x@))

  )
)
(declare-fun StateField.pte.usermode.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.usermode.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffffb
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000002
          )
        )
      ):pattern (StateField.pte.usermode.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.writethrough
(declare-fun StateField.pte.writethrough.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.writethrough.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000003
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.writethrough.get! x@))

  )
)
(declare-fun StateField.pte.writethrough.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.writethrough.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffff7
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000003
          )
        )
      ):pattern (StateField.pte.writethrough.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.nocache
(declare-fun StateField.pte.nocache.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.nocache.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000004
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.nocache.get! x@))

  )
)
(declare-fun StateField.pte.nocache.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.nocache.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffffffffffef
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000004
          )
        )
      ):pattern (StateField.pte.nocache.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.accessed
(declare-fun StateField.pte.accessed.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.accessed.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000005
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.accessed.get! x@))

  )
)
(declare-fun StateField.pte.accessed.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.accessed.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffffffffffdf
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000005
          )
        )
      ):pattern (StateField.pte.accessed.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.dirty
(declare-fun StateField.pte.dirty.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.dirty.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000006
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.dirty.get! x@))

  )
)
(declare-fun StateField.pte.dirty.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.dirty.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffffffffffbf
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000006
          )
        )
      ):pattern (StateField.pte.dirty.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.pat
(declare-fun StateField.pte.pat.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.pat.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000007
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.pat.get! x@))

  )
)
(declare-fun StateField.pte.pat.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.pat.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffffffffff7f
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000007
          )
        )
      ):pattern (StateField.pte.pat.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.global
(declare-fun StateField.pte.global.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.global.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000008
          )
          #x0000000000000001
        )
      ):pattern (StateField.pte.global.get! x@))

  )
)
(declare-fun StateField.pte.global.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.global.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffeff
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000008
          )
        )
      ):pattern (StateField.pte.global.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.ignored
(declare-fun StateField.pte.ignored.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.ignored.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000009
          )
          #x0000000000000007
        )
      ):pattern (StateField.pte.ignored.get! x@))

  )
)
(declare-fun StateField.pte.ignored.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.ignored.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffff1ff
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000007
            )
            #x0000000000000009
          )
        )
      ):pattern (StateField.pte.ignored.set! x@ v@))

  )
)
; Accessors for StateField.pte.state.pte.base
(declare-fun StateField.pte.base.get! (StateField.pte_t) Num)

(assert 
  (forall (
    (x@ StateField.pte_t)) 
    (! 
      (= 
        (StateField.pte.base.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x000000000000000c
          )
          #x00000000000fffff
        )
      ):pattern (StateField.pte.base.get! x@))

  )
)
(declare-fun StateField.pte.base.set! (StateField.pte_t Num) StateField.pte_t)

(assert 
  (forall (
    (x@ StateField.pte_t) (v@ Num)) 
    (! 
      (= 
        (StateField.pte.base.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffff00000fff
          )
          (bvshl 
            (bvand 
              v@
              #x00000000000fffff
            )
            #x000000000000000c
          )
        )
      ):pattern (StateField.pte.base.set! x@ v@))

  )
)
; Type for the StateField.cr4_t
(define-sort StateField.cr4_t () Num)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; State
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; State Definition, ../../examples/x86_pt.vrs:72:13
(declare-datatypes ((State_t 0)) (
  ((State (State.pte StateField.pte_t) (State.cr4 StateField.cr4_t)))))
(define-fun State.pte.get! ((s@ State_t)) StateField.pte_t
  (State.pte 
    s@
  )
)

(define-fun State.cr4.get! ((s@ State_t)) StateField.cr4_t
  (State.cr4 
    s@
  )
)

(define-fun State.pte.set! ((s@ State_t) (v@ StateField.pte_t)) State_t
  (State 
    v@
    (State.cr4.get! 
      s@
    )
  )
)

(define-fun State.cr4.set! ((s@ State_t) (v@ StateField.cr4_t)) State_t
  (State 
    (State.pte.get! 
      s@
    )
    v@
  )
)

(define-fun State.pte.present.get! ((st State_t)) Num
  (StateField.pte.present.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.present.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.present.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.writable.get! ((st State_t)) Num
  (StateField.pte.writable.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.writable.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.writable.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.usermode.get! ((st State_t)) Num
  (StateField.pte.usermode.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.usermode.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.usermode.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.writethrough.get! ((st State_t)) Num
  (StateField.pte.writethrough.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.writethrough.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.writethrough.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.nocache.get! ((st State_t)) Num
  (StateField.pte.nocache.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.nocache.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.nocache.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.accessed.get! ((st State_t)) Num
  (StateField.pte.accessed.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.accessed.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.accessed.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.dirty.get! ((st State_t)) Num
  (StateField.pte.dirty.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.dirty.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.dirty.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.pat.get! ((st State_t)) Num
  (StateField.pte.pat.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.pat.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.pat.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.global.get! ((st State_t)) Num
  (StateField.pte.global.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.global.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.global.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.ignored.get! ((st State_t)) Num
  (StateField.pte.ignored.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.ignored.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.ignored.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun State.pte.base.get! ((st State_t)) Num
  (StateField.pte.base.get! 
    (State.pte.get! 
      st
    )
  )
)

(define-fun State.pte.base.set! ((st State_t) (val Num)) State_t
  (State.pte.set! 
    st
    (StateField.pte.base.set! 
      (State.pte.get! 
        st
      )
      val
    )
  )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Interface Fields
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Type for the IFaceField.pte_t
(define-sort IFaceField.pte_t () Num)
; Accessors for IFaceField.pte.interface.pte.present
(declare-fun IFaceField.pte.present.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.present.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000000
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.present.get! x@))

  )
)
(declare-fun IFaceField.pte.present.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.present.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffffe
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000000
          )
        )
      ):pattern (IFaceField.pte.present.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.writable
(declare-fun IFaceField.pte.writable.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.writable.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000001
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.writable.get! x@))

  )
)
(declare-fun IFaceField.pte.writable.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.writable.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffffd
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000001
          )
        )
      ):pattern (IFaceField.pte.writable.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.usermode
(declare-fun IFaceField.pte.usermode.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.usermode.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000002
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.usermode.get! x@))

  )
)
(declare-fun IFaceField.pte.usermode.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.usermode.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffffb
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000002
          )
        )
      ):pattern (IFaceField.pte.usermode.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.writethrough
(declare-fun IFaceField.pte.writethrough.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.writethrough.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000003
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.writethrough.get! x@))

  )
)
(declare-fun IFaceField.pte.writethrough.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.writethrough.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffff7
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000003
          )
        )
      ):pattern (IFaceField.pte.writethrough.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.nocache
(declare-fun IFaceField.pte.nocache.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.nocache.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000004
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.nocache.get! x@))

  )
)
(declare-fun IFaceField.pte.nocache.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.nocache.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffffffffffef
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000004
          )
        )
      ):pattern (IFaceField.pte.nocache.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.accessed
(declare-fun IFaceField.pte.accessed.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.accessed.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000005
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.accessed.get! x@))

  )
)
(declare-fun IFaceField.pte.accessed.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.accessed.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffffffffffdf
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000005
          )
        )
      ):pattern (IFaceField.pte.accessed.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.dirty
(declare-fun IFaceField.pte.dirty.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.dirty.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000006
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.dirty.get! x@))

  )
)
(declare-fun IFaceField.pte.dirty.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.dirty.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffffffffffbf
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000006
          )
        )
      ):pattern (IFaceField.pte.dirty.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.pat
(declare-fun IFaceField.pte.pat.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.pat.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000007
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.pat.get! x@))

  )
)
(declare-fun IFaceField.pte.pat.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.pat.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffffffffff7f
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000007
          )
        )
      ):pattern (IFaceField.pte.pat.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.global
(declare-fun IFaceField.pte.global.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.global.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000008
          )
          #x0000000000000001
        )
      ):pattern (IFaceField.pte.global.get! x@))

  )
)
(declare-fun IFaceField.pte.global.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.global.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffffeff
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000001
            )
            #x0000000000000008
          )
        )
      ):pattern (IFaceField.pte.global.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.ignored
(declare-fun IFaceField.pte.ignored.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.ignored.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x0000000000000009
          )
          #x0000000000000007
        )
      ):pattern (IFaceField.pte.ignored.get! x@))

  )
)
(declare-fun IFaceField.pte.ignored.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.ignored.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xfffffffffffff1ff
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000007
            )
            #x0000000000000009
          )
        )
      ):pattern (IFaceField.pte.ignored.set! x@ v@))

  )
)
; Accessors for IFaceField.pte.interface.pte.base
(declare-fun IFaceField.pte.base.get! (IFaceField.pte_t) Num)

(assert 
  (forall (
    (x@ IFaceField.pte_t)) 
    (! 
      (= 
        (IFaceField.pte.base.get! 
          x@
        )
        (bvand 
          (bvlshr 
            x@
            #x000000000000000c
          )
          #x00000000000fffff
        )
      ):pattern (IFaceField.pte.base.get! x@))

  )
)
(declare-fun IFaceField.pte.base.set! (IFaceField.pte_t Num) IFaceField.pte_t)

(assert 
  (forall (
    (x@ IFaceField.pte_t) (v@ Num)) 
    (! 
      (= 
        (IFaceField.pte.base.set! 
          x@
          v@
        )
        (bvor 
          (bvand 
            x@
            #xffffffff00000fff
          )
          (bvshl 
            (bvand 
              v@
              #x00000000000fffff
            )
            #x000000000000000c
          )
        )
      ):pattern (IFaceField.pte.base.set! x@ v@))

  )
)
; Type for the IFaceField.cr4_t
(define-sort IFaceField.cr4_t () Num)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Interface
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Interface Definition, ../../examples/x86_pt.vrs:94:17
(declare-datatypes ((IFace_t 0)) (
  ((IFace (IFace.pte IFaceField.pte_t) (IFace.cr4 IFaceField.cr4_t)))))
(define-fun IFace.pte.get! ((s@ IFace_t)) IFaceField.pte_t
  (IFace.pte 
    s@
  )
)

(define-fun IFace.cr4.get! ((s@ IFace_t)) IFaceField.cr4_t
  (IFace.cr4 
    s@
  )
)

(define-fun IFace.pte.set! ((s@ IFace_t) (v@ IFaceField.pte_t)) IFace_t
  (IFace 
    v@
    (IFace.cr4.get! 
      s@
    )
  )
)

(define-fun IFace.cr4.set! ((s@ IFace_t) (v@ IFaceField.cr4_t)) IFace_t
  (IFace 
    (IFace.pte.get! 
      s@
    )
    v@
  )
)

(define-fun IFace.pte.present.get! ((st IFace_t)) Num
  (IFaceField.pte.present.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.present.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.present.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.writable.get! ((st IFace_t)) Num
  (IFaceField.pte.writable.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.writable.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.writable.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.usermode.get! ((st IFace_t)) Num
  (IFaceField.pte.usermode.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.usermode.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.usermode.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.writethrough.get! ((st IFace_t)) Num
  (IFaceField.pte.writethrough.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.writethrough.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.writethrough.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.nocache.get! ((st IFace_t)) Num
  (IFaceField.pte.nocache.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.nocache.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.nocache.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.accessed.get! ((st IFace_t)) Num
  (IFaceField.pte.accessed.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.accessed.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.accessed.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.dirty.get! ((st IFace_t)) Num
  (IFaceField.pte.dirty.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.dirty.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.dirty.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.pat.get! ((st IFace_t)) Num
  (IFaceField.pte.pat.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.pat.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.pat.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.global.get! ((st IFace_t)) Num
  (IFaceField.pte.global.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.global.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.global.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.ignored.get! ((st IFace_t)) Num
  (IFaceField.pte.ignored.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.ignored.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.ignored.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)

(define-fun IFace.pte.base.get! ((st IFace_t)) Num
  (IFaceField.pte.base.get! 
    (IFace.pte.get! 
      st
    )
  )
)

(define-fun IFace.pte.base.set! ((st IFace_t) (val Num)) IFace_t
  (IFace.pte.set! 
    st
    (IFaceField.pte.base.set! 
      (IFace.pte.get! 
        st
      )
      val
    )
  )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Model
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Model Definition
(declare-datatypes ((Model_t 0)) (
  ((Model (Model.State State_t) (Model.IFace IFace_t)))))
(define-fun Model.State.get! ((s@ Model_t)) State_t
  (Model.State 
    s@
  )
)

(define-fun Model.IFace.get! ((s@ Model_t)) IFace_t
  (Model.IFace 
    s@
  )
)

(define-fun Model.State.set! ((s@ Model_t) (v@ State_t)) Model_t
  (Model 
    v@
    (Model.IFace.get! 
      s@
    )
  )
)

(define-fun Model.IFace.set! ((s@ Model_t) (v@ IFace_t)) Model_t
  (Model 
    (Model.State.get! 
      s@
    )
    v@
  )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Model State Accessors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; state field: state.pte
;----------------------------------------------------------------------------------------------------

(define-fun Model.State.pte.get! ((st Model_t)) StateField.pte_t
  (State.pte.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.set! ((st Model_t) (val StateField.pte_t)) Model_t
  (Model.State.set! 
    st
    (State.pte.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.present.get! ((st Model_t)) Num
  (State.pte.present.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.present.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.present.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.writable.get! ((st Model_t)) Num
  (State.pte.writable.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.writable.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.writable.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.usermode.get! ((st Model_t)) Num
  (State.pte.usermode.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.usermode.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.usermode.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.writethrough.get! ((st Model_t)) Num
  (State.pte.writethrough.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.writethrough.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.writethrough.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.nocache.get! ((st Model_t)) Num
  (State.pte.nocache.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.nocache.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.nocache.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.accessed.get! ((st Model_t)) Num
  (State.pte.accessed.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.accessed.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.accessed.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.dirty.get! ((st Model_t)) Num
  (State.pte.dirty.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.dirty.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.dirty.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.pat.get! ((st Model_t)) Num
  (State.pte.pat.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.pat.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.pat.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.global.get! ((st Model_t)) Num
  (State.pte.global.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.global.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.global.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.ignored.get! ((st Model_t)) Num
  (State.pte.ignored.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.ignored.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.ignored.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.State.pte.base.get! ((st Model_t)) Num
  (State.pte.base.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.pte.base.set! ((st Model_t) (val Num)) Model_t
  (Model.State.set! 
    st
    (State.pte.base.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)


; state field: state.cr4
;----------------------------------------------------------------------------------------------------

(define-fun Model.State.cr4.get! ((st Model_t)) StateField.cr4_t
  (State.cr4.get! 
    (Model.State.get! 
      st
    )
  )
)

(define-fun Model.State.cr4.set! ((st Model_t) (val StateField.cr4_t)) Model_t
  (Model.State.set! 
    st
    (State.cr4.set! 
      (Model.State.get! 
        st
      )
      val
    )
  )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Model Interface Accessors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; interface field: interface.pte
;----------------------------------------------------------------------------------------------------

(define-fun Model.IFace.pte.get! ((st Model_t)) IFaceField.pte_t
  (IFace.pte.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.set! ((st Model_t) (val IFaceField.pte_t)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.present.get! ((st Model_t)) Num
  (IFace.pte.present.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.present.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.present.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.writable.get! ((st Model_t)) Num
  (IFace.pte.writable.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.writable.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.writable.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.usermode.get! ((st Model_t)) Num
  (IFace.pte.usermode.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.usermode.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.usermode.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.writethrough.get! ((st Model_t)) Num
  (IFace.pte.writethrough.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.writethrough.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.writethrough.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.nocache.get! ((st Model_t)) Num
  (IFace.pte.nocache.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.nocache.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.nocache.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.accessed.get! ((st Model_t)) Num
  (IFace.pte.accessed.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.accessed.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.accessed.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.dirty.get! ((st Model_t)) Num
  (IFace.pte.dirty.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.dirty.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.dirty.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.pat.get! ((st Model_t)) Num
  (IFace.pte.pat.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.pat.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.pat.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.global.get! ((st Model_t)) Num
  (IFace.pte.global.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.global.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.global.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.ignored.get! ((st Model_t)) Num
  (IFace.pte.ignored.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.ignored.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.ignored.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)

(define-fun Model.IFace.pte.base.get! ((st Model_t)) Num
  (IFace.pte.base.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.pte.base.set! ((st Model_t) (val Num)) Model_t
  (Model.IFace.set! 
    st
    (IFace.pte.base.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)


; interface field: interface.cr4
;----------------------------------------------------------------------------------------------------

(define-fun Model.IFace.cr4.get! ((st Model_t)) IFaceField.cr4_t
  (IFace.cr4.get! 
    (Model.IFace.get! 
      st
    )
  )
)

(define-fun Model.IFace.cr4.set! ((st Model_t) (val IFaceField.cr4_t)) Model_t
  (Model.IFace.set! 
    st
    (IFace.cr4.set! 
      (Model.IFace.get! 
        st
      )
      val
    )
  )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Actions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; interface field: interface.pte
;----------------------------------------------------------------------------------------------------

;; performs the write actions of interface.pte
(define-fun Model.IFace.pte.writeaction! ((st Model_t)) Model_t
  (let (
    (st_1 (Model.State.pte.set! 
      st
      (Model.IFace.pte.get! 
        st
      )
    ))
  ) st_1)
)

;; performs the write actions of interface.pte
(define-fun Model.IFace.pte.readaction! ((st Model_t)) Model_t
  (let (
    (st_1 (Model.IFace.pte.set! 
      st
      (Model.State.pte.get! 
        st
      )
    ))
  ) st_1)
)


; interface field: interface.cr4
;----------------------------------------------------------------------------------------------------

;; performs the write actions of interface.cr4
(define-fun Model.IFace.cr4.writeaction! ((st Model_t)) Model_t
  st
)

;; performs the write actions of interface.cr4
(define-fun Model.IFace.cr4.readaction! ((st Model_t)) Model_t
  st
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Methods
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Function: valid, ../../examples/x86_pt.vrs:121:5
(define-fun valid ((st Model_t)) Bool
  (= 
    (Model.State.pte.present.get! 
      st
    )
    #x0000000000000001
  )
)

;; Function Preconditions: valid, ../../examples/x86_pt.vrs:121:5
(define-fun valid.pre ((st!0 Model_t)) Bool
  true
)

;; Function Assumptions: valid, ../../examples/x86_pt.vrs:121:5
(define-fun valid.assms ((st!0 Model_t)) Bool
  true
)

;; Function: matchflags, ../../examples/x86_pt.vrs:127:5
(define-fun matchflags ((st Model_t) (flgs Flags_t)) Bool
  (and 
    (= 
      (Model.State.pte.writable.get! 
        st
      )
      (Flags.writable.get! 
        flgs
      )
    )
    (= 
      (Model.State.pte.global.get! 
        st
      )
      #x0000000000000000
    )
  )
)

;; Function Body part 0: matchflags, ../../examples/x86_pt.vrs:127:5
(define-fun matchflags.part.0 ((st!0 Model_t) (flgs Flags_t)) Bool
  (= 
    (Model.State.pte.writable.get! 
      st!0
    )
    (Flags.writable.get! 
      flgs
    )
  )
)

;; Function Body part 1: matchflags, ../../examples/x86_pt.vrs:127:5
(define-fun matchflags.part.1 ((st!0 Model_t) (flgs Flags_t)) Bool
  (= 
    (Model.State.pte.global.get! 
      st!0
    )
    #x0000000000000000
  )
)

;; Checking the matchflags function result
(define-fun matchflags.map.result.0 ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  (matchflags.part.0 
    st!0
    flgs
  )
)

;; Checking the matchflags function result
(define-fun matchflags.map.result.1 ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  (matchflags.part.1 
    st!0
    flgs
  )
)

;; Checking the matchflags function result
(define-fun matchflags.map.result ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  (matchflags 
    st!0
    flgs
  )
)

;; Checking the matchflags function result
(define-fun matchflags.protect.result.0 ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  (matchflags.part.0 
    st!0
    flgs
  )
)

;; Checking the matchflags function result
(define-fun matchflags.protect.result.1 ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  (matchflags.part.1 
    st!0
    flgs
  )
)

;; Checking the matchflags function result
(define-fun matchflags.protect.result ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  (matchflags 
    st!0
    flgs
  )
)

;; Function Preconditions part 0: matchflags, ../../examples/x86_pt.vrs:127:5
(define-fun matchflags.pre.0 ((st!0 Model_t) (flgs Flags_t)) Bool
  (= 
    (Model.State.pte.present.get! 
      st!0
    )
    #x0000000000000001
  )
)

;; Function Preconditions: matchflags, ../../examples/x86_pt.vrs:127:5
(define-fun matchflags.pre ((st!0 Model_t) (flgs Flags_t)) Bool
  (and 
    true
    (= 
      (Model.State.pte.present.get! 
        st!0
      )
      #x0000000000000001
    )
  )
)

;; Function Assumptions: matchflags, ../../examples/x86_pt.vrs:127:5
(define-fun matchflags.assms ((st!0 Model_t) (flgs Flags_t)) Bool
  (and 
    (and 
      true
      (Flags_t.assms 
        flgs
      )
    )
    (valid 
      st!0
    )
  )
)

;; Function: translate, ../../examples/x86_pt.vrs:140:5
(define-fun translate ((st Model_t) (va VAddr_t)) PAddr_t
  (bvadd 
    va
    (bvshl 
      (Model.State.pte.base.get! 
        st
      )
      #x000000000000000c
    )
  )
)

;; Checking the translate function result
(define-fun translate.map.result ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  (forall (
    (i!0 Size_t)) 
    (=> 
      (and 
        (bvuge 
          #x0000000000000000
          i!0
        )
        (bvult 
          i!0
          sz
        )
      )
      (= 
        (translate 
          st!0
          (bvadd 
            va
            i!0
          )
        )
        (bvadd 
          pa
          i!0
        )
      )
    )
  )
)

;; Checking the translate function result
(define-fun translate.protect.result ((st!0 Model_t) (st!1 Model_t) (va VAddr_t) (sz Size_t)) Bool
  (forall (
    (i!0 Size_t)) 
    (=> 
      (and 
        (bvuge 
          #x0000000000000000
          i!0
        )
        (bvult 
          i!0
          sz
        )
      )
      (= 
        (translate 
          st!0
          (bvadd 
            va
            i!0
          )
        )
        (translate 
          st!1
          (bvadd 
            va
            i!0
          )
        )
      )
    )
  )
)

;; Function Preconditions part 0: translate, ../../examples/x86_pt.vrs:140:5
(define-fun translate.pre.0 ((st!0 Model_t) (va VAddr_t)) Bool
  (= 
    (Model.State.pte.present.get! 
      st!0
    )
    #x0000000000000001
  )
)

;; Function Preconditions: translate, ../../examples/x86_pt.vrs:140:5
(define-fun translate.pre ((st!0 Model_t) (va VAddr_t)) Bool
  (and 
    true
    (= 
      (Model.State.pte.present.get! 
        st!0
      )
      #x0000000000000001
    )
  )
)

;; Function Assumptions: translate, ../../examples/x86_pt.vrs:140:5
(define-fun translate.assms ((st!0 Model_t) (va VAddr_t)) Bool
  (and 
    (and 
      true
      (VAddr_t.assms 
        va
      )
    )
    (bvult 
      va
      #x0000000000001000
    )
  )
)

; skipping method unmap, no body defined
;; Function Preconditions: unmap, ../../examples/x86_pt.vrs:148:5
(define-fun unmap.pre ((st!0 Model_t) (va VAddr_t) (sz Size_t)) Bool
  true
)

;; Function Assumptions: unmap, ../../examples/x86_pt.vrs:148:5
(define-fun unmap.assms ((st!0 Model_t) (va VAddr_t) (sz Size_t)) Bool
  (and 
    (and 
      (and 
        (and 
          true
          (VAddr_t.assms 
            va
          )
        )
        (Size_t.assms 
          sz
        )
      )
      (= 
        va
        #x0000000000000000
      )
    )
    (= 
      sz
      #x0000000000001000
    )
  )
)

; skipping method map, no body defined
;; Function Preconditions: map, ../../examples/x86_pt.vrs:154:5
(define-fun map.pre ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  true
)

;; Function Assumptions: map, ../../examples/x86_pt.vrs:154:5
(define-fun map.assms ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  (and 
    (and 
      (and 
        (and 
          (and 
            (and 
              (and 
                true
                (VAddr_t.assms 
                  va
                )
              )
              (Size_t.assms 
                sz
              )
            )
            (Flags_t.assms 
              flgs
            )
          )
          (PAddr_t.assms 
            pa
          )
        )
        (= 
          va
          #x0000000000000000
        )
      )
      (= 
        sz
        #x0000000000001000
      )
    )
    (= 
      (bvand 
        pa
        #x0000000000000fff
      )
      #x0000000000000000
    )
  )
)

; skipping method protect, no body defined
;; Function Preconditions: protect, ../../examples/x86_pt.vrs:167:5
(define-fun protect.pre ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t)) Bool
  true
)

;; Function Assumptions: protect, ../../examples/x86_pt.vrs:167:5
(define-fun protect.assms ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t)) Bool
  (and 
    (and 
      (and 
        true
        (VAddr_t.assms 
          va
        )
      )
      (Size_t.assms 
        sz
      )
    )
    (Flags_t.assms 
      flgs
    )
  )
)

; skipping method foo, no body defined
;; Function Preconditions: foo, ../../examples/x86_pt.vrs:171:5
(define-fun foo.pre ((st!0 Model_t) (va VAddr_t)) Bool
  true
)

;; Function Assumptions: foo, ../../examples/x86_pt.vrs:171:5
(define-fun foo.assms ((st!0 Model_t) (va VAddr_t)) Bool
  (and 
    (and 
      (and 
        (and 
          (and 
            (and 
              (and 
                true
                (VAddr_t.assms 
                  va
                )
              )
              (bvult 
                va
                #x0000000000000000
              )
            )
            (bvugt 
              va
              #x0000000000000000
            )
          )
          (bvult 
            va
            #x0000000000000000
          )
        )
        (or 
          (bvugt 
            va
            #x0000000000000000
          )
          (= 
            va
            #x0000000000000000
          )
        )
      )
      (not 
        (= 
          va
          #x0000000000000001
        )
      )
    )
    (not 
      (= 
        va
        #x0000000000000002
      )
    )
  )
)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (va VAddr_t) (sz Size_t) (st!0 Model_t) (pa PAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (flgs Flags_t) (st!0 Model_t) (sz Size_t) (va VAddr_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (flgs Flags_t) (sz Size_t) (pa PAddr_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (sz Size_t) (pa PAddr_t) (st!0 Model_t) (va VAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (sz Size_t) (flgs Flags_t) (va VAddr_t) (pa PAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      va
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      sz
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      pa
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (flgs Flags_t) (st!0 Model_t) (sz Size_t) (va VAddr_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvshl 
        va
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (pa PAddr_t) (flgs Flags_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvshl 
        sz
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (va VAddr_t) (flgs Flags_t) (st!0 Model_t) (sz Size_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvshl 
        pa
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (pa PAddr_t) (flgs Flags_t) (sz Size_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvadd 
        va
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (flgs Flags_t) (va VAddr_t) (sz Size_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvadd 
        sz
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (flgs Flags_t) (st!0 Model_t) (sz Size_t) (va VAddr_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvadd 
        pa
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (sz Size_t) (flgs Flags_t) (pa PAddr_t) (st!0 Model_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvsub 
        va
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (pa PAddr_t) (sz Size_t) (flgs Flags_t) (st!0 Model_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvsub 
        sz
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvsub 
        pa
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (pa PAddr_t) (sz Size_t) (flgs Flags_t) (va VAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvand 
        va
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (pa PAddr_t) (va VAddr_t) (sz Size_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvand 
        sz
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (flgs Flags_t) (st!0 Model_t) (va VAddr_t) (sz Size_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvand 
        pa
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (pa PAddr_t) (sz Size_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvor 
        va
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (sz Size_t) (va VAddr_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvor 
        sz
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (flgs Flags_t) (st!0 Model_t) (pa PAddr_t) (sz Size_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvor 
        pa
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (sz Size_t) (pa PAddr_t) (va VAddr_t) (st!0 Model_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvand 
        (bvlshr 
          va
          symvar!0
        )
        symvar!1
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (flgs Flags_t) (pa PAddr_t) (sz Size_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvand 
        (bvlshr 
          sz
          symvar!0
        )
        symvar!1
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (pa PAddr_t) (flgs Flags_t) (sz Size_t) (va VAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvand 
        (bvlshr 
          pa
          symvar!0
        )
        symvar!1
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (pa PAddr_t) (sz Size_t) (flgs Flags_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvmul 
        va
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (sz Size_t) (va VAddr_t) (st!0 Model_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvmul 
        sz
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (sz Size_t) (st!0 Model_t) (va VAddr_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvmul 
        pa
        symvar!0
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (pa PAddr_t) (flgs Flags_t) (st!0 Model_t) (va VAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (flgs Flags_t) (st!0 Model_t) (pa PAddr_t) (sz Size_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvnot 
        (Flags.writable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (sz Size_t) (st!0 Model_t) (pa PAddr_t) (va VAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (Flags.readable.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (sz Size_t) (pa PAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvnot 
        (Flags.readable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (pa PAddr_t) (flgs Flags_t) (st!0 Model_t) (sz Size_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (Flags.devicemem.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (flgs Flags_t) (sz Size_t) (va VAddr_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvnot 
        (Flags.devicemem.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (va VAddr_t) (flgs Flags_t) (sz Size_t) (st!0 Model_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (Flags.usermode.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (pa PAddr_t) (va VAddr_t) (st!0 Model_t) (sz Size_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.base.set! 
      st0
      (bvnot 
        (Flags.usermode.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (va VAddr_t) (st!0 Model_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      symvar!0
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (st!0 Model_t) (va VAddr_t) (flgs Flags_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      symvar!1
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (sz Size_t) (va VAddr_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      va
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (st!0 Model_t) (va VAddr_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      va
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      sz
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (sz Size_t) (va VAddr_t) (st!0 Model_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      sz
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (va VAddr_t) (pa PAddr_t) (flgs Flags_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      pa
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (flgs Flags_t) (sz Size_t) (pa PAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      pa
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (sz Size_t) (va VAddr_t) (pa PAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvshl 
        va
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (flgs Flags_t) (va VAddr_t) (pa PAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvshl 
        va
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (flgs Flags_t) (pa PAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvshl 
        sz
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (flgs Flags_t) (pa PAddr_t) (sz Size_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvshl 
        sz
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (sz Size_t) (st!0 Model_t) (va VAddr_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvshl 
        pa
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (va VAddr_t) (st!0 Model_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvshl 
        pa
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (sz Size_t) (st!0 Model_t) (pa PAddr_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvadd 
        va
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (flgs Flags_t) (sz Size_t) (pa PAddr_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvadd 
        va
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (flgs Flags_t) (pa PAddr_t) (st!0 Model_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvadd 
        sz
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (flgs Flags_t) (pa PAddr_t) (va VAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvadd 
        sz
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (st!0 Model_t) (flgs Flags_t) (pa PAddr_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvadd 
        pa
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (flgs Flags_t) (va VAddr_t) (sz Size_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvadd 
        pa
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (pa PAddr_t) (va VAddr_t) (sz Size_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvsub 
        va
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (st!0 Model_t) (va VAddr_t) (pa PAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvsub 
        va
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (va VAddr_t) (sz Size_t) (st!0 Model_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvsub 
        sz
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (flgs Flags_t) (pa PAddr_t) (sz Size_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvsub 
        sz
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (flgs Flags_t) (st!0 Model_t) (va VAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvsub 
        pa
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (flgs Flags_t) (va VAddr_t) (st!0 Model_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvsub 
        pa
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (st!0 Model_t) (pa PAddr_t) (va VAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        va
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (pa PAddr_t) (sz Size_t) (st!0 Model_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        va
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (va VAddr_t) (flgs Flags_t) (st!0 Model_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        sz
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (sz Size_t) (pa PAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        sz
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (st!0 Model_t) (flgs Flags_t) (sz Size_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        pa
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (va VAddr_t) (st!0 Model_t) (sz Size_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        pa
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (st!0 Model_t) (flgs Flags_t) (sz Size_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvor 
        va
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (flgs Flags_t) (sz Size_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvor 
        va
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (flgs Flags_t) (va VAddr_t) (pa PAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvor 
        sz
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (pa PAddr_t) (sz Size_t) (st!0 Model_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvor 
        sz
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (st!0 Model_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvor 
        pa
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (pa PAddr_t) (va VAddr_t) (st!0 Model_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvor 
        pa
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (sz Size_t) (pa PAddr_t) (st!0 Model_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        (bvlshr 
          va
          symvar!0
        )
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (flgs Flags_t) (pa PAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(declare-const symvar!2 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        (bvlshr 
          va
          symvar!1
        )
        symvar!2
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (st!0 Model_t) (pa PAddr_t) (flgs Flags_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1 symvar!2))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        (bvlshr 
          sz
          symvar!0
        )
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (st!0 Model_t) (sz Size_t) (pa PAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(declare-const symvar!2 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        (bvlshr 
          sz
          symvar!1
        )
        symvar!2
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (flgs Flags_t) (pa PAddr_t) (sz Size_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1 symvar!2))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        (bvlshr 
          pa
          symvar!0
        )
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (va VAddr_t) (pa PAddr_t) (st!0 Model_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(declare-const symvar!2 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        (bvlshr 
          pa
          symvar!1
        )
        symvar!2
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (va VAddr_t) (st!0 Model_t) (sz Size_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1 symvar!2))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvmul 
        va
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (va VAddr_t) (pa PAddr_t) (st!0 Model_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvmul 
        va
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (sz Size_t) (st!0 Model_t) (flgs Flags_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvmul 
        sz
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (sz Size_t) (va VAddr_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvmul 
        sz
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (flgs Flags_t) (pa PAddr_t) (st!0 Model_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvmul 
        pa
        symvar!0
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (va VAddr_t) (st!0 Model_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(declare-const symvar!1 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvmul 
        pa
        symvar!1
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (flgs Flags_t) (pa PAddr_t) (va VAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0 symvar!1))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (sz Size_t) (pa PAddr_t) (va VAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (sz Size_t) (st!0 Model_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvnot 
        (Flags.writable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvnot 
        (Flags.writable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (Flags.readable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (sz Size_t) (flgs Flags_t) (va VAddr_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (Flags.readable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (st!0 Model_t) (sz Size_t) (va VAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvnot 
        (Flags.readable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (st!0 Model_t) (va VAddr_t) (pa PAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvnot 
        (Flags.readable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (Flags.devicemem.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (pa PAddr_t) (sz Size_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (Flags.devicemem.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (va VAddr_t) (sz Size_t) (pa PAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvnot 
        (Flags.devicemem.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (pa PAddr_t) (sz Size_t) (va VAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvnot 
        (Flags.devicemem.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (flgs Flags_t) (sz Size_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (Flags.usermode.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (pa PAddr_t) (st!0 Model_t) (va VAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (Flags.usermode.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (va VAddr_t) (flgs Flags_t) (pa PAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvnot 
        (Flags.usermode.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (flgs Flags_t) (pa PAddr_t) (st!0 Model_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvnot 
        (Flags.usermode.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (st!0 Model_t) (va VAddr_t) (pa PAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (sz Size_t) (pa PAddr_t) (va VAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (sz Size_t) (va VAddr_t) (pa PAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.present.set! 
      st0
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (flgs Flags_t) (pa PAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.present.set! 
      st0
      (bvnot 
        (Flags.writable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (pa PAddr_t) (va VAddr_t) (flgs Flags_t) (sz Size_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.present.set! 
      st0
      (Flags.readable.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (sz Size_t) (pa PAddr_t) (va VAddr_t) (st!0 Model_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.present.set! 
      st0
      (bvnot 
        (Flags.readable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (pa PAddr_t) (st!0 Model_t) (flgs Flags_t) (sz Size_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.present.set! 
      st0
      (Flags.devicemem.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (va VAddr_t) (sz Size_t) (st!0 Model_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.present.set! 
      st0
      (bvnot 
        (Flags.devicemem.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (va VAddr_t) (flgs Flags_t) (sz Size_t) (pa PAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.present.set! 
      st0
      (Flags.usermode.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (sz Size_t) (st!0 Model_t) (pa PAddr_t) (flgs Flags_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.present.set! 
      st0
      (bvnot 
        (Flags.usermode.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (pa PAddr_t) (st!0 Model_t) (sz Size_t) (flgs Flags_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.present.set! 
      st1
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (pa PAddr_t) (sz Size_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.present.set! 
      st1
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (flgs Flags_t) (pa PAddr_t) (st!0 Model_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.present.set! 
      st1
      (bvnot 
        (Flags.writable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (sz Size_t) (st!0 Model_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.present.set! 
      st1
      (bvnot 
        (Flags.writable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (sz Size_t) (st!0 Model_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.present.set! 
      st1
      (Flags.readable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (sz Size_t) (st!0 Model_t) (flgs Flags_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.present.set! 
      st1
      (Flags.readable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (pa PAddr_t) (st!0 Model_t) (sz Size_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.present.set! 
      st1
      (bvnot 
        (Flags.readable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.present.set! 
      st1
      (bvnot 
        (Flags.readable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (sz Size_t) (pa PAddr_t) (va VAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.present.set! 
      st1
      (Flags.devicemem.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (va VAddr_t) (sz Size_t) (st!0 Model_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.present.set! 
      st1
      (Flags.devicemem.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (va VAddr_t) (st!0 Model_t) (pa PAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.present.set! 
      st1
      (bvnot 
        (Flags.devicemem.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.present.set! 
      st1
      (bvnot 
        (Flags.devicemem.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (pa PAddr_t) (st!0 Model_t) (va VAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.present.set! 
      st1
      (Flags.usermode.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (st!0 Model_t) (va VAddr_t) (pa PAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.present.set! 
      st1
      (Flags.usermode.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (sz Size_t) (st!0 Model_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.present.set! 
      st1
      (bvnot 
        (Flags.usermode.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (flgs Flags_t) (st!0 Model_t) (va VAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.present.set! 
      st1
      (bvnot 
        (Flags.usermode.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (flgs Flags_t) (st!0 Model_t) (pa PAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (va VAddr_t) (flgs Flags_t) (sz Size_t) (pa PAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (va VAddr_t) (flgs Flags_t) (st!0 Model_t) (pa PAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.writable.set! 
      st0
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (sz Size_t) (pa PAddr_t) (flgs Flags_t) (st!0 Model_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.writable.set! 
      st0
      (bvnot 
        (Flags.writable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (pa PAddr_t) (va VAddr_t) (st!0 Model_t) (flgs Flags_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.writable.set! 
      st0
      (Flags.readable.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (flgs Flags_t) (sz Size_t) (pa PAddr_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.writable.set! 
      st0
      (bvnot 
        (Flags.readable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (va VAddr_t) (st!0 Model_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.writable.set! 
      st0
      (Flags.devicemem.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (flgs Flags_t) (va VAddr_t) (st!0 Model_t) (sz Size_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.writable.set! 
      st0
      (bvnot 
        (Flags.devicemem.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (sz Size_t) (pa PAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.writable.set! 
      st0
      (Flags.usermode.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (pa PAddr_t) (sz Size_t) (va VAddr_t) (flgs Flags_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.writable.set! 
      st0
      (bvnot 
        (Flags.usermode.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (va VAddr_t) (st!0 Model_t) (sz Size_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (sz Size_t) (flgs Flags_t) (va VAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (bvnot 
        (Flags.writable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (flgs Flags_t) (sz Size_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (bvnot 
        (Flags.writable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (flgs Flags_t) (va VAddr_t) (sz Size_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (Flags.readable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (pa PAddr_t) (st!0 Model_t) (va VAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (Flags.readable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (va VAddr_t) (pa PAddr_t) (st!0 Model_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (bvnot 
        (Flags.readable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (bvnot 
        (Flags.readable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (va VAddr_t) (flgs Flags_t) (pa PAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (Flags.devicemem.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (flgs Flags_t) (st!0 Model_t) (va VAddr_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (Flags.devicemem.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (va VAddr_t) (flgs Flags_t) (st!0 Model_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (bvnot 
        (Flags.devicemem.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (bvnot 
        (Flags.devicemem.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (pa PAddr_t) (va VAddr_t) (flgs Flags_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (Flags.usermode.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (pa PAddr_t) (sz Size_t) (st!0 Model_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (Flags.usermode.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (sz Size_t) (pa PAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (bvnot 
        (Flags.usermode.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (st!0 Model_t) (pa PAddr_t) (sz Size_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (bvnot 
        (Flags.usermode.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (flgs Flags_t) (st!0 Model_t) (va VAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.0 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (sz Size_t) (flgs Flags_t) (st!0 Model_t) (va VAddr_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (flgs Flags_t) (st!0 Model_t) (sz Size_t) (pa PAddr_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.global.set! 
      st0
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (pa PAddr_t) (flgs Flags_t) (st!0 Model_t) (va VAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.global.set! 
      st0
      (bvnot 
        (Flags.writable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.global.set! 
      st0
      (Flags.readable.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (sz Size_t) (flgs Flags_t) (pa PAddr_t) (st!0 Model_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.global.set! 
      st0
      (bvnot 
        (Flags.readable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (pa PAddr_t) (sz Size_t) (va VAddr_t) (st!0 Model_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.global.set! 
      st0
      (Flags.devicemem.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (pa PAddr_t) (flgs Flags_t) (st!0 Model_t) (va VAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.global.set! 
      st0
      (bvnot 
        (Flags.devicemem.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.global.set! 
      st0
      (Flags.usermode.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (pa PAddr_t) (st!0 Model_t) (sz Size_t) (va VAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.global.set! 
      st0
      (bvnot 
        (Flags.usermode.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (pa PAddr_t) (st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.global.set! 
      st1
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (pa PAddr_t) (st!0 Model_t) (va VAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.global.set! 
      st1
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (va VAddr_t) (st!0 Model_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.global.set! 
      st1
      (bvnot 
        (Flags.writable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (pa PAddr_t) (st!0 Model_t) (sz Size_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.global.set! 
      st1
      (bvnot 
        (Flags.writable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (pa PAddr_t) (va VAddr_t) (st!0 Model_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.global.set! 
      st1
      (Flags.readable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (va VAddr_t) (flgs Flags_t) (st!0 Model_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.global.set! 
      st1
      (Flags.readable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (pa PAddr_t) (sz Size_t) (st!0 Model_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.global.set! 
      st1
      (bvnot 
        (Flags.readable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (flgs Flags_t) (sz Size_t) (pa PAddr_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.global.set! 
      st1
      (bvnot 
        (Flags.readable.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (sz Size_t) (flgs Flags_t) (st!0 Model_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.global.set! 
      st1
      (Flags.devicemem.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.global.set! 
      st1
      (Flags.devicemem.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (flgs Flags_t) (sz Size_t) (st!0 Model_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.global.set! 
      st1
      (bvnot 
        (Flags.devicemem.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (flgs Flags_t) (va VAddr_t) (sz Size_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.global.set! 
      st1
      (bvnot 
        (Flags.devicemem.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (va VAddr_t) (flgs Flags_t) (pa PAddr_t) (sz Size_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.global.set! 
      st1
      (Flags.usermode.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (sz Size_t) (st!0 Model_t) (pa PAddr_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.global.set! 
      st1
      (Flags.usermode.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (st!0 Model_t) (sz Size_t) (va VAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.global.set! 
      st1
      (bvnot 
        (Flags.usermode.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (pa PAddr_t) (flgs Flags_t) (st!0 Model_t) (va VAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(declare-const symvar!0 Num)
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      symvar!0
    ))
  ) (let (
    (st2 (Model.IFace.pte.global.set! 
      st1
      (bvnot 
        (Flags.usermode.get! 
          flgs
        )
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (sz Size_t) (va VAddr_t) (st!0 Model_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result.1 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(get-value (symvar!0))
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.writable.set! 
      st0
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st2 (Model.IFace.pte.writeaction!  
      st1
    ))
  ) st2))
)

(assert 
  (forall (
    (va VAddr_t) (st!0 Model_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.readaction!  
      st0
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (st!0 Model_t) (sz Size_t) (flgs Flags_t) (va VAddr_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000000
    ))
  ) (let (
    (st2 (Model.IFace.pte.writable.set! 
      st1
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writeaction!  
      st2
    ))
  ) st3)))
)

(assert 
  (forall (
    (flgs Flags_t) (pa PAddr_t) (va VAddr_t) (sz Size_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writable.set! 
      st2
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writeaction!  
      st3
    ))
  ) st4))))
)

(assert 
  (forall (
    (pa PAddr_t) (va VAddr_t) (st!0 Model_t) (flgs Flags_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.pre 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writable.set! 
      st2
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writeaction!  
      st3
    ))
  ) st4))))
)

(assert 
  (forall (
    (flgs Flags_t) (pa PAddr_t) (va VAddr_t) (sz Size_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writable.set! 
      st2
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writeaction!  
      st3
    ))
  ) st4))))
)

(assert 
  (forall (
    (pa PAddr_t) (sz Size_t) (st!0 Model_t) (va VAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writable.set! 
      st2
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writeaction!  
      st3
    ))
  ) st4))))
)

(assert 
  (forall (
    (va VAddr_t) (pa PAddr_t) (flgs Flags_t) (sz Size_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.readaction!  
      st1
    ))
  ) (let (
    (st3 (Model.IFace.pte.base.set! 
      st2
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writable.set! 
      st3
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st5 (Model.IFace.pte.writeaction!  
      st4
    ))
  ) st5)))))
)

(assert 
  (forall (
    (va VAddr_t) (st!0 Model_t) (pa PAddr_t) (flgs Flags_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.pre 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.readaction!  
      st1
    ))
  ) (let (
    (st3 (Model.IFace.pte.base.set! 
      st2
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writable.set! 
      st3
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st5 (Model.IFace.pte.writeaction!  
      st4
    ))
  ) st5)))))
)

(assert 
  (forall (
    (pa PAddr_t) (st!0 Model_t) (va VAddr_t) (flgs Flags_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.readaction!  
      st1
    ))
  ) (let (
    (st3 (Model.IFace.pte.base.set! 
      st2
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writable.set! 
      st3
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st5 (Model.IFace.pte.writeaction!  
      st4
    ))
  ) st5)))))
)

(assert 
  (forall (
    (flgs Flags_t) (pa PAddr_t) (sz Size_t) (va VAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.readaction!  
      st1
    ))
  ) (let (
    (st3 (Model.IFace.pte.base.set! 
      st2
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writable.set! 
      st3
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st5 (Model.IFace.pte.writeaction!  
      st4
    ))
  ) st5)))))
)

(assert 
  (forall (
    (st!0 Model_t) (pa PAddr_t) (sz Size_t) (va VAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.set! 
      st1
      #x0000000200000000
    ))
  ) (let (
    (st3 (Model.IFace.pte.base.set! 
      st2
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writable.set! 
      st3
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st5 (Model.IFace.pte.writeaction!  
      st4
    ))
  ) st5)))))
)

(assert 
  (forall (
    (st!0 Model_t) (sz Size_t) (flgs Flags_t) (va VAddr_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.pre 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.set! 
      st1
      #x0000000200000000
    ))
  ) (let (
    (st3 (Model.IFace.pte.base.set! 
      st2
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writable.set! 
      st3
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st5 (Model.IFace.pte.writeaction!  
      st4
    ))
  ) st5)))))
)

(assert 
  (forall (
    (sz Size_t) (va VAddr_t) (st!0 Model_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.set! 
      st1
      #x0000000200000000
    ))
  ) (let (
    (st3 (Model.IFace.pte.base.set! 
      st2
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writable.set! 
      st3
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st5 (Model.IFace.pte.writeaction!  
      st4
    ))
  ) st5)))))
)

(assert 
  (forall (
    (pa PAddr_t) (va VAddr_t) (st!0 Model_t) (sz Size_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.set! 
      st1
      #x0000000200000000
    ))
  ) (let (
    (st3 (Model.IFace.pte.base.set! 
      st2
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writable.set! 
      st3
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st5 (Model.IFace.pte.writeaction!  
      st4
    ))
  ) st5)))))
)

(assert 
  (forall (
    (va VAddr_t) (sz Size_t) (flgs Flags_t) (st!0 Model_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writable.set! 
      st2
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writeaction!  
      st3
    ))
  ) st4))))
)

(assert 
  (forall (
    (pa PAddr_t) (sz Size_t) (flgs Flags_t) (va VAddr_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.pre 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writable.set! 
      st2
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writeaction!  
      st3
    ))
  ) st4))))
)

(assert 
  (forall (
    (flgs Flags_t) (va VAddr_t) (sz Size_t) (st!0 Model_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writable.set! 
      st2
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writeaction!  
      st3
    ))
  ) st4))))
)

(assert 
  (forall (
    (flgs Flags_t) (pa PAddr_t) (st!0 Model_t) (va VAddr_t) (sz Size_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.base.set! 
      st1
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st3 (Model.IFace.pte.writable.set! 
      st2
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writeaction!  
      st3
    ))
  ) st4))))
)

(assert 
  (forall (
    (st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.readaction!  
      st1
    ))
  ) (let (
    (st3 (Model.IFace.pte.base.set! 
      st2
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writable.set! 
      st3
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st5 (Model.IFace.pte.writeaction!  
      st4
    ))
  ) st5)))))
)

(assert 
  (forall (
    (sz Size_t) (st!0 Model_t) (pa PAddr_t) (va VAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.pre 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.readaction!  
      st1
    ))
  ) (let (
    (st3 (Model.IFace.pte.base.set! 
      st2
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writable.set! 
      st3
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st5 (Model.IFace.pte.writeaction!  
      st4
    ))
  ) st5)))))
)

(assert 
  (forall (
    (va VAddr_t) (st!0 Model_t) (pa PAddr_t) (sz Size_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.readaction!  
      st1
    ))
  ) (let (
    (st3 (Model.IFace.pte.base.set! 
      st2
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writable.set! 
      st3
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st5 (Model.IFace.pte.writeaction!  
      st4
    ))
  ) st5)))))
)

(assert 
  (forall (
    (va VAddr_t) (flgs Flags_t) (pa PAddr_t) (sz Size_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.pre 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        flgs
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.readaction!  
      st1
    ))
  ) (let (
    (st3 (Model.IFace.pte.base.set! 
      st2
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writable.set! 
      st3
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st5 (Model.IFace.pte.writeaction!  
      st4
    ))
  ) st5)))))
)

(assert 
  (forall (
    (va VAddr_t) (pa PAddr_t) (flgs Flags_t) (sz Size_t) (st!0 Model_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (matchflags.assms 
          st!0
          flgs
        )
      )
      (matchflags.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.set! 
      st1
      #x0000000200000000
    ))
  ) (let (
    (st3 (Model.IFace.pte.base.set! 
      st2
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writable.set! 
      st3
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st5 (Model.IFace.pte.writeaction!  
      st4
    ))
  ) st5)))))
)

(assert 
  (forall (
    (pa PAddr_t) (st!0 Model_t) (sz Size_t) (va VAddr_t) (flgs Flags_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.pre 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)


; Verification
;----------------------------------------------------------------------------------------------------


(push)
; Variable Definitions
(define-fun map ((st0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Model_t
  (let (
    (st1 (Model.IFace.pte.set! 
      st0
      #x0000000000000001
    ))
  ) (let (
    (st2 (Model.IFace.pte.set! 
      st1
      #x0000000200000000
    ))
  ) (let (
    (st3 (Model.IFace.pte.base.set! 
      st2
      (bvand 
        (bvlshr 
          pa
          #x000000000000000c
        )
        #x00000000000fffff
      )
    ))
  ) (let (
    (st4 (Model.IFace.pte.writable.set! 
      st3
      (Flags.writable.get! 
        flgs
      )
    ))
  ) (let (
    (st5 (Model.IFace.pte.writeaction!  
      st4
    ))
  ) st5)))))
)

(assert 
  (forall (
    (flgs Flags_t) (pa PAddr_t) (sz Size_t) (st!0 Model_t) (va VAddr_t)) 
    (=> 
      (and 
        (map.assms 
          st!0
          va
          sz
          flgs
          pa
        )
        (translate.assms 
          st!0
          va
        )
      )
      (translate.map.result 
        (map 
          st!0
          va
          sz
          flgs
          pa
        )
        va
        sz
        flgs
        pa
      )
    )
  )
)
(check-sat)
; Get Values
(echo "()")
(pop)

