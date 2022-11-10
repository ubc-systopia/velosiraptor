

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

; flags for unit X86PageTableEntry (SrcLoc { context: Some("tests/precond_conflict.vrs"), line: 47, column: 5 }
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
          #x0000000000000003
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
            #xfffffffffffffffc
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x0000000000000003
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
            #xfffffffffffffff9
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x0000000000000003
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
            #xfffffffffffffff3
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x0000000000000003
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
            #xffffffffffffffe7
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x0000000000000003
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
            #xffffffffffffffcf
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x0000000000000003
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
            #xffffffffffffff9f
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x0000000000000003
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
            #xffffffffffffff3f
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x0000000000000003
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
            #xfffffffffffffe7f
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x0000000000000003
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
            #xfffffffffffffcff
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x000000000000000f
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
            #xffffffffffffe1ff
          )
          (bvshl 
            (bvand 
              v@
              #x000000000000000f
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
          #x00000000001fffff
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
            #xfffffffe00000fff
          )
          (bvshl 
            (bvand 
              v@
              #x00000000001fffff
            )
            #x000000000000000c
          )
        )
      ):pattern (StateField.pte.base.set! x@ v@))

  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; State
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; State Definition, tests/precond_conflict.vrs:54:13
(declare-datatypes ((State_t 0)) (
  ((State (State.pte StateField.pte_t)))))
(define-fun State.pte.get! ((s@ State_t)) StateField.pte_t
  (State.pte 
    s@
  )
)

(define-fun State.pte.set! ((s@ State_t) (v@ StateField.pte_t)) State_t
  (State 
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
          #x0000000000000003
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
            #xfffffffffffffffc
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x0000000000000003
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
            #xfffffffffffffff9
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x0000000000000003
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
            #xfffffffffffffff3
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x0000000000000003
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
            #xffffffffffffffe7
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x0000000000000003
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
            #xffffffffffffffcf
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x0000000000000003
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
            #xffffffffffffff9f
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x0000000000000003
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
            #xffffffffffffff3f
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x0000000000000003
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
            #xfffffffffffffe7f
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x0000000000000003
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
            #xfffffffffffffcff
          )
          (bvshl 
            (bvand 
              v@
              #x0000000000000003
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
          #x000000000000000f
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
            #xffffffffffffe1ff
          )
          (bvshl 
            (bvand 
              v@
              #x000000000000000f
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
          #x00000000001fffff
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
            #xfffffffe00000fff
          )
          (bvshl 
            (bvand 
              v@
              #x00000000001fffff
            )
            #x000000000000000c
          )
        )
      ):pattern (IFaceField.pte.base.set! x@ v@))

  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Interface
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Interface Definition, tests/precond_conflict.vrs:71:17
(declare-datatypes ((IFace_t 0)) (
  ((IFace (IFace.pte IFaceField.pte_t)))))
(define-fun IFace.pte.get! ((s@ IFace_t)) IFaceField.pte_t
  (IFace.pte 
    s@
  )
)

(define-fun IFace.pte.set! ((s@ IFace_t) (v@ IFaceField.pte_t)) IFace_t
  (IFace 
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Actions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; interface field: interface.pte
;----------------------------------------------------------------------------------------------------

;; performs the write actions of interface.pte
(define-fun Model.IFace.interface.pte.writeactions! ((st Model_t)) Model_t
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
(define-fun Model.IFace.interface.pte.readactions! ((st Model_t)) Model_t
  (let (
    (st_1 (Model.IFace.pte.set! 
      st
      (Model.State.pte.get! 
        st
      )
    ))
  ) st_1)
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Methods
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Function: matchflags, tests/precond_conflict.vrs:97:5
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

;; Function Preconditions part 0: matchflags, tests/precond_conflict.vrs:97:5
(define-fun matchflags.pre.0 ((st!0 Model_t) (flgs Flags_t)) Bool
  (= 
    (Model.State.pte.present.get! 
      st!0
    )
    #x0000000000000001
  )
)

;; Function Preconditions: matchflags, tests/precond_conflict.vrs:97:5
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

;; Function Assumptions: matchflags, tests/precond_conflict.vrs:97:5
(define-fun matchflags.assms ((st!0 Model_t) (flgs Flags_t)) Bool
  (and 
    true
    (Flags_t.assms 
      flgs
    )
  )
)

;; Function: translate, tests/precond_conflict.vrs:109:5
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

;; Function Preconditions part 0: translate, tests/precond_conflict.vrs:109:5
(define-fun translate.pre.0 ((st!0 Model_t) (va VAddr_t)) Bool
  (= 
    (Model.State.pte.present.get! 
      st!0
    )
    #x0000000000000000
  )
)

;; Function Preconditions: translate, tests/precond_conflict.vrs:109:5
(define-fun translate.pre ((st!0 Model_t) (va VAddr_t)) Bool
  (and 
    true
    (= 
      (Model.State.pte.present.get! 
        st!0
      )
      #x0000000000000000
    )
  )
)

;; Function Assumptions: translate, tests/precond_conflict.vrs:109:5
(define-fun translate.assms ((st!0 Model_t) (va VAddr_t)) Bool
  (and 
    (and 
      (and 
        true
        (VAddr_t.assms 
          va
        )
      )
      (= 
        va
        #x0000000000001000
      )
    )
    false
  )
)

; skipping method unmap, no body defined
;; Function Preconditions: unmap, tests/precond_conflict.vrs:118:5
(define-fun unmap.pre ((st!0 Model_t) (va VAddr_t) (sz Size_t)) Bool
  true
)

;; Function Assumptions: unmap, tests/precond_conflict.vrs:118:5
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
;; Function Preconditions: map, tests/precond_conflict.vrs:124:5
(define-fun map.pre ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t) (pa PAddr_t)) Bool
  true
)

;; Function Assumptions: map, tests/precond_conflict.vrs:124:5
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
;; Function Preconditions: protect, tests/precond_conflict.vrs:137:5
(define-fun protect.pre ((st!0 Model_t) (va VAddr_t) (sz Size_t) (flgs Flags_t)) Bool
  true
)

;; Function Assumptions: protect, tests/precond_conflict.vrs:137:5
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
;; Function Preconditions: foo, tests/precond_conflict.vrs:141:5
(define-fun foo.pre ((st!0 Model_t) (va VAddr_t)) Bool
  true
)

;; Function Assumptions: foo, tests/precond_conflict.vrs:141:5
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
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000000
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
    false:named fn_1-2)

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
    (= 
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
      #x0000000000000000
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
      #x0000000000000000
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
      #x0000000000000000
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
    false:named fn_1-2)

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
    false:named fn_1-2)

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
    false:named fn_1-2)

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
    (= 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
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
    (= 
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
      #x0000000000000000
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
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    false:named fn_2-2)

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
      #x0000000000000000
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000000
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
      #x0000000000000000
    ):named fn_1-1)

)
(assert 
  (! 
    false:named fn_2-2)

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
    false:named fn_1-2)

)
(assert 
  (! 
    false:named fn_2-2)

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
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000000
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
    false:named fn_1-2)

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
    (= 
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
      #x0000000000000000
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
      #x0000000000000000
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
    false:named fn_1-2)

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
    false:named fn_1-2)

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
    (= 
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
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
    (= 
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
      #x0000000000000000
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
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    false:named fn_2-2)

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
      #x0000000000000000
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000000
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
      #x0000000000000000
    ):named fn_1-1)

)
(assert 
  (! 
    false:named fn_2-2)

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
    false:named fn_1-2)

)
(assert 
  (! 
    false:named fn_2-2)

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
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000000
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
    false:named fn_1-2)

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
      va
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    (= 
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
    (= 
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
      #x0000000000000000
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
      #x0000000000001000
    ):named fn_1-0)

)
(assert 
  (! 
    false:named fn_2-2)

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
      #x0000000000000000
    ):named fn_1-1)

)
(assert 
  (! 
    (= 
      (Model.State.pte.present.get! 
        st
      )
      #x0000000000000000
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
      #x0000000000000000
    ):named fn_1-1)

)
(assert 
  (! 
    false:named fn_2-2)

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
    false:named fn_1-2)

)
(assert 
  (! 
    false:named fn_2-2)

)
(check-sat)
(get-unsat-core)
(pop)

