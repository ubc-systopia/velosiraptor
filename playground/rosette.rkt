#lang rosette

(require rosette/lib/synthax)
(require rosette/lib/destruct)


; define bitvector types
(define int64? (bitvector 64))
(define int32? (bitvector 32))
(define int16? (bitvector 16))
(define int8?  (bitvector  8))

; constructors for values
(define (int64 i) (bv i int64?))
(define (int32 i) (bv i int32?))
(define (int16 i) (bv i int16?))
(define (int8 i)  (bv i int8?))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; State Fields
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; State Definition
; A struct that contains all the defined state fields of the specification
; This struct models the state. Each field will be represented as a bitvector.
(struct statefields (entry) #:transparent)

; Declare a function to create a new state, and initialize the fields with
; known values.
(define (make-state-fields)
  (statefields (int64 0))
)

; State Field: 'entry'
;------------------------------------------------------------------------------

; TODO: have this as a struct as well? i.e., each entry field is a struct
;       of bitvectors of its slices?

; Accessor method to extract the value of the 'entry' field from the state
; TODO: can we just use the normal struct accessors?
(define (state-fields-load-entry st)
  (match st
    [(statefields e) e]
    [_               (printf "ERROR: wrong state supplied! expected statefields, got ~a" st) (assert #f) 0]
  )
)

; Accessor method to update the value of the 'entry' field.
; Note, we do not do inplace updates to have more control over the state.
(define (state-fields-store-entry st v)
  (struct-copy statefields st [entry v])
)

; Bitslice: entry.present
; -----------------------------------------------------------------------------

; extracts the present bits in the entry value
(define (state-fields-entry-present-extract val)
  (bvand val (int64 #x1)))

; inserts the present bits in the entry value
(define (state-fields-entry-present-insert old val)
  (bvor (bvand old (int64 #xfffffffffffffffe)) (bvand val (int64 1))))

; extracts the present bit from the state
(define (state-field-entry-present-read st)
  (state-fields-entry-present-extract (state-fields-load-entry st)))

; inserts the a new present value into the field 'entry'
(define (state-fields-entry-present-write st val)
  (state-fields-store-entry st
    (state-fields-entry-present-insert (state-fields-load-entry st) val)
  )
)

; Bitslice: entry.base
; -----------------------------------------------------------------------------

; extracts the base address from the 'entry'
(define (state-fields-entry-base-extract val)
  (bvand (bvlshr val (int64 12)) (int64 #xfffffffff)))

; insers the base address into an entry value
(define (state-fields-entry-base-insert old val)
  (bvor (bvand old (int64 #xffff000000000fff))
        (bvand val (int64 #xfffffffff000))))

; extracts the base portion of the state
(define (state-field-entry-base-read st)
  (state-fields-entry-base-extract (state-fields-load-entry st)))

; inserts the a new base value into the field 'entry'
(define (state-fields-entry-base-write st val)
  (state-fields-store-entry st
    (state-fields-entry-base-insert (state-fields-load-entry st) val)
  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Interface Fields (or local variables)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here, shall we do this as like a dictionary? So the synthesizer will actually
; need to initialize the used variables before?
; On the other hand, we can take the sequence of operations,

; Interface Definition
; A struct that contains values for all possible fields of the interface.
; Note, this effectively correspond to local variables in the function.
(struct interfacefields (entry) #:transparent)

; Declare a function to create a new interface state, and initialize the
; fields with the default values.
(define (make-interface-fields)
  (interfacefields (int64 0))
)

; Interface Field: 'entry'
;------------------------------------------------------------------------------

; Accessor method to read a the local variable 'entry'
; TODO: can we just use the normal struct accessors?
(define (var-fields-load-entry st)
  (match st
    [(interfacefields e) e]
    [_                   (printf "ERROR: wrong state supplied! expected interfacefields, got ~a" st) (assert #f) 0]
  )
)

; Accessor method to update the value fo the 'entry' local variable
; Note, this creates a new copy of the state
(define (var-fields-store-entry st v)
  (struct-copy interfacefields st [entry v])
)

; Bitslice: entry.present
; -----------------------------------------------------------------------------

; extracts the present bits in the entry value
(define (var-fields-entry-present-extract val)
  (bvand val (int64 #x1)))

; inserts the present bits in the entry value
(define (var-fields-entry-present-insert old val)
  (bvor (bvand old (int64 #xfffffffffffffffe)) (bvand val (int64 1))))

; reads the entry extracts the present bit from the vars
(define (var-fields-entry-present-read st)
  (var-fields-entry-present-extract (var-fields-load-entry st)))

; inserts 'val' into the 'present' bits of the 'entries' field in the variables
(define (var-fields-entry-present-write st val)
  (var-fields-store-entry st
    (var-fields-entry-present-insert (var-fields-load-entry st) val)
  )
)

; Bitslice: entry.base
; -----------------------------------------------------------------------------

; extracts the base address from the 'entry' value
(define (var-fields-entry-base-extract val)
  (bvand (bvlshr val (int64 12)) (int64 #xfffffffff)))

; insers the base address into an entry value
(define (var-fields-entry-base-insert old val)
  (bvor (bvand old (int64 #xffff000000000fff))
        (bvand val (int64 #xfffffffff000))))

; reads the entry and extracts the base
(define (var-fields-entry-base-read st)
  (var-fields-entry-base-extract (var-fields-load-entry st)))

; inserts 'val' into the 'base' bits of the 'entries' field in the variables
(define (var-fields-entry-base-write st v)
  (var-fields-store-entry st
    (var-fields-entry-base-insert (var-fields-load-entry st) v)
  )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Model Definition
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This defines the model of the unit. The model consists of
; - the state of the unit that defines the translation behavior
; - the availbe local variables of the interface.
(struct model (st var) #:transparent)

; create the state, it invokes the creation procedurs of the translation state and variables
(define (make-model)
  (model (make-state-fields) (make-interface-fields))
)

; Model Accessors
;------------------------------------------------------------------------------

; gets the translation state (ts) from the model
(define (model-get-state st)
  (match st
    [(model s _) s]
    [_            (printf "ERROR: wrong state supplied! expected state, got ~a" st) (assert #f) st]
  )
)

; updates the model with a new translation state
; NOTE: this returns a new copy of the model state
(define (model-set-state oldst newst)
  (struct-copy model oldst [st newst])
)

; gets the variable state from the model
(define (model-get-var st)
  (match st
    [(model _ var) var]
    [_            (printf "ERROR: wrong state supplied! expected state, got ~a" st) (assert #f) st]
  )
)

; updates the model with a new translation state
; NOTE: this returns a new copy of the model state
(define (model-set-var oldst newst)
  (struct-copy model oldst [var newst])
)


; State Accessors
;------------------------------------------------------------------------------

; loads the entry from the translation state
(define (state-load-entry st)
  (state-fields-load-entry (model-get-state st))
)

; stores a new value in the 'entry' field translation state
; NOTE: this creates a new copy of the state
(define (state-store-entry st val)
  (model-set-state st (state-fields-store-entry (model-get-state st) val))
)

; extract the present bit from the state
(define (state-entry-present-read st)
  (state-field-entry-present-read (model-get-state st))
)

(define (state-entry-present-write st val)
  (model-set-state st (state-fields-entry-present-write (model-get-state st) val))
)

; extract the base address from the entry
(define (state-entry-base-read st)
  (state-field-entry-base-read (model-get-state st))
)

(define (state-entry-base-write st val)
  (model-set-state st (state-fields-entry-base-write (model-get-state st) val))
)

; Variable Accessors
;------------------------------------------------------------------------------

; loads the 'entry' field from the state variables
(define (var-load-entry st)
  (var-fields-load-entry (model-get-var st))
)

; stores a new value in the 'entry' field variable state
; NOTE: this creates a new copy of the state
(define (var-store-entry st val)
  (model-set-var st (var-fields-store-entry (model-get-var st) val))
)

; here it's the same as in the state
(define (var-entry-present-read st)
  (var-fields-entry-present-read (model-get-var st))
)

(define (var-entry-present-write st val)
  (model-set-var st (var-fields-entry-present-write (model-get-var st) val))
)

(define (var-entry-base-read st)
  (var-fields-entry-base-read (model-get-var st))
)

(define (var-entry-base-write st val)
 (model-set-var st (var-fields-entry-base-write (model-get-var st) val))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Transfers Interface <--> State
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; the interface has just a single entry to read/write

; reads the 'entry' field in the interface
(define (interface-read-entry st)
  ; update the vars is just copy from the state
  (var-store-entry st (state-load-entry st)))

; writes the 'entry' field in the interface
(define (interface-write-entry st)
  ; update the state is just the copy to it
  (state-store-entry st (var-load-entry st)))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Translation Function
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; the translate function defines the semantics
(define (translate st va flags)
    ; the va must be smaller than the static size
    (assert (bvule va (int64 4096)))
    ; the entry must be set
    (assert (bveq (state-entry-present-read st) (int64 1)))
    ; then just add the base
    (bvadd (bvshl (state-entry-base-read st) (int64 12)) va)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Grammar
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Expresses a sequence of operations
(struct Seq (op rem)   #:transparent)
(struct Return ()      #:transparent)

; have a node for each interface field and bitslice
(struct OpVarEntryPresentInsert (arg) #:transparent)
(struct OpVarEntryBaseInsert    (arg) #:transparent)
(struct OpStoreEntry ()               #:transparent)

; Grammar Definition
(define-grammar (ast-grammar st va pa size flags)
  [
    stmts (choose                           ; STMTS :=
      (Return)                              ;        | RETURN
      (Seq (op) (stmts))                    ;        |SEQ(OP, STMTS)
    )
  ]
  [
    op (choose                              ; OP :=
      (OpVarEntryPresentInsert (valexpr))   ;     | OpVarEntryPresentInsert(VALEXPR)
      (OpVarEntryBaseInsert    (valexpr))   ;     | OpVarEntryBaseInsert(VALEXPR)
      (OpStoreEntry)                        ;     | OpStoreEntry
    )
  ]
  [ valexpr (choose                         ; VALEXPR :=
          va                                ;          | va
          pa                                ;          | pa
          size                              ;          | size
          flags                             ;          | flags
          (?? int64?)                       ;          | const
          ;((binop) (valexpr) (valexpr))
    )
  ]
  [
    binop (choose                           ; BINOP :=
      bvadd bvand bvlshr bvshl              ;        | + | & | << | >>
    )
  ]
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Interpretation Function
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; the interpretation function evaluates the program and applies the updates
; to the state.
; TODO: check the constraints on every check here. e.g., set the present bit last
(define (ast-interpret prog st)
  (destruct prog
    [(Seq s b) (destruct s
       [(OpVarEntryPresentInsert v) (ast-interpret b (var-entry-present-write st v))]
       [(OpVarEntryBaseInsert v)    (ast-interpret b (var-entry-base-write st v))]
       [(OpStoreEntry)              (ast-interpret b (interface-write-entry st))]
       [_                           st])
    ]
    [_ st]
  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Correctness Proparty
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Evaluates the interpreted function, checks translation properties
(define (ast-check-translate impl va pa size flags)
  (assume (bveq (bvand pa (int64 #xfff)) (int64 0)))  ; the base address must be aligned to zero
  (assume (bvule pa (int64 #xffffffffffff)))          ; the base address must not be larger than max
  (assume (bvule size (int64 #xfff)))                 ; the size must not exceed size <= 0xfff
  (assume (bveq va (int64 0)))                        ; the base address must be aligned to zero

  (let ([st (make-model)])
    ; evaluate the implementation, update the state
    (set! st (ast-interpret (impl st va pa size flags) st))

    ; now check if the translation is right
    (assert (bveq (translate st va 0) pa))
  )
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Solving / Synthesizing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define maxdepth 5)

;(define (try-synthesize i)
; define symbolic variables
(define-symbolic va int64?)
(define-symbolic pa int64?)
(define-symbolic size int64?)
(define-symbolic flags int64?)

(define (do-map-synth st va pa size flags)
  (ast-grammar st va pa size flags #:depth 5))

(define sol
    (synthesize
    #:forall    (list va pa size flags)
    #:guarantee (ast-check-translate do-map-synth va pa size flags)))

(if (sat? sol)
  (generate-forms sol)
  (printf "no solution found at all with maxdepth ~a\n" maxdepth)
)
