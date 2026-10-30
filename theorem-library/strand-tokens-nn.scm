;;; sb5-tokens.scm -- every subset of NN is a token set; a nonempty token set exists.
;;; Agent SB-5, 2026-10-26.  Destination: theorem-library/strand-tokens-nn.scm (library strand).
;;; Load window: after structure-library/strand-messages (IS-TOKEN-SET) and list-recursion
;;; (nn-not-a-list).  Helper prefix sbt-.

(sp (make-wff '(FORALL sbtt_ (IMPLIES (SUBSET sbtt_ NN) (IS-TOKEN-SET sbtt_)))))
(dk-peel!)
(fact 'nn-is-set)
(dk-have! '(IN sbtt_ SET) (lambda () (dk-sethood! 'sbtt_)))
(mac 'is-token-set)
(dk-conj-close!
  (lambda ()
    (if (not (dk-ass!))
        (begin
          (dk-peel!)
          (let ((x (cadr (cadr (dk-goal)))))
            (mac-h 'subset-def '(SUBSET sbtt_ NN))
            (dk-apply! (dk-pick (lambda (h) (and (dk-head-is? h 'FORALL) (dk-contains? h 'NN))) "the inclusion") x)
            (dk-cite! 'nn-not-a-list x)
            (dk-ass!))))))
(qed 'nn-subset-token-set)

(sp (make-wff '(IS-TOKEN-SET NN)))
(dk-have! '(SUBSET NN NN) (lambda () (mac 'subset-def) (di) (dk-ass!)))
(dk-cite! 'nn-subset-token-set 'NN)
(dk-ass!)
(qed 'nn-is-token-set)

(sp (make-wff '(FORSOME sbtt_ (AND (IS-TOKEN-SET sbtt_) (FORSOME sbtx_ (IN sbtx_ sbtt_))))))
(dk-cite! 'nn-is-token-set)
(fact 'nn-zero-in)
(ew 'NN)
(dk-conj-close! (lambda () (if (not (dk-ass!)) (begin (ew 0) (dk-ass!)))))
(qed 'token-set-nonempty-exists)
