;;; theorem-library/cnvs-view-typing.scm -- THE FLUSH POINT FOR THE COMPLEX NORMED VECTOR
;;; SPACE VIEWS (D8c, 2026-11-16).
;;;
;;; structure-library/cnvs-vocab.scm declares CNVS-AS-NVS, CNVS-AS-MODULE and
;;; CNVS-AS-NORMED-AG.  def-functor only QUEUES their typing obligations (D8b, s.1.3c);
;;; view-typing-flush! (structures.scm) proves the queue.  Until this file the first flush
;;; after cnvs-vocab was the one at the head of l2-hilbert, a file of the MEASURE library,
;;; so the three typings were sourced from it and cnvs-a (ANALYSIS) cited them across the
;;; library order (library-gate: analysis -> measure, cnvs-nvs-view-scal-pin uses
;;; cnvs-as-nvs-is-normed-vector-space).  This file, of the analysis library, loads
;;; between the CNVS vocabulary and l2-hilbert and proves them there.  It holds no other
;;; proof.
(view-typing-flush!)
