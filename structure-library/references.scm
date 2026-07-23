;;; -----------------------------------------------------------------------
;;; BOOK REGISTRY -- the sources a `reference' warrant may cite by key.
;;;
;;; Loaded early (before any structure-library / theorem-library file), so a
;;; (warrant! 'thm 'reference '(KEY "Prop. II.2.1")) anywhere downstream
;;; resolves against a key registered here.  See the BOOK REGISTRY block in
;;; macetes.scm for the mechanism and the two-job (human citation / machine
;;; anchor) rationale.
;;;
;;; Discipline (decided 2026-07-22, kept REVERSIBLE -- legacy free-text
;;; references still work, nothing is migrated):
;;;   * cite at NAMED-RESULT granularity ("Prop. II.2.1"), section as fallback
;;;     ("II.1") -- edition-stable, edition-independent;
;;;   * page numbers, if given, go in the SEPARATE machine anchor
;;;     (warrant! ... '(KEY "II.1" 87)), never in the human citation string;
;;;   * every reference-warranted entry should carry a gloss! (soft-nudged).
;;;
;;;   (cite-book! 'KEY "Short name" "Title" "Edition" "/abs/path.pdf")
;;; Only KEY and short name are required; drop or "" the rest.  A PDF path is
;;; wired in when the file is actually on disk; where it is absent the human
;;; citation stands alone and a page anchor would resolve to nothing, so do not
;;; give one.  On disk today: lang, bourbaki-algebra, thayer-calc,
;;; thayer-spectral, yosida, theorie-spectrale, thayer-tvs, dieudonne, lima,
;;; hoffman-kunze, lima-la, reed-simon-1, reed-simon-2.  NOT on disk: schaefer.

;; Lang: OCR'd scan on disk (934 pp, one book page per PDF page).
;; PAGE ANCHORS ARE PDF PAGES: pdf page = printed page + 15 (verified at printed
;; 45/85/385/685/885).  Prose OCR is clean; displayed math is not -- navigate by
;; the text layer, read the page image to quote anything.
(cite-book! 'lang "Lang" "Algebra" "rev. 3rd ed. (GTM 211)" "/home/ubuntu/docs/AlgebraLang-ocr.pdf")
;; Bourbaki, Algebra I (Chapters 1-3), English ed.  OCR'd scan on disk, 733 pp.
;; PAGE ANCHORS ARE PDF PAGES, but the offset is NOT constant: pdf = printed + 24
;; through the body (verified at printed 36/176/376/626/656, i.e. all of Ch. I-III),
;; drifting to +23 in the back matter (a plate skipped near pdf 691-695; printed 673
;; = pdf 696).  Prose OCR clean; displayed math is noise, and the folio is at the
;; page FOOT -- navigate by the text layer, read the page image to quote anything.
(cite-book! 'bourbaki-algebra "Bourbaki" "Algebra I (Chapters 1-3)" "" "/home/ubuntu/docs/Algebra-Bourbaki-ocr.pdf")
;; Dieudonné, Foundations of Modern Analysis.  OCR'd scan on disk, 407 pp.
;; PAGE ANCHOR = pdf page = printed page + 19 (verified at printed 21/81/181).
;; Prose clean, math noise, and a `zyxwv...' watermark artifact eats the head
;; line on some pages -- read the image when the running head comes back garbled.
(cite-book! 'dieudonne "Dieudonné" "Foundations of Modern Analysis" "" "/home/ubuntu/docs/Dieudonne-ocr.pdf")
;; The user's own calculus notes -- first source with a real PDF on disk, so the
;; machine anchor (page) resolves.  Short name from the author (F. Javier Thayer).
(cite-book! 'thayer-calc "Thayer" "Calculus (notes)" "" "/home/ubuntu/docs/calculus.pdf")
;; Thayer's functional-analysis / spectral-theory text (Portuguese), a PUBLISHED
;; source -- citable as a real reference, not just exercises (user, 2026-07-23).
;; Born-digital LaTeX, clean text incl. math.  PAGE ANCHOR = pdf page = printed
;; page (offset 0; verified at printed 50/100/200).
(cite-book! 'thayer-spectral "Thayer" "Análise Funcional e Teoria Espectral" "" "/home/ubuntu/docs/th-main.pdf")
;; Yosida: two scans of the same book are on disk.  Use Yosida-Functional_Analysis.pdf
;; -- 517 pages, one book page per PDF page, and it carries an OCR text layer, so
;; pdftotext works on it.  (YosidaFnalAnalysis.pdf is a 2-up scan with NO text layer:
;; it can only be read as page images.)  PAGE ANCHORS ARE PDF PAGES: for this file
;; pdf page = book page + 17.
(cite-book! 'yosida "Yosida" "Functional Analysis" "6th ed." "/home/ubuntu/docs/Yosida-Functional_Analysis.pdf")
;; French notes, now OCR'd (was the no-text-layer scan until 2026-07-23).
;; PAGE ANCHOR = pdf page = printed page + 8 (folios in `-N-` form; verified at
;; printed 2/32/62/92).  French OCR clean incl. accents; math noise as usual.
(cite-book! 'theorie-spectrale "Théorie Spectrale" "Théorie Spectrale (notes)" "" "/home/ubuntu/docs/TheorieSpectrale-ocr.pdf")
;; Elon Lages Lima, Espacos Metricos (IMPA), a published classic (Portuguese).
;; Born-digital, clean text.  PAGE ANCHOR = pdf page = printed page + 10
;; (verified at printed 20/50/90/190/290).
(cite-book! 'lima "Lima" "Espacos Metricos (IMPA)" "" "/home/ubuntu/docs/MetricSpacesLima.pdf")
;; Linear algebra references.  Hoffman & Kunze (the classic) -- OCR'd scan,
;; pdf = printed + 8 (verified at printed 22/92/192/292), prose clean / math
;; noisy.  Lima, Algebra Linear (IMPA, Portuguese) -- born-digital, clean,
;; pdf = printed + 6 (verified at printed 24/94/194/294).  `lima-la' is a
;; DISTINCT key from `lima' (Espacos Metricos), same author.
(cite-book! 'hoffman-kunze "Hoffman-Kunze" "Linear Algebra" "2nd ed." "/home/ubuntu/docs/HoffmanKunze-ocr.pdf")
(cite-book! 'lima-la "Lima" "Algebra Linear (IMPA)" "" "/home/ubuntu/docs/LimaAlgebraLinear.pdf")
;; Reed & Simon, Methods of Modern Mathematical Physics I: Functional Analysis.
;; OCR'd scan, pdf = printed + 7 (verified printed 53/153/253/293/303).  Prose
;; clean; a `zyxwv...' watermark artifact (as in Dieudonne) eats the running head
;; on some pages -- read the image when a head comes back garbled; the folio
;; sits at the END of the head line.
(cite-book! 'reed-simon-1 "Reed-Simon" "Methods of Modern Mathematical Physics I" "" "/home/ubuntu/docs/Reed-Simon-vol-I-ocr.pdf")
;; Vol II (Fourier Analysis, Self-Adjointness).  Same OCR/watermark caveats, but
;; a DIFFERENT offset: pdf = printed + 4 (verified printed 76/136/196/256/316) --
;; the two volumes have different front matter, so don't share vol I's +7.
(cite-book! 'reed-simon-2 "Reed-Simon" "Methods of Modern Mathematical Physics II" "" "/home/ubuntu/docs/Reed-Simon-vol-II-ocr.pdf")
;; The user's topological-vector-space notes: Ch. 4 is the open mapping (Thm 4.7),
;; closed graph (Thm 4.9) and uniform boundedness chapter.
(cite-book! 'thayer-tvs "Thayer" "Topological Vector Spaces (notes)" "" "/home/ubuntu/docs/topological-vector-space.pdf")
;; Schaefer is the better TVS reference: III.1 (p. 74) defines a TOPOLOGICAL
;; HOMOMORPHISM (a linear map open onto its image), III.2 (p. 76) is Banach's
;; homomorphism theorem, IV.8 (p. 161) the general open mapping / closed graph
;; theorems for B-complete domains.  Not on this box -- no pdf-path, so the page
;; anchors are human citations only.
(cite-book! 'schaefer "Schaefer" "Topological Vector Spaces" "2nd ed. (GTM 3)" "")
