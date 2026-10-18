;;; reference-html.scm -- the browser pages of the VNB reference, built by
;;; the prover image itself.
;;;
;;; This file replaces three Python builders that lived in reference/
;;; (the user's decision of 2026-10-17: VNB itself is Scheme or elisp,
;;; Python is for integrator tooling only):
;;;
;;;   (build-home-html [out-dir [port]])     was reference/build-home-html.py
;;;       writes home.html, the browser landing page.  PORT (default 8973)
;;;       is the localhost listener the workbench links poke
;;;       (`vnb--home-server-ensure' in emacs/vnb-launch.el).
;;;   (build-graph-html [out-dir [in-dir]])  was reference/build-graph-html.py
;;;       reads structure-graph.dot, renders each of the 16 layer
;;;       combinations with the external program `dot -Tsvg', and writes
;;;       structure-graph.html.
;;;   (build-reference-html [out-dir [in-dir]]) was reference/build-reference-html.py
;;;       converts the reference/*.md documents of `rh--docs' into one page
;;;       per document plus the reference.html hub.
;;;
;;; OUT-DIR and IN-DIR default to `*reference-dir*' (load.scm); #f also
;;; means the default.  Each procedure returns the path, or the list of
;;; paths, it wrote.
;;;
;;; THE CONTRACT: for the same inputs each procedure writes the same bytes
;;; the Python script wrote.  The Python used regular expressions; each one
;;; is replaced here by a hand scanner, and the comment above each scanner
;;; quotes the expression it reproduces, including its backtracking
;;; behaviour where that matters.  "Whitespace" is Python's `str.isspace'
;;; set (`rh--space?'), which is what `\s', `\S' and the argument-free
;;; `strip'/`split' of Python 3 use on str.
;;;
;;; Internal helpers carry the prefix `rh--'.

(declare (usual-integrations))

;;; -----------------------------------------------------------------------
;;; Strings

(define (rh--space? c)
  ;; Python 3 str.isspace: the C0 separators, Unicode White_Space and the
  ;; bidi classes B / S / WS.
  (let ((k (char->integer c)))
    (or (and (>= k 9) (<= k 13))
        (and (>= k #x1c) (<= k #x20))
        (= k #x85) (= k #xa0) (= k #x1680)
        (and (>= k #x2000) (<= k #x200a))
        (= k #x2028) (= k #x2029) (= k #x202f) (= k #x205f) (= k #x3000))))

(define (rh--dir d)
  (let ((d (if (or (default-object? d) (not d)) *reference-dir* d)))
    (if (string-suffix? "/" d) d (string-append d "/"))))

(define (rh--index-char s c start)
  ;; index of the first C in S at or after START, or #f
  (let ((n (string-length s)))
    (let loop ((i start))
      (cond ((>= i n) #f)
            ((char=? (string-ref s i) c) i)
            (else (loop (+ i 1)))))))

(define (rh--has-char? s c) (rh--index-char s c 0))

(define (rh--starts-at? s pat i)
  ;; does PAT occur in S at index I?
  (let ((m (string-length pat)))
    (and (>= i 0)
         (<= (+ i m) (string-length s))
         (let loop ((k 0))
           (or (= k m)
               (and (char=? (string-ref s (+ i k)) (string-ref pat k))
                    (loop (+ k 1))))))))

(define (rh--search s pat start)
  ;; index of the first occurrence of PAT in S at or after START, or #f
  (let ((last (- (string-length s) (string-length pat))))
    (if (= (string-length pat) 0)
        (and (<= start (string-length s)) start)
        (let ((c0 (string-ref pat 0)))
          (let loop ((i start))
            (cond ((> i last) #f)
                  ((and (char=? (string-ref s i) c0) (rh--starts-at? s pat i)) i)
                  (else (loop (+ i 1)))))))))

(define (rh--skip-space s i)
  (let ((n (string-length s)))
    (let loop ((i i))
      (if (and (< i n) (rh--space? (string-ref s i))) (loop (+ i 1)) i))))

(define (rh--skip-char s c i)
  (let ((n (string-length s)))
    (let loop ((i i))
      (if (and (< i n) (char=? (string-ref s i) c)) (loop (+ i 1)) i))))

(define (rh--strip-pred s pred)
  (let* ((n (string-length s))
         (a (let loop ((i 0))
              (if (and (< i n) (pred (string-ref s i))) (loop (+ i 1)) i)))
         (b (let loop ((j n))
              (if (and (> j a) (pred (string-ref s (- j 1)))) (loop (- j 1)) j))))
    (if (and (= a 0) (= b n)) s (substring s a b))))

(define (rh--strip s) (rh--strip-pred s rh--space?))                        ; s.strip()
(define (rh--strip-char s c) (rh--strip-pred s (lambda (x) (char=? x c))))  ; s.strip(c)

(define (rh--rstrip s)                                                      ; s.rstrip()
  (let loop ((j (string-length s)))
    (if (and (> j 0) (rh--space? (string-ref s (- j 1))))
        (loop (- j 1))
        (substring s 0 j))))

(define (rh--blank? s) (string-null? (rh--strip s)))

(define (rh--split s c)
  ;; s.split(c): every field, empty ones included
  (let loop ((start 0) (acc '()))
    (let ((i (rh--index-char s c start)))
      (if i
          (loop (+ i 1) (cons (substring s start i) acc))
          (reverse (cons (substring s start (string-length s)) acc))))))

(define (rh--first-word s)
  ;; s.split()[0] if s.split() else s
  (let* ((a (rh--skip-space s 0)) (n (string-length s)))
    (if (= a n)
        s
        (let loop ((b a))
          (if (and (< b n) (not (rh--space? (string-ref s b))))
              (loop (+ b 1))
              (substring s a b))))))

(define (rh--concat strs)
  ;; (apply string-append STRS), in chunks so that a list of any length is
  ;; safe.  String ports cost ~9 us apiece in MIT 12.1, string-append ~1 us,
  ;; so every builder here collects pieces and concatenates once.
  (let loop ((l strs) (acc '()))
    (if (null? l)
        (cond ((null? acc) "")
              ((null? (cdr acc)) (car acc))
              (else (rh--concat (reverse acc))))
        (let take ((l l) (k 0) (chunk '()))
          (if (or (null? l) (= k 1000))
              (loop l (cons (apply string-append (reverse chunk)) acc))
              (take (cdr l) (+ k 1) (cons (car l) chunk)))))))

(define (rh--concat-rev pieces) (rh--concat (reverse pieces)))

(define (rh--join strs sep)
  (if (null? strs)
      ""
      (let loop ((l (cdr strs)) (acc (list (car strs))))
        (if (null? l)
            (rh--concat-rev acc)
            (loop (cdr l) (cons* (car l) sep acc))))))

(define (rh--replace-all s from to)
  ;; s.replace(from, to)
  (let ((m (string-length from)) (n (string-length s)))
    (let loop ((start 0) (acc '()))
      (let ((i (rh--search s from start)))
        (if i
            (loop (+ i m) (cons* to (substring s start i) acc))
            (if (null? acc) s (rh--concat-rev (cons (substring s start n) acc))))))))

(define (rh--esc-char c)
  (case c
    ((#\&) "&amp;")
    ((#\<) "&lt;")
    ((#\>) "&gt;")
    ((#\") "&quot;")
    ((#\') "&#x27;")
    (else #f)))

(define (rh--esc s)
  ;; html.escape(s, quote=True)
  (let ((n (string-length s)))
    (let loop ((start 0) (i 0) (acc '()))
      (if (= i n)
          (if (null? acc) s (rh--concat-rev (cons (substring s start n) acc)))
          (let ((rep (rh--esc-char (string-ref s i))))
            (if rep
                (loop (+ i 1) (+ i 1) (cons* rep (substring s start i) acc))
                (loop start (+ i 1) acc)))))))

(define (rh--lines s)
  ;; s.split("\n")
  (rh--split s #\newline))

(define (rh--splitlines s)
  ;; s.splitlines() for the separators that can occur in a text read by
  ;; `rh--read' (\n only; \r is already translated): no trailing empty line.
  (let ((l (rh--split s #\newline)))
    (if (and (pair? l) (string-null? (car (last-pair l))))
        (except-last-pair! l)
        l)))

;;; -----------------------------------------------------------------------
;;; Files

(define (rh--read path)
  ;; The file as one string, "" when absent; decoded as UTF-8 with universal
  ;; newlines, as Python's open(path, encoding="utf-8").read() does.  Read as
  ;; bytes and decoded in one call: a character port is several times slower
  ;; on the 1 MB indexes.
  (if (not (file-exists? path))
      ""
      (let* ((bytes (call-with-port (open-binary-input-file path)
                      (lambda (in)
                        (let loop ((chunks '()))
                          (let ((b (read-bytevector 1048576 in)))
                            (if (eof-object? b)
                                (apply bytevector-append (reverse chunks))
                                (loop (cons b chunks))))))))
             (raw (utf8->string bytes)))
        (if (rh--has-char? raw #\return)
            (rh--replace-all (rh--replace-all raw "\r\n" "\n") "\r" "\n")
            raw))))

(define (rh--write path text)
  ;; TEXT encoded as UTF-8, written in one call
  (call-with-port (open-binary-output-file path)
    (lambda (out) (write-bytevector (string->utf8 text) out)))
  path)

;;; -----------------------------------------------------------------------
;;; 1. home.html

(define rh--home-ref-links
  '(("Library"           "reference.html"          "everything cross-linked \x2014; start here")
    ("Structures"        "STRUCTURE-INDEX.html"    "every structure: slots, laws, views")
    ("Categories"        "CATEGORIES.html"         "the default category of each structure, and the ones declared beside it")
    ("Theorems & axioms" "THEOREMS.html"           "the full installed catalog")
    ("Definitions"       "DEFINITIONS.html"        "term & predicate definitions")
    ("Proof Support Set" "PSS.html"                "theorems excused from the VNB test, accepted on a warrant")
    ("Fingerprint Index" "FINGERPRINT-INDEX.html"  "results bucketed by conclusion skeleton")
    ("Tactics"           "TACTICS.html"            "interactive proof commands, each with a one-line gloss")
    ("Glossary"          "GLOSSARY.html"           "every name in VNB, A to Z -- what it is, how it reads, where it is declared")
    ("Kernel rules"      "KERNEL-RULES.html"       "every inference rule the checker can record -- the trusted base beyond the axiom table")
    ("Kernel map"        "KERNEL-MAP.html"         "which code is permitted to record an inference, and what each proof command can reach")
    ("Structure Graph"   "structure-graph.html"    "refines & view-as relations, clickable")))

;;; Workbench: (heading (label fn-name blurb) ...).  Each fn-name MUST have a
;;; matching entry in `vnb--home-actions' (emacs/vnb-launch.el); the two are
;;; kept in sync by hand.
(define rh--home-workbench
  '(("Prove"
     ("Your first proof" "first-proof"    "brand new? a gentle two-step proof, guided all the way")
     ("Start Proof"      "start-proof"    "compose the goal theorem, then carry out its proof in a Focus workspace")
     ("Continue Proof"   "continue-proof" "return to the proof in progress, in its Focus workspace")
     ("Scratch"          "scratch"        "a free-form workspace for trying things out; C-j runs the current line or selection"))
    ("Build"
     ("What Is\x2026;?"   "what-is"        "look up a structure, number, or constant \x2014; its accessors, shape, type")
     ("Build Structure"  "build-structure" "define a new structure (saved to file)")
     ("\x2026;and a calculator too!" "calculator" "not just proofs \x2014; a live tape that does sums (2 + 3 \xd7; 5) and algebra ((x + y)\xb2; \x2192; x\xb2; + xy + y\xb2;); C-j works it out"))
    ("Session"
     ("Examples"         "examples"       "step through worked example proofs")
     ("Save Session"     "save-session"   "this session's proofs as one re-loadable script"))))

(define rh--home-hero-svg "
<svg class=\"hero-art\" viewBox=\"0 0 640 230\" xmlns=\"http://www.w3.org/2000/svg\"
     role=\"img\" aria-label=\"A graph of mathematical structures growing out of one another: set, group, ring, field, metric space, Euclidean ring.\">
  <defs>
    <marker id=\"ar\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\">
      <path d=\"M0,0 L10,5 L0,10 z\" fill=\"#9bb6d4\"/>
    </marker>
  </defs>
  <g fill=\"none\" stroke=\"#9bb6d4\" stroke-width=\"2\" marker-end=\"url(#ar)\">
    <path d=\"M120,115 C175,75 195,70 235,62\"/>
    <path d=\"M120,115 C185,150 210,165 250,178\"/>
    <path d=\"M300,62 C345,72 360,90 388,108\"/>
    <path d=\"M300,178 C350,168 362,150 388,122\"/>
    <path d=\"M470,108 C510,80 520,72 548,64\"/>
  </g>
  <g font-family=\"Georgia, serif\" font-size=\"15\" text-anchor=\"middle\">
    <g><ellipse cx=\"80\"  cy=\"115\" rx=\"48\" ry=\"30\" fill=\"#eaf2fb\" stroke=\"#7fa6cf\"/><text x=\"80\"  y=\"120\" fill=\"#2a4a6a\">set</text></g>
    <g><ellipse cx=\"268\" cy=\"62\"  rx=\"52\" ry=\"30\" fill=\"#e7f0ea\" stroke=\"#86b08f\"/><text x=\"268\" y=\"67\"  fill=\"#34603f\">group</text></g>
    <g><ellipse cx=\"268\" cy=\"178\" rx=\"78\" ry=\"31\" fill=\"#f3ecf6\" stroke=\"#a98cbf\"/><text x=\"268\" y=\"183\" fill=\"#5a3f72\">metric space</text></g>
    <g><ellipse cx=\"430\" cy=\"115\" rx=\"48\" ry=\"30\" fill=\"#e7f0ea\" stroke=\"#86b08f\"/><text x=\"430\" y=\"120\" fill=\"#34603f\">ring</text></g>
    <g><ellipse cx=\"580\" cy=\"62\"  rx=\"50\" ry=\"30\" fill=\"#fbf2e6\" stroke=\"#d59a3c\"/><text x=\"580\" y=\"67\"  fill=\"#8a5a12\">field</text></g>
    <g><ellipse cx=\"560\" cy=\"170\" rx=\"74\" ry=\"31\" fill=\"#fbf2e6\" stroke=\"#d59a3c\"/><text x=\"560\" y=\"175\" fill=\"#8a5a12\">Euclidean ring</text></g>
  </g>
  <g fill=\"none\" stroke=\"#9bb6d4\" stroke-width=\"2\" marker-end=\"url(#ar)\">
    <path d=\"M430,145 C475,165 495,168 520,170\"/>
  </g>
</svg>
")

;;; What VNB is -- faithful to docs/ch-intro.tex (paraphrased, no new claims).
(define rh--home-intro "
<section class=\"intro\">
  <p><b>Vienbi</b> &mdash; pronounced as (reading in English) the letters <b>VNB</b> &mdash;
  is an <b>interactive proof assistant</b> &mdash;
  a program you do mathematics <em>with</em>. You state a theorem and build its proof a
  step at a time; the machine checks every step against a small, auditable logical
  kernel, so a finished proof is correct <em>by construction</em>, not by trust.</p>
  <p>Its foundation is a first-order set theory in the style of von&nbsp;Neumann&ndash;Bernays:
  one universe of <em>classes</em>, with membership&nbsp;(&isin;) the only primitive notion.
  But you rarely touch that foundation &mdash; numbers, functions, and ordinals are built in as
  primitives governed by ordinary axioms, so a proof reads the way mathematics is actually
  written, not as a tower of encodings.</p>
</section>
")

(define rh--home-fits "
<h2>How it fits together</h2>
<div class=\"fits\">
  <div class=\"part\"><h3>The engine</h3>
    <p>An MIT&nbsp;Scheme program: the logical kernel, the library of structures and
    theorems, and the tactics you steer a proof with. The part that does the checking.</p></div>
  <div class=\"part\"><h3>This page</h3>
    <p>Where you <em>read</em>: browse the library, the catalog of theorems, and the
    clickable structure graph. No setup &mdash; just links in your browser.</p></div>
  <div class=\"part\"><h3>Emacs</h3>
    <p>The real work of doing mathematics takes place in several workspaces in Emacs,
    as explained below.</p></div>
</div>
<div class=\"reassure\">
  <p>The launcher sets everything up, and the links below open the right workspace in Emacs:</p>
  <ol>
    <li>writing and editing formal mathematical statements or potential theorems;</li>
    <li>starting proofs, either interactively &mdash; entering commands that modify the
    proof state &mdash; or by running scripts, sequences of commands that also modify the
    proof state. The two methods are entirely equivalent: what a user can do with one of
    these approaches can be done with the other;</li>
    <li>a copilot facility that suggests proof moves to the user.</li>
  </ol>
</div>
")

;;; The two named tactic-evaluation surfaces.
(define rh--home-surfaces "
<h2>Two surfaces for running tactics</h2>
<div class=\"fits\">
  <div class=\"part\"><h3>(a) The interactive surface</h3>
    <p>The Focus workspace: single-key commands and menus. You are <em>prompted</em>
    for each argument and type it <em>bare</em> &mdash; a lemma's <b>name</b> with no
    quote, a term in the minibuffer &mdash; and the command assembles the call for you.
    E.g. press <code>F</code>, accept <code>null-rr-seq-exists</code>, <kbd>RET</kbd>.</p></div>
  <div class=\"part\"><h3>(b) The programmatic surface</h3>
    <p>The Scratch workspace, the REPL, and saved proof scripts: you write the tactic
    as a Scheme s-expression, with the quoting <em>explicit</em>. A lemma name is a
    quoted <b>symbol</b>; a formula argument is a quoted <b>s-expression</b>:<br>
    <code>(fact 'null-rr-seq-exists)</code>,
    <code>(ai '(forsome rad (null-rr-seq rad)))</code>.</p></div>
</div>
<div class=\"reassure\">
  <p>The two are equivalent &mdash; anything you can do at one you can do at the other.
  They differ only in how you supply arguments: <b>prompted and bare</b> at (a),
  <b>written and quoted</b> at (b).</p>
</div>
")

(define rh--home-css "
 body { font-family: Helvetica, Arial, sans-serif; color:#1a2a3a;
        background:#eef3f9; margin:0; padding:2.4rem 1rem 3rem; }
 main { max-width:46rem; margin:0 auto; }
 .hero { text-align:center; margin:0 auto 1.2rem; }
 .hero-art { width:100%; max-width:30rem; height:auto; display:block; margin:0 auto .3rem; }
 .wordmark { font-family:\"Palatino Linotype\",\"Book Antiqua\",Palatino,\"Iowan Old Style\",
             \"Hoefler Text\",Georgia,\"Times New Roman\",serif;
             font-size:4.2rem; line-height:1; font-weight:600; letter-spacing:.01em;
             margin:.1rem 0 0;
             background:linear-gradient(95deg,#2a4a6a 0%,#3f7fb0 55%,#b06a00 100%);
             -webkit-background-clip:text; background-clip:text; color:transparent; }
 .tagline { color:#557; font-size:1.05rem; margin:.25rem 0 0; }
 .tagline b { color:#2a4a6a; letter-spacing:.04em; }
 h1 { color:#2a4a6a; font-size:1.6rem; margin:.2rem 0; }
 .sub { color:#667; margin:.2rem 0 2rem; }
 h2 { color:#365b7d; font-size:1.05rem; margin:1.8rem 0 .6rem;
      border-bottom:2px solid #dde6f0; padding-bottom:.2rem; }
 .intro { background:#fff; border:1px solid #dde6f0; border-radius:12px;
          padding:1rem 1.3rem; margin:1.3rem 0; line-height:1.55; color:#243446; }
 .intro p { margin:.5rem 0; }
 .fits { display:grid; grid-template-columns:repeat(auto-fit,minmax(12.5rem,1fr));
         gap:.7rem; margin:.6rem 0; }
 .fits .part { background:#fff; border:1px solid #dde6f0; border-radius:10px;
               padding:.8rem 1rem; }
 .fits .part h3 { margin:.1rem 0 .3rem; color:#2a4a6a; font-size:1rem; }
 .fits .part p { margin:0; color:#556; font-size:.92rem; line-height:1.45; }
 .reassure { background:#fdf6ec; border:1px solid #f0e0c4; border-left:4px solid #d59a3c;
             border-radius:8px; padding:.8rem 1.1rem; margin:1rem 0 1.4rem;
             color:#5a4a30; font-size:.95rem; line-height:1.5; }
 .card { display:block; background:#fff; border:1px solid #dde6f0;
         border-radius:10px; padding:.8rem 1rem; margin:.5rem 0;
         text-decoration:none; color:inherit; transition:box-shadow .12s; }
 .card:hover { box-shadow:0 2px 10px rgba(40,80,140,.15); border-color:#bcd0e8; }
 .card .t { font-weight:600; color:#2a4a6a; }
 .card .b { color:#667; font-size:.9rem; margin-top:.1rem; }
 .emacs .t::after { content:\" \\2192 Emacs\"; color:#b06a00; font-weight:400;
                    font-size:.82rem; }
 #flash { position:fixed; top:1rem; right:1rem; background:#2a4a6a; color:#fff;
          padding:.5rem .9rem; border-radius:6px; opacity:0; transition:opacity .2s;
          font-size:.9rem; }
 #flash.show { opacity:.95; }
 .classify { background:#fff; border:1px solid #dde6f0; border-radius:10px;
             padding:.4rem 1.1rem 1rem; margin:1.4rem 0 1rem; }
 .classify dt { font-weight:600; color:#2a4a6a; margin-top:.7rem; }
 .classify dd { margin:.15rem 0 0; color:#445; font-size:.92rem; }
 .classify .note { color:#556; font-size:.9rem; margin-top:.9rem;
                   border-top:1px solid #eef2f7; padding-top:.7rem; }
 .classify summary { cursor:pointer; color:#365b7d; font-weight:600;
                     font-size:1.05rem; padding:.6rem 0 .2rem; }
")

(define (rh--home-js port)
  (string-append "
 const PORT = " (number->string port) ";
 function flash(msg) {
   const f = document.getElementById('flash');
   f.textContent = msg; f.classList.add('show');
   setTimeout(() => f.classList.remove('show'), 1400);
 }
 function poke(ev, fn, label) {
   ev.preventDefault();
   fetch('http://127.0.0.1:' + PORT + '/do?fn=' + encodeURIComponent(fn),
         {mode:'no-cors'})
     .then(() => flash('\\u2192 ' + label + ' (see Emacs)'))
     .catch(() => flash('Emacs listener not reachable \x2014; start it from the launcher'));
 }
"))

;;; The result taxonomy.  Collapsed by default.
(define rh--home-classify "
<details class=\"classify\">
<summary>How results are classified</summary>
<dl>
  <dt>Axiom</dt>
  <dd>A primitive of VNB. The base we build on &mdash; small and essentially fixed.</dd>
  <dt>Definition</dt>
  <dd>True by construction (a defining equation, or an unfolding of one). <em>Not a
      theorem</em>, so it is never proved and is <em>not</em> a Proof Support Set
      member &mdash; but it still <strong>fires as a rewrite</strong> in proofs.</dd>
  <dt>Theorem</dt>
  <dd>Carries a machine proof, re-certified by the VNB test.</dd>
  <dt>Proof Support Set (PSS)</dt>
  <dd>A <em>theorem we trust on a warrant, without a machine proof</em> &mdash; excused
      from the VNB test. Each entry carries credentials: a plain statement plus why we
      accept it.</dd>
</dl>
<p class=\"note\"><strong>Firing is a separate matter.</strong> Whether the prover may apply
a result as a rewrite is independent of this classification: axioms, definitions, theorems,
and PSS members can all be rewrite rules. A definition keeps that right even though it is
not a PSS member.</p>
</details>
")

(define (rh--home-ref-card label href blurb)
  (string-append "<a class=\"card\" href=\"" (rh--esc href) "\">"
                 "<div class=\"t\">" (rh--esc label) "</div>"
                 "<div class=\"b\">" (rh--esc blurb) "</div></a>"))

(define (rh--home-emacs-card label fn blurb)
  (string-append "<a class=\"card emacs\" href=\"#\" "
                 "onclick=\"poke(event, '" (rh--esc fn) "', '" (rh--esc label) "')\">"
                 "<div class=\"t\">" (rh--esc label) "</div>"
                 "<div class=\"b\">" (rh--esc blurb) "</div></a>"))

(define (build-home-html #!optional out-dir port)
  (let* ((dir (rh--dir out-dir))
         (port (if (or (default-object? port) (not port)) 8973 port))
         (out (string-append dir "home.html"))
         (refs (rh--concat (map (lambda (r) (apply rh--home-ref-card r))
                                rh--home-ref-links)))
         (n-work 0)
         (works
          (rh--join
           (map (lambda (sect)
                  (set! n-work (+ n-work (length (cdr sect))))
                  (string-append
                   "<h2>" (rh--esc (car sect)) " <span class=\"sub\" style=\"font-size:.85rem\">"
                   "(opens in Emacs)</span></h2>\n"
                   (rh--concat (map (lambda (e) (apply rh--home-emacs-card e))
                                    (cdr sect)))))
                rh--home-workbench)
           "\n"))
         (doc (string-append "<!DOCTYPE html>
<html lang=\"en\"><head><meta charset=\"utf-8\">
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">
<title>Vienbi \x2014; VNB Math Assistant</title>
<style>" rh--home-css "</style></head><body>
<div id=\"flash\"></div>
<main>
<header class=\"hero\">
" rh--home-hero-svg "
<div class=\"wordmark\">Vienbi</div>
<p class=\"tagline\"><b>VNB</b> &middot; the von Neumann&ndash;Bernays Math Assistant</p>
</header>
" rh--home-intro "
" rh--home-fits "
" rh--home-surfaces "
<h2>Reference <span class=\"sub\" style=\"font-size:.85rem\">(reads in the browser)</span></h2>
" refs "
" works "
" rh--home-classify "
</main>
<script>" (rh--home-js port) "</script>
</body></html>
")))
    (rh--write out doc)
    (display (string-append "wrote " out "  (port " (number->string port) ", "
                            (number->string (length rh--home-ref-links)) " reference + "
                            (number->string n-work) " workbench links)"))
    (newline)
    out))

;;; -----------------------------------------------------------------------
;;; 2. structure-graph.html

;;; A node is a concrete INSTANCE (a number-system model, hidden by default)
;;; when its name starts with zz/qq/rr/cc/nn followed by `-', `+' or the end:
;;; Python's  re.match(r'(zz|qq|rr|cc|nn)([-+]|$)', name).
(define (rh--instance? name)
  (and (>= (string-length name) 2)
       (member (substring name 0 2) '("zz" "qq" "rr" "cc" "nn"))
       (or (= (string-length name) 2)
           (memv (string-ref name 2) '(#\- #\+)))
       #t))

;;; \s*"([^"]+)"  at the start of LINE: (name . index-after-closing-quote) or #f
(define (rh--quoted-at line i)
  (let ((i (rh--skip-space line i)))
    (and (< i (string-length line))
         (char=? (string-ref line i) #\")
         (let ((q (rh--index-char line #\" (+ i 1))))
           (and q (> q (+ i 1))
                (cons (substring line (+ i 1) q) (+ q 1)))))))

;;; \s*"([^"]+)"\s+\[tooltip   -> (name . index-after-"[tooltip") or #f
(define (rh--dot-node line)
  (let ((a (rh--quoted-at line 0)))
    (and a
         (let* ((j (cdr a)) (k (rh--skip-space line j)))
           (and (> k j)
                (rh--starts-at? line "[tooltip" k)
                (cons (car a) (+ k 8)))))))

;;; \s*"([^"]+)"\s*->\s*"([^"]+)"   -> (src tgt . index-after) or #f
(define (rh--dot-edge line)
  (let ((a (rh--quoted-at line 0)))
    (and a
         (let ((k (rh--skip-space line (cdr a))))
           (and (rh--starts-at? line "->" k)
                (let ((b (rh--quoted-at line (+ k 2))))
                  (and b (cons* (car a) (car b) (cdr b)))))))))

;;; After an edge: \s+\[KEY    -> index after "[KEY" or #f
(define (rh--dot-attr-open line j key)
  (let ((k (rh--skip-space line j)))
    (and (> k j)
         (rh--starts-at? line (string-append "[" key) k)
         (+ k 1 (string-length key)))))

;;; .*?KEY="([^"]*)"  from index J: (value . index-after-closing-quote) or #f.
;;; The lazy .*? takes the FIRST occurrence of KEY=" that has a closing quote.
(define (rh--lazy-attr line j key)
  (let ((pat (string-append key "=\"")))
    (let ((i (rh--search line pat j)))
      (and i
           (let* ((v (+ i (string-length pat)))
                  (q (rh--index-char line #\" v)))
             (and q (cons (substring line v q) (+ q 1))))))))

(define (rh--parse-dot text)
  ;; -> (nodes views refines bridges), each in file order;
  ;;    nodes: ((name . slots) ...), views: ((src tgt label full mapping) ...),
  ;;    refines: ((child . parent) ...), bridges: ((src tgt label) ...)
  (let loop ((ls (rh--splitlines text)) (nodes '()) (views '()) (refines '()) (bridges '()))
    (if (null? ls)
        (list (reverse nodes) (reverse views) (reverse refines) (reverse bridges))
        (let* ((line (car ls))
               (nd (rh--dot-node line))
               (node
                ;; \s*"([^"]+)"\s+\[tooltip="([^"]*)",\s*URL=
                (and nd
                     (rh--starts-at? line "=\"" (cdr nd))
                     (let ((q (rh--index-char line #\" (+ (cdr nd) 2))))
                       (and q
                            (rh--starts-at? line "," (+ q 1))
                            (rh--starts-at? line "URL=" (rh--skip-space line (+ q 2)))
                            (cons (car nd) (substring line (+ (cdr nd) 2) q)))))))
          (if node
              (let* ((tip (cdr node))
                     (s (rh--search tip "slots" 0))
                     (slots (if s (rh--strip (substring tip (+ s 5) (string-length tip))) "")))
                (loop (cdr ls) (cons (cons (car node) slots) nodes) views refines bridges))
              (let ((e (rh--dot-edge line)))
                (if (not e)
                    (loop (cdr ls) nodes views refines bridges)
                    (let* ((src (car e)) (tgt (cadr e)) (j (cddr e))
                           (dotted (rh--dot-attr-open line j "style=dotted"))
                           (blabel (and dotted (rh--lazy-attr line dotted "label"))))
                      (if blabel
                          (loop (cdr ls) nodes views refines
                                (cons (list src tgt (car blabel)) bridges))
                          (let* ((dashed (rh--dot-attr-open line j "style=dashed"))
                                 (vlabel (and dashed (rh--lazy-attr line dashed "label")))
                                 (vtip (and vlabel (rh--lazy-attr line (cdr vlabel) "tooltip"))))
                            (if vtip
                                (let* ((tip (car vtip))
                                       (c (rh--index-char tip #\: 0))
                                       (full (if c (substring tip 0 c) tip))
                                       (mapping (if c (substring tip (+ c 1) (string-length tip)) "")))
                                  (loop (cdr ls) nodes
                                        (cons (list src tgt (car vlabel) (rh--strip full) (rh--strip mapping))
                                              views)
                                        refines bridges))
                                ;; \s+\[color=.*tooltip=
                                (let ((colr (rh--dot-attr-open line j "color=")))
                                  (if (and colr (rh--search line "tooltip=" colr))
                                      (loop (cdr ls) nodes views (cons (cons src tgt) refines) bridges)
                                      (loop (cdr ls) nodes views refines bridges))))))))))))))

(define (rh--group-dot-lines text)
  ;; -> (preamble-string node-lines edges), node-lines ((name . line) ...),
  ;;    edges: alist section -> ((src tgt line) ...) for ref / view / bridge
  (let loop ((ls (rh--splitlines text)) (section 'pre) (pre '()) (nodes '())
             (ref '()) (view '()) (bridge '()))
    (if (null? ls)
        (list (rh--join (reverse pre) "\n") (reverse nodes)
              (list (cons 'ref (reverse ref)) (cons 'view (reverse view))
                    (cons 'bridge (reverse bridge))))
        (let ((ln (car ls)))
          (cond ((string=? (rh--strip ln) "}")
                 (loop (cdr ls) section pre nodes ref view bridge))
                ((rh--search ln "// refines" 0)
                 (loop (cdr ls) 'ref pre nodes ref view bridge))
                ((rh--search ln "// view-as" 0)
                 (loop (cdr ls) 'view pre nodes ref view bridge))
                ((rh--search ln "// bridges" 0)
                 (loop (cdr ls) 'bridge pre nodes ref view bridge))
                (else
                 (let ((nd (rh--dot-node ln)) (ed (rh--dot-edge ln)))
                   (cond (nd (loop (cdr ls) 'nodes pre (cons (cons (car nd) ln) nodes)
                                   ref view bridge))
                         ((and ed (eq? section 'ref))
                          (loop (cdr ls) section pre nodes
                                (cons (list (car ed) (cadr ed) ln) ref) view bridge))
                         ((and ed (eq? section 'view))
                          (loop (cdr ls) section pre nodes ref
                                (cons (list (car ed) (cadr ed) ln) view) bridge))
                         ((and ed (eq? section 'bridge))
                          (loop (cdr ls) section pre nodes ref view
                                (cons (list (car ed) (cadr ed) ln) bridge)))
                         ((eq? section 'pre)
                          (loop (cdr ls) section (cons ln pre) nodes ref view bridge))
                         (else (loop (cdr ls) section pre nodes ref view bridge))))))))))

(define (rh--assemble-dot preamble node-lines edges show-ref show-view show-bridge show-inst)
  (let* ((keep (filter (lambda (n) (or show-inst (not (rh--instance? n))))
                       (map car node-lines)))
         (keep? (lambda (n) (member n keep)))
         (out (list "" preamble)))
    (for-each (lambda (nl) (if (keep? (car nl)) (set! out (cons (cdr nl) out))))
              node-lines)
    (for-each
     (lambda (flag sect)
       (if flag
           (begin
             (set! out (cons (string-append "\n  // " (symbol->string sect)) out))
             (for-each (lambda (e)
                         (if (and (keep? (car e)) (keep? (cadr e)))
                             (set! out (cons (caddr e) out))))
                       (cdr (assq sect edges))))))
     (list show-ref show-view show-bridge)
     '(ref view bridge))
    (rh--join (reverse (cons "}" out)) "\n")))

(define (rh--render-svg dot-text)
  ;; `dot -Tsvg' on DOT-TEXT; drop the xml/doctype preamble; turn the external
  ;; links into in-page anchors.  The text goes to dot's stdin and its stdout
  ;; is read back through temporary files (decoded as UTF-8 with universal
  ;; newlines, as Python's subprocess.run(..., text=True) does): about 60 ms a
  ;; call less than piping through string ports.
  (load-option 'synchronous-subprocess)
  (call-with-temporary-file-pathname
   (lambda (in-path)
     (call-with-temporary-file-pathname
      (lambda (out-path)
        (rh--write (->namestring in-path) dot-text)
        (let ((status (run-shell-command
                       (string-append "dot -Tsvg < '" (->namestring in-path)
                                      "' > '" (->namestring out-path) "'"))))
          (if (not (eqv? status 0))
              (error "build-graph-html: dot failed with status" status))
          (let* ((svg (rh--read (->namestring out-path)))
                 (i (rh--search svg "<svg" 0)))
            (if (not i) (error "build-graph-html: dot produced no <svg"))
            (rh--replace-all (substring svg i (string-length svg))
                             "structure-graph.html#" "#"))))))))

;;; One combination per (refines view-as bridges instances), in the Python's
;;; order: r in (1 0), v in (0 1), b in (0 1), i in (0 1).
(define rh--graph-combos
  (append-map (lambda (r)
                (append-map (lambda (v)
                              (append-map (lambda (b)
                                            (map (lambda (i) (list r v b i)) '(0 1)))
                                          '(0 1)))
                            '(0 1)))
              '(1 0)))

(define (rh--combo-key c)
  (apply string-append
         (map (lambda (tag k) (string-append tag (number->string k)))
              '("r" "v" "b" "i") c)))

(define (rh--sort-strings l) (sort l string<?))

(define rh--graph-head "<!DOCTYPE html>
<html lang=\"en\"><head><meta charset=\"utf-8\">
<title>VNB structure graph</title>
<style>
 body { font-family: Helvetica, Arial, sans-serif; margin: 2rem; color:#1a2a3a; }
 h1 { font-size:1.4rem; } h3 { margin:.2rem 0; color:#2a4a6a; }
 .hint { color:#666; font-size:.9rem; }
 .controls { margin:.8rem 0; padding:.6rem .8rem; background:#f2f6fb; border-radius:8px;
              display:flex; gap:1.2rem; align-items:center; flex-wrap:wrap; font-size:.95rem; }
 .controls label { cursor:pointer; user-select:none; }
 .controls .swatch { font-weight:bold; }
 .controls .ref { color:#2a4a6a; } .controls .view { color:#b06a00; } .controls .bridge { color:#2a8a4a; }
 code.bridge { color:#2a8a4a; background:#eef7f0; }
 .controls input[type=text] { padding:.2rem .4rem; border:1px solid #bbcbdb; border-radius:4px; }
 .controls button { padding:.2rem .5rem; cursor:pointer; }
 .graph { overflow:auto; border:1px solid #ddd; border-radius:8px; padding:1rem; }
 .svgwrap g.node, .svgwrap g.edge { transition: opacity .15s; }
 svg a { cursor:pointer; }
 section, tr { scroll-margin-top: 1rem; }
 section:target, tr:target { background:#fff4e0; border-left:4px solid #b06a00; padding-left:.6rem; }
 .slots, .map { font-family: ui-monospace, Menlo, Consolas, monospace; color:#555; }
 .inst { font-size:.7rem; font-weight:normal; color:#888; border:1px solid #ccc;
          border-radius:3px; padding:0 .3rem; vertical-align:middle; }
 .cols { display:flex; gap:2rem; flex-wrap:wrap; }
 .cols section { min-width:16rem; }
 table { border-collapse:collapse; margin-top:.5rem; }
 td { border-top:1px solid #eee; padding:.3rem .8rem; vertical-align:top; }
 code { background:#f2f6fb; padding:0 .25rem; border-radius:3px; }
</style></head><body>
<h1>VNB structure graph</h1>
<p class=\"hint\"><span class=\"swatch ref\">&#9472;</span> refines (specialisation)
 &nbsp; <span class=\"swatch view\">&#9476;</span> view-as (forgetful map)
 &nbsp; <span class=\"swatch bridge\">&#8230;</span> bridge (constructor functoid, builds a new slot).
 Hover for full names; click a node or arrow to jump to its entry below.</p>
<div class=\"controls\">
 <label><input type=\"checkbox\" id=\"t-ref\" checked> <span class=\"ref\">refines</span></label>
 <label><input type=\"checkbox\" id=\"t-view\" checked> <span class=\"view\">view-as</span></label>
 <label><input type=\"checkbox\" id=\"t-bridge\"> <span class=\"bridge\">bridges</span></label>
 <label><input type=\"checkbox\" id=\"t-inst\"> instances</label>
 <span style=\"margin-left:auto\"></span>
 <label>focus: <input type=\"text\" id=\"focus\" list=\"names\" placeholder=\"structure\"></label>
 <datalist id=\"names\">")

(define rh--graph-script "</table>
<script>
(function(){
  var ref=document.getElementById('t-ref'),
      view=document.getElementById('t-view'),
      bridge=document.getElementById('t-bridge'),
      inst=document.getElementById('t-inst'),
      focus=document.getElementById('focus'),
      wraps=[].slice.call(document.querySelectorAll('.svgwrap'));
  function key(){ return 'r'+(ref.checked?1:0)+'v'+(view.checked?1:0)+'b'+(bridge.checked?1:0)+'i'+(inst.checked?1:0); }
  function visible(){ for(var i=0;i<wraps.length;i++) if(wraps[i].style.display!=='none') return wraps[i].querySelector('svg'); return null; }
  function title(g){ var t=g.querySelector('title'); return t?t.textContent.trim():''; }
  function applyFocus(){
    var svg=visible(); if(!svg) return;
    var f=focus.value.trim();
    var nodes=[].slice.call(svg.querySelectorAll('g.node')),
        edges=[].slice.call(svg.querySelectorAll('g.edge'));
    if(!f){ nodes.concat(edges).forEach(function(g){g.style.opacity=1;}); return; }
    var nbr={}; nbr[f]=1;
    edges.forEach(function(e){ var p=title(e).split('->'); if(p[0]===f)nbr[p[1]]=1; if(p[1]===f)nbr[p[0]]=1; });
    nodes.forEach(function(n){ n.style.opacity=nbr[title(n)]?1:0.12; });
    edges.forEach(function(e){ var p=title(e).split('->'); e.style.opacity=(p[0]===f||p[1]===f)?1:0.08; });
  }
  function show(){ var k=key(); wraps.forEach(function(w){ w.style.display=(w.getAttribute('data-combo')===k)?'block':'none'; }); applyFocus(); }
  [ref,view,bridge,inst].forEach(function(b){ b.addEventListener('change',show); });
  focus.addEventListener('input',applyFocus);
  document.getElementById('focus-clear').addEventListener('click',function(){ focus.value=''; applyFocus(); });
  show();
})();
</script>
</body></html>
")

(define (build-graph-html #!optional out-dir in-dir)
  (let* ((odir (rh--dir out-dir))
         (idir (rh--dir in-dir))
         (out (string-append odir "structure-graph.html"))
         (dot-path (string-append idir "structure-graph.dot"))
         (text (if (file-exists? dot-path)
                   (rh--read dot-path)
                   (error "build-graph-html: no such file:" dot-path)))
         (parsed (rh--parse-dot text))
         (nodes (car parsed)) (views (cadr parsed))
         (refines (caddr parsed)) (bridges (cadddr parsed))
         (grouped (rh--group-dot-lines text))
         (preamble (car grouped)) (node-lines (cadr grouped)) (edges (caddr grouped))
         (parent (make-string-hash-table))
         (slots (make-string-hash-table)))
    (for-each (lambda (cp) (hash-table-set! parent (car cp) (cdr cp))) refines)
    (for-each (lambda (ns) (hash-table-set! slots (car ns) (cdr ns))) nodes)
    (let* ((names (rh--sort-strings (hash-table-keys slots)))
           (wraps
            (map (lambda (c)
                   (let ((svg (rh--render-svg
                               (apply rh--assemble-dot preamble node-lines edges
                                      (map (lambda (k) (= k 1)) c)))))
                     (string-append
                      "<div class=\"svgwrap\" data-combo=\"" (rh--combo-key c) "\" "
                      "style=\"display:" (if (equal? c '(1 1 0 0)) "block" "none") "\">"
                      svg "</div>")))
                 rh--graph-combos))
           (secs
            (map (lambda (name)
                   (let* ((outv (filter (lambda (v) (string=? (car v) name)) views))
                          (rows (if (null? outv)
                                    "<li><em>none</em></li>"
                                    (rh--concat
                                     (map (lambda (v)
                                            (string-append
                                             "<li><a href=\"#views\"><code>" (rh--esc (caddr v))
                                             "</code></a> &rarr; "
                                             "<a href=\"#" (rh--esc (cadr v)) "\">" (rh--esc (cadr v)) "</a> "
                                             "<span class=\"map\">" (rh--esc (list-ref v 4)) "</span></li>"))
                                          outv))))
                          (par (hash-table-ref/default parent name #f))
                          (ref (if par
                                   (string-append "<p>refines <a href=\"#" (rh--esc par) "\">"
                                                  (rh--esc par) "</a></p>")
                                   ""))
                          (bout (filter (lambda (b) (string=? (car b) name)) bridges))
                          (bin (filter (lambda (b) (and (string=? (cadr b) name)
                                                        (not (string=? (car b) name))))
                                       bridges))
                          (brz (if (and (null? bout) (null? bin))
                                   ""
                                   (string-append
                                    "<p>bridges:</p><ul>"
                                    (rh--concat
                                     (map (lambda (b)
                                            (string-append
                                             "<li><code class=\"bridge\">" (rh--esc (caddr b))
                                             "</code> &rarr; <a href=\"#" (rh--esc (cadr b)) "\">"
                                             (rh--esc (cadr b)) "</a></li>"))
                                          bout))
                                    (rh--concat
                                     (map (lambda (b)
                                            (string-append
                                             "<li><a href=\"#" (rh--esc (car b)) "\">" (rh--esc (car b))
                                             "</a> &rarr; <code class=\"bridge\">" (rh--esc (caddr b))
                                             "</code></li>"))
                                          bin))
                                    "</ul>")))
                          (tag (if (rh--instance? name) " <span class=\"inst\">instance</span>" "")))
                     (string-append
                      "<section id=\"" (rh--esc name) "\"><h3>" (rh--esc name) tag "</h3>"
                      "<p class=\"slots\">slots " (rh--esc (hash-table-ref slots name (lambda () "")))
                      "</p>" ref
                      "<p>views out:</p><ul>" rows "</ul>" brz "</section>")))
                 names))
           (vrows
            (rh--concat
             (map (lambda (v)
                    (let ((s (car v)) (t (cadr v)) (full (cadddr v)) (m (list-ref v 4)))
                      (string-append
                       "<tr id=\"view-" (rh--esc full) "\"><td><code>" (rh--esc full) "</code></td>"
                       "<td><a href=\"#" (rh--esc s) "\">" (rh--esc s) "</a> &rarr; <a href=\"#"
                       (rh--esc t) "\">" (rh--esc t) "</a></td>"
                       "<td class=\"map\">" (rh--esc m) "</td></tr>")))
                  (sort views (lambda (a b) (string<? (cadddr a) (cadddr b)))))))
           (opts (rh--concat (map (lambda (n) (string-append "<option value=\"" (rh--esc n) "\">"))
                                  names)))
           (doc (string-append
                 rh--graph-head opts "</datalist>
 <button id=\"focus-clear\" type=\"button\">clear</button>
</div>
<div class=\"graph\">" (rh--concat wraps) "</div>
<h2 id=\"structures\">Structures</h2>
<div class=\"cols\">" (rh--concat secs) "</div>
<h2 id=\"views\">view-as functoids</h2>
<table><tr><th>functoid</th><th>map</th><th>components</th></tr>" vrows
                 rh--graph-script)))
      (rh--write out doc)
      (display (string-append
                "wrote " out "  (" (number->string (length names)) " structures, "
                (number->string (length views)) " views, "
                (number->string (length refines)) " refines, "
                (number->string (length bridges)) " bridges, "
                (number->string (length rh--graph-combos)) " layer combos)"))
      (newline)
      (display (string-append "  instances (default-hidden): "
                              (rh--join (filter rh--instance? names) ", ")))
      (newline)
      (display (string-append "  bridges: "
                              (rh--join (map (lambda (b)
                                               (string-append (car b) "->" (cadr b)
                                                              " (" (caddr b) ")"))
                                             bridges)
                                        "; ")))
      (newline)
      out)))

;;; -----------------------------------------------------------------------
;;; 3. reference.html and one page per document

;;; Ordered: reading-oriented first, retrieval indexes last.
;;; (title filename blurb).  STRUCTURE-INDEX precedes STRUCTURES so it claims
;;; the canonical structure ids.  A .md file absent from this list is
;;; reachable from no page.
(define rh--docs
  '(("Library map"        "LIBRARY.md"          "the lay of the land \x2014; where everything lives")
    ("Structures"         "STRUCTURE-INDEX.md"  "every structure: slots, laws, views")
    ("Structure notes"    "STRUCTURES.md"       "prose notes on the structure hierarchy")
    ("Categories"         "CATEGORIES.md"       "every category: the default arrows of each structure, the categories declared beside one (Lipschitz, continuous, bounded linear), the status of their laws, the inclusions")
    ("Theorems & axioms"  "THEOREMS.md"         "the full installed catalog")
    ("Definitions"        "DEFINITIONS.md"      "term & predicate definitions")
    ("Operators"          "OPERATORS.md"        "the operator census: every head as function / functoid / predicate / primitive")
    ("Glossary"           "GLOSSARY.md"         "every name in VNB -- structures, predicates, functoids, accessors, tactics -- in one alphabetical list")
    ("Functoids"          "FUNCTORS.md"         "structure-to-structure constructions")
    ("Proof Support Set"  "PSS.md"              "theorems excused from the VNB test, accepted on a warrant")
    ("By operator"        "BY-OPERATOR.md"      "results indexed by the operator they mention")
    ("Macete index"       "MACETE-INDEX.md"     "rewrite macetes, grouped")
    ("Fingerprint index"  "FINGERPRINT-INDEX.md" "results bucketed by conclusion skeleton")
    ("Proof debt"         "PROOF-DEBT.md"       "what each proof rests on (asserted base)")
    ("Debt bundle"        "DEBT-BUNDLE.md"      "the same debt raked into heaps: what to prove next (greedy what-if), and which arc each long bill comes in through")
    ("Tactics"            "TACTICS.md"          "interactive proof commands, each with a one-line gloss")
    ("Theorems by topic"  "BY-TOPIC.md"         "grouped by subject (calculus basics, metric spaces), each with a link to its proof")
    ("The kernel"         "KERNEL.md"           "the kernel in three parts: (a) the operations, each with the hypothesis sequents it creates and the conditions under which it declines, (b) the oracles, (c) the axioms; tactics are everything else")
    ("Kernel rules"       "KERNEL-RULES.md"     "every inference rule the checker can record, with its premises and conclusion -- the trusted base beyond the axiom table")
    ("Kernel map"         "KERNEL-MAP.md"       "which code is permitted to record an inference, and which of it each proof command can reach")
    ("Tactic uses"        "TACTIC-USES.md"      "for each proof command, the kernel operations it can reach: the bound on what the command can do")))

(define (rh--page-of secid) (string-append secid ".html"))
(define (rh--secid fname) (substring fname 0 (- (string-length fname) 3)))

;;; State of one build (the Python's module globals).
(define rh--in-dir #f)
(define rh--structs #f)        ; string hash tables used as sets
(define rh--thms #f)
(define rh--defs #f)
(define rh--pss #f)
(define rh--doc-anchors #f)    ; docid -> (slug -> heading id)
(define rh--current-docid #f)
(define rh--current-page #f)
(define rh--file-cache #f)

(define (rh--doc-text fname)
  (or (hash-table-ref/default rh--file-cache fname #f)
      (let ((t (rh--read (string-append rh--in-dir fname))))
        (hash-table-set! rh--file-cache fname t)
        t)))

(define (rh--set-of strs)
  (let ((h (make-string-hash-table)))
    (for-each (lambda (s) (hash-table-set! h s #t)) strs)
    h))

(define (rh--in? set s) (hash-table-ref/default set s #f))

(define (rh--structure-names)
  ;; re.match(r'\s*"([^"]+)"\s+\[tooltip=', line) over structure-graph.dot
  (let loop ((ls (rh--splitlines (rh--doc-text "structure-graph.dot"))) (acc '()))
    (if (null? ls)
        acc
        (let ((nd (rh--dot-node (car ls))))
          (loop (cdr ls)
                (if (and nd (rh--starts-at? (car ls) "=" (cdr nd))) (cons (car nd) acc) acc))))))

(define (rh--theorem-names)
  ;; re.match(r'\s*-\s+`([^`]+)`', line) over THEOREMS.md
  (let loop ((ls (rh--splitlines (rh--doc-text "THEOREMS.md"))) (acc '()))
    (if (null? ls)
        acc
        (let* ((line (car ls))
               (i (rh--skip-space line 0))
               (name
                (and (rh--starts-at? line "-" i)
                     (let ((j (rh--skip-space line (+ i 1))))
                       (and (> j (+ i 1))
                            (rh--starts-at? line "`" j)
                            (let ((q (rh--index-char line #\` (+ j 1))))
                              (and q (> q (+ j 1)) (substring line (+ j 1) q))))))))
          (loop (cdr ls) (if name (cons name acc) acc))))))

(define (rh--heading3-names fname)
  ;; re.match(r'###\s+(.+?)\s*$', line), then .strip("`").strip()
  (let loop ((ls (rh--splitlines (rh--doc-text fname))) (acc '()))
    (if (null? ls)
        acc
        (let* ((line (car ls))
               (name
                (and (rh--starts-at? line "###" 0)
                     (let* ((s (substring line 3 (string-length line)))
                            (w (rh--skip-space s 0)))
                       (cond ((= w 0) #f)
                             ((< w (string-length s))
                              (rh--strip (rh--strip-char (rh--rstrip (substring s w (string-length s))) #\`)))
                             ;; all whitespace: .+? takes the last blank, if one is left over
                             ((>= w 2) "")
                             (else #f))))))
          (loop (cdr ls) (if name (cons name acc) acc))))))

(define (rh--target-for name)
  ;; the home (page . anchor) of a linkable name, or #f
  (cond ((rh--in? rh--structs name) (cons (rh--page-of "STRUCTURE-INDEX") name))
        ((rh--in? rh--thms name) (cons (rh--page-of "THEOREMS") (string-append "t-" name)))
        ((rh--in? rh--defs name) (cons (rh--page-of "DEFINITIONS") (string-append "d-" name)))
        ((rh--in? rh--pss name) (cons (rh--page-of "PSS") (string-append "p-" name)))
        (else #f)))

(define (rh--slug-char? c)
  ;; [a-z0-9+*<>=/.-]
  (or (and (char>=? c #\a) (char<=? c #\z))
      (and (char>=? c #\0) (char<=? c #\9))
      (case c ((#\+ #\* #\< #\> #\= #\/ #\. #\-) #t) (else #f))))

(define (rh--slug s)
  ;; s.strip().strip("`").strip().lower(), runs outside [a-z0-9+*<>=/.-]
  ;; replaced by one "-", "-" stripped from both ends; "x" when empty.
  ;; Lowering: only ASCII letters and the two non-ASCII characters whose full
  ;; lowercase mapping contains an ASCII letter (U+212A KELVIN SIGN -> "k",
  ;; U+0130 -> "i" + U+0307) can yield a slug character; every other
  ;; non-ASCII character lowers to non-ASCII ones, i.e. to a "-" run.
  (let* ((s (rh--strip (rh--strip-char (rh--strip s) #\`)))
         (n (string-length s)))
    (let loop ((i 0) (acc '()) (in-run #f))
      (if (< i n)
          (let* ((c (string-ref s i))
                 (k (char->integer c)))
            (cond ((and (>= k 65) (<= k 90))
                   (loop (+ i 1) (cons (integer->char (+ k 32)) acc) #f))
                  ((and (< k 128) (rh--slug-char? c))
                   (loop (+ i 1) (cons c acc) #f))
                  ((= k #x212A) (loop (+ i 1) (cons #\k acc) #f))
                  ((= k #x130) (loop (+ i 1) (cons #\- (cons #\i acc)) #t))
                  (in-run (loop (+ i 1) acc #t))
                  (else (loop (+ i 1) (cons #\- acc) #t))))
          (let ((r (rh--strip-char (list->string (reverse acc)) #\-)))
            (if (string-null? r) "x" r))))))

;;; (#{1,6})\s   at the start of LINE: the level, or #f
(define (rh--heading-level line)
  (let ((k (rh--skip-char line #\# 0)))
    (and (>= k 1) (<= k 6)
         (< k (string-length line))
         (rh--space? (string-ref line k))
         k)))

;;; ^-{3,}\s*$
(define (rh--hr? line)
  (let ((k (rh--skip-char line #\- 0)))
    (and (>= k 3) (= (rh--skip-space line k) (string-length line)))))

;;; ^(\s*)-\s+   -> (indent . index-after-the-blanks) or #f
(define (rh--list-item line)
  (let ((k (rh--skip-space line 0)))
    (and (rh--starts-at? line "-" k)
         (let ((j (rh--skip-space line (+ k 1))))
           (and (> j (+ k 1)) (cons k j))))))

;;; ^ {4,}\S
(define (rh--indented-code? line)
  (let ((k (rh--skip-char line #\space 0)))
    (and (>= k 4) (< k (string-length line))
         (not (rh--space? (string-ref line k))))))

(define (rh--four-spaces? line) (rh--starts-at? line "    " 0))

(define (rh--heading-id-static level raw docid)
  (let ((name (rh--strip (rh--strip-char (rh--strip raw) #\`))))
    (cond ((rh--in? rh--structs name) name)
          ((and (string=? docid "DEFINITIONS") (= level 3)) (string-append "d-" name))
          ((and (string=? docid "PSS") (= level 3)) (string-append "p-" name))
          (else (string-append docid "__" (rh--slug raw))))))

(define (rh--setdefault! h k v)
  (if (not (hash-table-contains? h k)) (hash-table-set! h k v)))

(define (rh--prescan-anchors docid text)
  (let ((m (make-string-hash-table)))
    (for-each
     (lambda (line)
       (let ((level (rh--heading-level line)))
         (if level
             (let* ((raw (rh--strip (substring line level (string-length line))))
                    (hid (rh--heading-id-static level raw docid))
                    (name (or (and (rh--starts-at? raw "`" 0)
                                   (let ((q (rh--index-char raw #\` 1)))
                                     (and q (> q 1) (substring raw 1 q))))
                              (rh--first-word raw))))
               (rh--setdefault! m (rh--slug raw) hid)
               (rh--setdefault! m (rh--slug name) hid)))))
     (rh--lines text))
    m))

(define (rh--anchor-of doc key)
  (let ((m (hash-table-ref/default rh--doc-anchors doc #f)))
    (and m (hash-table-ref/default m key #f))))

(define (rh--md-doc-href href)
  ;; re.fullmatch(r"([A-Za-z0-9._-]+)\.md(?:#(.*))?", href) -> (doc . anchor-or-#f)
  (let* ((h (rh--index-char href #\# 0))
         (before (if h (substring href 0 h) href))
         (anchor (and h (substring href (+ h 1) (string-length href))))
         (n (string-length before)))
    (and (> n 3)
         (string-suffix? ".md" before)
         (let ((doc (substring before 0 (- n 3))))
           (and (let loop ((i 0))
                  (or (= i (string-length doc))
                      (let ((c (string-ref doc i)))
                        (and (or (rh--ascii-alnum? c) (memv c '(#\. #\_ #\-)))
                             (loop (+ i 1))))))
                (cons doc anchor))))))

(define (rh--ascii-alnum? c)
  (or (and (char>=? c #\A) (char<=? c #\Z))
      (and (char>=? c #\a) (char<=? c #\z))
      (and (char>=? c #\0) (char<=? c #\9))))

(define (rh--resolve-href href)
  ;; a markdown link target rewritten onto the ids this builder emits
  (cond ((and (rh--starts-at? href "#" 0) rh--current-docid)
         (let* ((key (rh--slug (substring href 1 (string-length href))))
                (hid (rh--anchor-of rh--current-docid key)))
           (if hid
               (string-append "#" hid)
               (string-append "#" rh--current-docid "__" key))))
        ((rh--md-doc-href href)
         => (lambda (da)
              (let ((doc (car da)) (anchor (cdr da)))
                (if (or (not anchor) (string-null? anchor))
                    (string-append doc ".html")
                    (let ((hid (rh--anchor-of doc (rh--slug anchor))))
                      (if hid
                          (string-append doc ".html#" hid)
                          (let ((t (rh--target-for anchor)))
                            (if (and t (string=? (car t) (string-append doc ".html")))
                                (string-append doc ".html#" (cdr t))
                                (string-append doc ".html#" doc "__" (rh--slug anchor))))))))))
        (else href)))

;;; --- inline markdown ---------------------------------------------------

(define (rh--linkify-code name)
  (let ((t (rh--target-for name))
        (inner (string-append "<code>" (rh--esc name) "</code>")))
    (if (not t)
        inner
        (let ((href (if (equal? (car t) rh--current-page)
                        (string-append "#" (rh--esc (cdr t)))
                        (string-append (rh--esc (car t)) "#" (rh--esc (cdr t))))))
          (string-append "<a class=\"x\" href=\"" href "\">" inner "</a>")))))

;;; Placeholders: "\x0;K\x0;" stands for the K-th stashed fragment.
(define rh--nul (integer->char 0))
(define rh--placeholders
  (let ((v (make-vector 64)))
    (do ((k 0 (+ k 1))) ((= k 64) v)
      (vector-set! v k (string-append (string rh--nul) (number->string k) (string rh--nul))))))

(define (rh--placeholder k)
  (if (< k 64)
      (vector-ref rh--placeholders k)
      (string-append (string rh--nul) (number->string k) (string rh--nul))))

(define (rh--nul? c) (char=? c rh--nul))

(define (rh--digit c)
  ;; the value of an ASCII digit, else #f.  (Python's \d also takes other
  ;; Unicode digits; a placeholder only ever holds ASCII ones.)
  (let ((k (- (char->integer c) 48)))
    (and (>= k 0) (<= k 9) k)))

;;; \x00(\d+)\x00 at index P: (k . index-after) or #f
(define (rh--placeholder-at s p)
  (let ((n (string-length s)))
    (and (< p n) (rh--nul? (string-ref s p))
         (let loop ((j (+ p 1)) (k 0))
           (let ((d (and (< j n) (rh--digit (string-ref s j)))))
             (cond (d (loop (+ j 1) (+ (* k 10) d)))
                   ((and (> j (+ p 1)) (< j n) (rh--nul? (string-ref s j)))
                    (cons k (+ j 1)))
                   (else #f)))))))

(define (rh--restore text spans)
  ;; while "\x00" in text: one re.sub pass of \x00(\d+)\x00 -> spans[k];
  ;; stop when a pass changes nothing.
  (let loop ((text text))
    (if (not (rh--has-char? text rh--nul))
        text
        (let ((new (rh--sub text rh--nul
                            (lambda (s p)
                              (let ((m (rh--placeholder-at s p)))
                                (and m (cons (vector-ref spans (car m)) (cdr m))))))))
          (if (string=? new text) text (loop new))))))

;;; A generic left-to-right substitution: (MATCH s p) returns
;;; (replacement . index-after) or #f; where it fails one character is copied.
(define (rh--sub text trigger match)
  (let ((n (string-length text)))
    (let loop ((start 0) (p (rh--index-char text trigger 0)) (acc '()))
      (if (not p)
          (if (null? acc) text (rh--concat-rev (cons (substring text start n) acc)))
          (let ((m (match text p)))
            (if m
                (loop (cdr m) (rh--index-char text trigger (cdr m))
                      (cons* (car m) (substring text start p) acc))
                (loop start (rh--index-char text trigger (+ p 1)) acc)))))))

;;; `([^`]+)`  -> (content . index-after) or #f
(define (rh--code-span-at s p)
  (let ((q (rh--index-char s #\` (+ p 1))))
    (and q (> q (+ p 1)) (cons (substring s (+ p 1) q) (+ q 1)))))

;;; \[([^\]]+)\]\(([^)]+)\)  -> (label href . index-after) or #f
(define (rh--md-link-at s p)
  (let ((q (rh--index-char s #\] (+ p 1))))
    (and q (> q (+ p 1))
         (rh--starts-at? s "(" (+ q 1))
         (let ((r (rh--index-char s #\) (+ q 2))))
           (and r (> r (+ q 2))
                (cons* (substring s (+ p 1) q) (substring s (+ q 2) r) (+ r 1)))))))

;;; \*\*([^*]+)\*\*  -> <strong>\1</strong>
(define (rh--strong-at s p)
  (and (rh--starts-at? s "**" p)
       (let ((q (rh--index-char s #\* (+ p 2))))
         (and q (> q (+ p 2)) (rh--starts-at? s "**" q)
              (cons (string-append "<strong>" (substring s (+ p 2) q) "</strong>")
                    (+ q 2))))))

;;; _(\[warrant:[^\]]*\])_  -> <em>\1</em>
(define (rh--warrant-at s p)
  (and (rh--starts-at? s "[warrant:" (+ p 1))
       (let ((q (rh--index-char s #\] (+ p 10))))
         (and q (rh--starts-at? s "_" (+ q 1))
              (cons (string-append "<em>" (substring s (+ p 1) (+ q 1)) "</em>")
                    (+ q 2))))))

;;; \*(\S|\S[^*]*?\S)\*  -> <em>\1</em>
(define (rh--em-at s p)
  (let ((n (string-length s)))
    (define (ns? i) (and (< i n) (not (rh--space? (string-ref s i)))))
    (define (star? i) (and (< i n) (char=? (string-ref s i) #\*)))
    (define (hit end) (cons (string-append "<em>" (substring s (+ p 1) end) "</em>") (+ end 1)))
    (and (ns? (+ p 1))
         (if (star? (+ p 2))
             (hit (+ p 2))                      ; \S alone
             ;; \S [^*]*? \S \*  : lazy, so end at the first j where it can
             (let loop ((j (+ p 2)))
               (cond ((>= j n) #f)
                     ((and (ns? j) (star? (+ j 1))) (hit (+ j 1)))
                     ((char=? (string-ref s j) #\*) #f)
                     (else (loop (+ j 1)))))))))

(define (rh--inline-special? c)
  (case c
    ((#\` #\[ #\* #\_ #\& #\< #\> #\" #\' #\x0) #t)
    (else #f)))

(define (rh--inline text)
  ;; one newline-free string of inline markdown -> HTML
  (or (rh--inline-simple text)
      (rh--inline-full text)))

(define (rh--inline-simple text)
  ;; The common case, done in one pass: outside its code spans TEXT holds
  ;; none of [ * _ & < > " ' NUL.  Then steps 2-4 of `rh--inline-full'
  ;; change nothing (they see only plain characters and placeholders), and
  ;; step 5 puts each span's HTML back where its placeholder was; so the
  ;; result is the text with each span replaced by its linkified HTML.
  ;; Returns #f when TEXT is not of this kind.
  (let ((n (string-length text)))
    (let loop ((i 0) (start 0) (pieces '()))
      (if (= i n)
          (cond ((null? pieces) text)
                (else (apply string-append
                             (reverse (cons (substring text start n) pieces)))))
          (let ((c (string-ref text i)))
            (cond ((char=? c #\`)
                   (let ((m (rh--code-span-at text i)))
                     (if m
                         (loop (cdr m) (cdr m)
                               (cons* (rh--linkify-code (car m))
                                      (substring text start i)
                                      pieces))
                         (loop (+ i 1) start pieces))))
                  ((rh--inline-special? c) #f)
                  (else (loop (+ i 1) start pieces))))))))

(define (rh--inline-full text)
  (let ((spans '()) (nspans 0) (code-at '()))
    (define (stash! frag code)
      (set! spans (cons frag spans))
      (if code (set! code-at (cons (cons nspans code) code-at)))
      (set! nspans (+ nspans 1))
      (rh--placeholder (- nspans 1)))
    ;; 1. code spans, cross-linked
    (let* ((text (rh--sub text #\`
                          (lambda (s p)
                            (let ((m (rh--code-span-at s p)))
                              (and m (cons (stash! (rh--linkify-code (car m)) (car m))
                                           (cdr m)))))))
           ;; 2. explicit links [label](href)
           (text (rh--sub text #\[
                          (lambda (s p)
                            (let ((m (rh--md-link-at s p)))
                              (and m
                                   (let* ((label (car m)) (href (cadr m))
                                          (pm (rh--placeholder-at label 0))
                                          (label
                                           (if (and pm (= (cdr pm) (string-length label))
                                                    (assv (car pm) code-at))
                                               (string-append "<code>"
                                                              (rh--esc (cdr (assv (car pm) code-at)))
                                                              "</code>")
                                               (rh--esc label))))
                                     (cons (stash! (string-append
                                                    "<a class=\"x\" href=\""
                                                    (rh--esc (rh--resolve-href href)) "\">"
                                                    label "</a>")
                                                   #f)
                                           (cddr m))))))))
           ;; 3. escape everything else
           (text (rh--esc text))
           ;; 4. emphasis
           (text (rh--sub text #\* rh--strong-at))
           (text (rh--sub text #\_ rh--warrant-at))
           (text (rh--sub text #\* rh--em-at)))
      ;; 5. restore placeholders
      (rh--restore text (list->vector (reverse spans))))))

(define (rh--inline-stmt text)
  ;; a formal statement verbatim: escape, the warrant tag, explicit links; no emphasis
  (let ((spans '()) (nspans 0))
    (define (stash! frag)
      (set! spans (cons frag spans))
      (set! nspans (+ nspans 1))
      (rh--placeholder (- nspans 1)))
    (let* ((text (rh--sub text #\[
                          (lambda (s p)
                            (let ((m (rh--md-link-at s p)))
                              (and m (cons (stash! (string-append
                                                    "<a class=\"x\" href=\"" (rh--esc (cadr m)) "\">"
                                                    (rh--esc (car m)) "</a>"))
                                           (cddr m)))))))
           (t (rh--esc text))
           (t (rh--sub t #\_ rh--warrant-at)))
      (rh--restore t (list->vector (reverse spans))))))

;;; --- block markdown ----------------------------------------------------

(define (rh--drop-empty-anchors text)
  ;; re.sub(r'<a id="[^"]*"></a>', "", text)
  (rh--sub text #\<
           (lambda (s p)
             (and (rh--starts-at? s "<a id=\"" p)
                  (let ((q (rh--index-char s #\" (+ p 7))))
                    (and q (rh--starts-at? s "\"></a>" q)
                         (cons "" (+ q 6))))))))

(define (rh--render-table rows)
  ;; rows: list of lists of cell strings
  (define (rule-cell? c)
    (let* ((c (if (rh--starts-at? c ":" 0) (substring c 1 (string-length c)) c))
           (c (if (string-suffix? ":" c) (substring c 0 (- (string-length c) 1)) c)))
      (and (>= (string-length c) 2)
           (= (rh--skip-char c #\- 0) (string-length c)))))
  (define (rule? row) (and (pair? row) (every rule-cell? row)))
  (let loop ((rs rows) (k 0) (head #f) (body '()))
    (if (pair? rs)
        (let ((row (car rs)))
          (if (rule? row)
              (if (= k 1)
                  (loop (cdr rs) (+ k 1) (car rows) '())
                  (loop (cdr rs) (+ k 1) head body))
              (loop (cdr rs) (+ k 1) head (cons row body))))
        (rh--concat
         (append
          (list "<div class=\"tw\"><table>")
          (if head
              (list (string-append
                     "<thead><tr>"
                     (rh--concat (map (lambda (c) (string-append "<th>" (rh--inline c) "</th>")) head))
                     "</tr></thead>"))
              '())
          (list "<tbody>")
          (map (lambda (row)
                 (string-append
                  "<tr>"
                  (rh--concat (map (lambda (c) (string-append "<td>" (rh--inline c) "</td>")) row))
                  "</tr>"))
               (reverse body))
          (list "</tbody></table></div>"))))))

(define (rh--render-list items)
  ;; items: list of (level inner id-or-#f) -> nested <ul>
  (let loop ((items items) (depth 0) (acc '()))
    (if (pair? items)
        (let* ((it (car items)) (lvl (car it)) (itid (caddr it)))
          (let close ((d depth) (acc acc))
            (if (> d (+ lvl 1))
                (close (- d 1) (cons "</ul>" acc))
                (let open ((d d) (acc acc))
                  (if (< d (+ lvl 1))
                      (open (+ d 1) (cons "<ul>" acc))
                      (loop (cdr items) d
                            (cons* "</li>" (cadr it)
                                   (if itid (string-append "<li id=\"" (rh--esc itid) "\">") "<li>")
                                   acc)))))))
        (let close ((d depth) (acc acc))
          (if (= d 0)
              (rh--concat-rev acc)
              (close (- d 1) (cons "</ul>" acc)))))))

(define (rh--md->html text docid used-ids)
  (define (claim idbase)
    (let loop ((cid idbase) (k 2))
      (if (hash-table-contains? used-ids cid)
          (loop (string-append idbase "-" (number->string k)) (+ k 1))
          (begin (hash-table-set! used-ids cid #t) cid))))
  (define (heading-id level raw)
    (let ((name (rh--strip (rh--strip-char (rh--strip raw) #\`))))
      (cond ((rh--in? rh--structs name) (claim name))
            ((and (string=? docid "DEFINITIONS") (= level 3)) (claim (string-append "d-" name)))
            ((and (string=? docid "PSS") (= level 3)) (claim (string-append "p-" name)))
            (else (claim (string-append docid "__" (rh--slug raw)))))))
  (define (table-line? l) (rh--starts-at? (rh--strip l) "|" 0))
  (let* ((lines (list->vector (rh--lines (rh--drop-empty-anchors text))))
         (n (vector-length lines))
         (out '()))
    (define (L i) (vector-ref lines i))
    (define (emit! s) (set! out (cons s out)))
    (let loop ((i 0))
      (if (< i n)
          (let* ((line (L i)) (stripped (rh--strip line)))
            (cond
             ((string-null? stripped) (loop (+ i 1)))
             ;; heading
             ((rh--heading-level line)
              => (lambda (level)
                   (let* ((raw (rh--strip (substring line level (string-length line))))
                          (hid (heading-id level raw))
                          (tag (string-append "h" (number->string (min (+ level 1) 6)))))
                     (emit! (string-append "<" tag " id=\"" (rh--esc hid) "\">"
                                           (rh--inline raw) "</" tag ">"))
                     (loop (+ i 1)))))
             ;; horizontal rule
             ((rh--hr? line) (emit! "<hr>") (loop (+ i 1)))
             ;; fenced code block: verbatim
             ((rh--starts-at? line "```" 0)
              (let gather ((j (+ i 1)) (buf '()))
                (if (and (< j n) (not (rh--starts-at? (L j) "```" 0)))
                    (gather (+ j 1) (cons (L j) buf))
                    (begin
                      (emit! (string-append "<pre>" (rh--esc (rh--rstrip (rh--join (reverse buf) "\n")))
                                            "</pre>"))
                      (loop (+ j 1))))))
             ;; indented code block (4+ spaces, not a list item)
             ((and (rh--indented-code? line) (not (rh--list-item line)))
              (let gather ((j i) (buf '()))
                (if (and (< j n)
                         (or (rh--blank? (L j)) (rh--four-spaces? (L j)))
                         (not (and (rh--blank? (L j))
                                   (not (and (< (+ j 1) n) (rh--four-spaces? (L (+ j 1))))))))
                    (gather (+ j 1)
                            (cons (if (rh--four-spaces? (L j))
                                      (substring (L j) 4 (string-length (L j)))
                                      (L j))
                                  buf))
                    (begin
                      (emit! (string-append "<pre>" (rh--esc (rh--rstrip (rh--join (reverse buf) "\n")))
                                            "</pre>"))
                      (loop j)))))
             ;; list (nesting by indent; continuation lines append to the item)
             ((rh--list-item line)
              (let gather ((j i) (items '()))   ; items reversed; each (lvl inner-list-reversed id)
                (define (finish j)
                  (emit! (rh--render-list
                          (reverse (map (lambda (it)
                                          (list (car it)
                                                (if (null? (cdr (cadr it)))
                                                    (car (cadr it))
                                                    (rh--concat (reverse (cadr it))))
                                                (caddr it)))
                                        items))))
                  (loop j))
                (if (>= j n)
                    (finish j)
                    (let ((lm (rh--list-item (L j))))
                      (cond
                       (lm
                        (let* ((lvl (quotient (car lm) 2))
                               (raw (substring (L j) (cdr lm) (string-length (L j))))
                               (stmt (rh--catalog-entry raw)))
                          (if (and stmt
                                   (string=? docid "THEOREMS")
                                   (string-suffix? "-rev" (car stmt))
                                   (rh--in? rh--thms (substring (car stmt) 0 (- (string-length (car stmt)) 4))))
                              (gather (+ j 1) items)
                              (let* ((name (and stmt (car stmt)))
                                     (body (and stmt (cdr stmt)))
                                     (itid (and stmt (string=? docid "THEOREMS") (rh--in? rh--thms name)
                                                (claim (string-append "t-" name))))
                                     (inner
                                      (cond ((not stmt) (rh--inline raw))
                                            (itid
                                             (let ((rev? (rh--in? rh--thms (string-append name "-rev"))))
                                               (string-append
                                                (if rev? (string-append "<a id=\"t-" (rh--esc name) "-rev\"></a>") "")
                                                "<code>" (rh--esc name) "</code>"
                                                (if rev?
                                                    " <span class=\"pm\" title=\"reverse (-rev) mirror folded in\">(\xb1;)</span>"
                                                    "")
                                                " \x2014; " (rh--inline-stmt body))))
                                            (else
                                             (string-append "<code>" (rh--esc name) "</code> \x2014; "
                                                            (rh--inline-stmt body))))))
                                (gather (+ j 1) (cons (list lvl (list inner) itid) items))))))
                       ((and (not (rh--blank? (L j)))
                             (not (rh--heading-level (L j)))
                             (not (rh--hr? (L j)))
                             (not (table-line? (L j)))
                             (pair? items))
                        (let ((it (car items)))
                          (gather (+ j 1)
                                  (cons (list (car it)
                                              (cons* (rh--inline (rh--strip (L j))) " " (cadr it))
                                              (caddr it))
                                        (cdr items)))))
                       (else (finish j)))))))
             ;; pipe table
             ((rh--starts-at? stripped "|" 0)
              (let gather ((j i) (rows '()))
                (if (and (< j n) (table-line? (L j)))
                    (gather (+ j 1)
                            (cons (map rh--strip
                                       (rh--split (rh--strip-char (rh--strip (L j)) #\|) #\|))
                                  rows))
                    (begin (emit! (rh--render-table (reverse rows)))
                           (loop j)))))
             ;; paragraph
             (else
              (let gather ((j i) (buf '()))
                (if (and (< j n)
                         (not (rh--blank? (L j)))
                         (not (rh--heading-level (L j)))
                         (not (rh--hr? (L j)))
                         (not (rh--list-item (L j)))
                         (not (table-line? (L j)))
                         (not (rh--indented-code? (L j))))
                    (gather (+ j 1) (cons (rh--strip (L j)) buf))
                    (begin
                      (emit! (string-append "<p>" (rh--inline (rh--join (reverse buf) " ")) "</p>"))
                      (loop j)))))))))
    (rh--join (reverse out) "\n")))

;;; `([^`]+)`\s*—\s*(.*)$  on a list item: (name . body) or #f
(define (rh--catalog-entry raw)
  (and (rh--starts-at? raw "`" 0)
       (let ((q (rh--index-char raw #\` 1)))
         (and q (> q 1)
              (let ((k (rh--skip-space raw (+ q 1))))
                (and (< k (string-length raw))
                     (char=? (string-ref raw k) #\x2014)
                     (let ((b (rh--skip-space raw (+ k 1))))
                       (cons (substring raw 1 q)
                             (substring raw b (string-length raw))))))))))

;;; --- shared chrome -----------------------------------------------------

(define rh--ref-css "
 :root { --ink:#1a2a3a; --accent:#2a4a6a; --accent2:#3f7fb0; --rule:#dde6f0;
         --bg:#eef3f9; --panel:#f5f8fc; }
 * { box-sizing:border-box; }
 body { font-family: Helvetica, Arial, sans-serif; color:var(--ink); margin:0;
        background:#fff; }
 #wrap { display:flex; align-items:flex-start; }
 nav { position:sticky; top:0; align-self:flex-start; min-width:14rem; width:14rem;
       height:100vh; overflow:auto; padding:1.2rem 1rem; background:var(--panel);
       border-right:1px solid var(--rule); box-sizing:border-box; }
 nav .home { font-size:1.05rem; font-weight:600; color:var(--accent);
             text-decoration:none; display:block; margin:.1rem 0 1rem; }
 nav .home:hover { text-decoration:underline; }
 nav a.doc { display:block; padding:.28rem .5rem; color:#33536f; text-decoration:none;
             border-radius:5px; font-size:.92rem; line-height:1.3; }
 nav a.doc:hover { background:#e3edf8; }
 nav a.doc.active { background:var(--accent); color:#fff; font-weight:600; }
 nav .extra { display:block; margin-top:1.2rem; padding-top:.8rem;
              border-top:1px solid var(--rule); }
 /* min-width:0 lets this flex child shrink below its content's intrinsic
    width; without it a wide <pre> formula forces main past the viewport. */
 main { padding:1.6rem 2.4rem 3rem; max-width:62rem; min-width:0; flex:1 1 auto; }
 h1.page { color:var(--accent); font-size:1.9rem; margin:.2rem 0 .1rem;
           background:linear-gradient(95deg,#2a4a6a 0%,#3f7fb0 60%,#b06a00 100%);
           -webkit-background-clip:text; background-clip:text; color:transparent; }
 .page-sub { color:#667; margin:.1rem 0 1.6rem; font-size:1.02rem; }
 h2 { color:var(--accent); border-bottom:2px solid #e3edf8; padding-bottom:.2rem;
      margin-top:2.2rem; }
 h3,h4,h5,h6 { color:#365b7d; margin:.9rem 0 .25rem; }
 :target { background:#fff4e0; box-shadow:-.5rem 0 0 #fff4e0, .3rem 0 0 #fff4e0; }
 [id] { scroll-margin-top: .6rem; }
 code { background:#f2f6fb; padding:0 .25rem; border-radius:3px;
        font-family: ui-monospace, Menlo, Consolas, monospace; font-size:.92em;
        overflow-wrap:anywhere; }
 pre { background:#f7f9fc; border:1px solid #e6edf6; border-radius:6px;
       padding:.6rem .8rem; font-size:.86rem;
       white-space:pre-wrap; overflow-wrap:anywhere; }
 li, p { overflow-wrap:anywhere; }
 a.x { text-decoration:none; }
 a.x:hover code { background:#dbe9fb; }
 .pm { color:#9aa7b4; font-size:.85em; cursor:help; }
 ul { margin:.3rem 0; }
 li { margin:.12rem 0; }
 hr { border:0; border-top:1px solid #e6edf6; margin:1.2rem 0; }
 /* .tw scrolls a wide table on its own instead of pushing the page sideways */
 .tw { overflow-x:auto; margin:.9rem 0; }
 .tw table { border-collapse:collapse; font-size:.9rem; width:100%; }
 .tw th, .tw td { border:1px solid var(--rule); padding:.3rem .55rem;
                  text-align:left; vertical-align:top; }
 .tw th { background:var(--panel); color:var(--accent); font-weight:600;
          white-space:nowrap; }
 .tw tbody tr:nth-child(even) { background:#fafcfe; }
 .tw td code { background:transparent; padding:0; }
 .lead { color:#667; }
 /* hub */
 .hub main { max-width:54rem; }
 .hub-grid { display:grid; grid-template-columns:repeat(auto-fit,minmax(15rem,1fr));
             gap:.9rem; margin:1.4rem 0; }
 a.card { display:block; background:#fff; border:1px solid var(--rule);
          border-radius:10px; padding:.9rem 1.1rem; text-decoration:none;
          color:inherit; transition:border-color .12s, box-shadow .12s; }
 a.card:hover { border-color:var(--accent2);
                box-shadow:0 2px 10px rgba(42,74,106,.10); }
 a.card .t { color:var(--accent); font-weight:600; font-size:1.05rem; }
 a.card .b { color:#667; font-size:.9rem; margin-top:.2rem; line-height:1.4; }
")

(define (rh--present-docs)
  ;; the DOCS entries whose file is present and non-empty
  (filter (lambda (d) (not (string-null? (rh--doc-text (cadr d))))) rh--docs))

(define (rh--sidebar active-secid)
  (rh--concat
   (append
    (list "<a class=\"home\" href=\"reference.html\">&#8962; VNB reference</a>")
    (map (lambda (d)
           (let ((secid (rh--secid (cadr d))))
             (string-append "<a class=\""
                            (if (equal? secid active-secid) "doc active" "doc")
                            "\" href=\"" (rh--esc (rh--page-of secid)) "\">"
                            (rh--esc (car d)) "</a>")))
         (rh--present-docs))
    (list "<a class=\"doc extra\" href=\"structure-graph.html\">Structure graph &#8599;</a>"))))

(define (rh--page-html title active-secid body body-class)
  (string-append "<!DOCTYPE html>
<html lang=\"en\"><head><meta charset=\"utf-8\">
<title>" (rh--esc title) " &mdash; VNB reference</title>
<style>" rh--ref-css "</style></head><body"
                 (if body-class (string-append " class=\"" body-class "\"") "") ">
<div id=\"wrap\">
<nav>" (rh--sidebar active-secid) "</nav>
<main>" body "</main>
</div></body></html>
"))

(define (build-reference-html #!optional out-dir in-dir)
  (let ((odir (rh--dir out-dir)))
    (set! rh--in-dir (rh--dir in-dir))
    (set! rh--file-cache (make-string-hash-table))
    (set! rh--structs (rh--set-of (rh--structure-names)))
    (set! rh--thms (rh--set-of (rh--theorem-names)))
    (set! rh--defs (rh--set-of (rh--heading3-names "DEFINITIONS.md")))
    (set! rh--pss (rh--set-of (rh--heading3-names "PSS.md")))
    (set! rh--doc-anchors (make-string-hash-table))
    (set! rh--current-docid #f)
    (set! rh--current-page #f)
    ;; anchors first: a link may point FORWARD, to a doc not yet rendered
    (for-each (lambda (d)
                (let ((secid (rh--secid (cadr d))))
                  (hash-table-set! rh--doc-anchors secid
                                   (rh--prescan-anchors secid (rh--doc-text (cadr d))))))
              (rh--present-docs))
    (let* ((written
            (map (lambda (d)
                   (let* ((title (car d)) (fname (cadr d)) (blurb (caddr d))
                          (secid (rh--secid fname))
                          (page (rh--page-of secid))
                          (body (rh--join
                                 (append
                                  (list (string-append "<h1 class=\"page\">" (rh--esc title) "</h1>")
                                        (string-append "<p class=\"page-sub\">" (rh--esc blurb) " "
                                                       "<span class=\"lead\">&mdash; " (rh--esc fname)
                                                       "</span></p>"))
                                  (if (string=? secid "STRUCTURE-INDEX")
                                      (list "<p class=\"lead\">See the clickable <a href=\"structure-graph.html\">structure graph</a> &mdash; refines &amp; view-as relations, with every node a link.</p>")
                                      '())
                                  (list (begin
                                          (set! rh--current-page page)
                                          (set! rh--current-docid secid)
                                          (rh--md->html (rh--doc-text fname) secid
                                                        (make-string-hash-table)))))
                                 "\n")))
                     (rh--write (string-append odir page)
                                (rh--page-html title secid body #f))))
                 (rh--present-docs)))
           (hub (string-append odir "reference.html"))
           (cards (append
                   (map (lambda (d)
                          (string-append "<a class=\"card\" href=\""
                                         (rh--esc (rh--page-of (rh--secid (cadr d)))) "\">"
                                         "<div class=\"t\">" (rh--esc (car d)) "</div>"
                                         "<div class=\"b\">" (rh--esc (caddr d)) "</div></a>"))
                        (rh--present-docs))
                   (list "<a class=\"card\" href=\"structure-graph.html\"><div class=\"t\">Structure graph &#8599;</div><div class=\"b\">refines &amp; view-as relations, every node clickable</div></a>")))
           (hub-body (string-append
                      "<h1 class=\"page\">VNB library reference</h1>"
                      "<p class=\"page-sub\">The installed library, one page per index. "
                      "Every backticked name links to where it is stated.</p>"
                      "<div class=\"hub-grid\">" (rh--concat cards) "</div>")))
      (set! rh--current-page "reference.html")
      (rh--write hub (rh--page-html "VNB library reference" #f hub-body "hub"))
      (display (string-append "wrote " hub " (hub) + " (number->string (length written))
                              " doc pages"))
      (newline)
      (display (string-append "  (" (number->string (length (hash-table-keys rh--structs))) " structures, "
                              (number->string (length (hash-table-keys rh--thms))) " theorem ids, "
                              (number->string (length (hash-table-keys rh--defs))) " defs, "
                              (number->string (length (hash-table-keys rh--pss))) " pss)"))
      (newline)
      (set! rh--file-cache #f)
      (cons hub written))))
