(module csp *
(import chicken scheme extras)
(use nondeterminism define-structure srfi-1 traversal)

(define-structure domain-variable domain before-demons after-demons)
(define  *csp-strategy* 'ac)

(define (create-domain-variable domain)
 (when (null? domain) (fail))
 (make-domain-variable domain '() '()))

(define (attach-before-demon! demon x)
 (local-set-domain-variable-before-demons!
  x (cons demon (domain-variable-before-demons x)))
 (demon))

(define (attach-after-demon! demon x)
 (local-set-domain-variable-after-demons!
  x (cons demon (domain-variable-after-demons x)))
 (demon))

(define (restrict-domain! x domain)
 (when (null? domain) (fail))
 (when (< (length domain) (length (domain-variable-domain x)))
  (for-each (lambda (demon) (demon)) (domain-variable-before-demons x))
  (local-set-domain-variable-domain! x domain)
  (for-each (lambda (demon) (demon)) (domain-variable-after-demons x))))

(define (bound? x) (null? (rest (domain-variable-domain x))))

(define (binding x) (first (domain-variable-domain x)))

(define (csp-solution domain-variables select)
 (let loop ((domain-variables domain-variables))
  (let ((domain-variables (remove-if bound? domain-variables)))
   (unless (null? domain-variables)
    (let* ((x (select domain-variables))
	   (value (a-member-of (domain-variable-domain x))))
     (restrict-domain! x (list value))
     (loop (removeq x domain-variables))))))
 (map binding domain-variables))

(define (standard-csp-startup)
 (set! *pause?* #f)
 (set-fail! (lambda () (set! *fail?* #t))))
(define (unwind) (unwind-trail))

(define (assert-unary-constraint-gfc! constraint x)
 (restrict-domain!
  x (remove-if-not (lambda (xe) (constraint xe))
		   (domain-variable-domain x))))

(define (assert-binary-constraint-gfc! constraint x y)
 (attach-after-demon!
  (lambda ()
   (when (bound? x)
    (restrict-domain!
     y (remove-if-not (lambda (ye) (constraint (binding x) ye))
		      (domain-variable-domain y)))))
  x)
 (attach-after-demon!
  (lambda ()
   (when (bound? y)
    (restrict-domain!
     x (remove-if-not (lambda (xe) (constraint xe (binding y)))
		      (domain-variable-domain x)))))
  y))

(define (assert-ternary-constraint-gfc! constraint x y z)
 (attach-after-demon!
  (lambda ()
   (when (and (null? (rest (domain-variable-domain x)))
            (null? (rest (domain-variable-domain z))))
    (let ((xe (first (domain-variable-domain x)))
	  (ze (first (domain-variable-domain z))))
     (restrict-domain!
      y
      (remove-if-not (lambda (ye) (constraint xe ye ze))
		     (domain-variable-domain y)))))
   (when (and (null? (rest (domain-variable-domain x)))
            (null? (rest (domain-variable-domain y))))
    (let ((xe (first (domain-variable-domain x)))
	  (ye (first (domain-variable-domain y))))
     (restrict-domain!
      z
      (remove-if-not (lambda (ze) (constraint xe ye ze))
		     (domain-variable-domain z))))))
  x)
 (attach-after-demon!
  (lambda ()
   (when (and (null? (rest (domain-variable-domain y)))
            (null? (rest (domain-variable-domain z))))
    (let ((ye (first (domain-variable-domain y)))
	  (ze (first (domain-variable-domain z))))
     (restrict-domain!
      x
      (remove-if-not (lambda (xe) (constraint xe ye ze))
		     (domain-variable-domain x)))))
   (when (and (null? (rest (domain-variable-domain y)))
            (null? (rest (domain-variable-domain x))))
    (let ((ye (first (domain-variable-domain y)))
	  (xe (first (domain-variable-domain x))))
     (restrict-domain!
      z
      (remove-if-not (lambda (ze) (constraint xe ye ze))
		     (domain-variable-domain z))))))
  y)
 (attach-after-demon!
  (lambda ()
   (when (and (null? (rest (domain-variable-domain z)))
            (null? (rest (domain-variable-domain x))))
    (let ((ze (first (domain-variable-domain z)))
	  (xe (first (domain-variable-domain x))))
     (restrict-domain!
      y
      (remove-if-not (lambda (ye) (constraint xe ye ze))
		     (domain-variable-domain y)))))
   (when (and (null? (rest (domain-variable-domain z)))
            (null? (rest (domain-variable-domain y))))
    (let ((ze (first (domain-variable-domain z)))
	  (ye (first (domain-variable-domain y))))
     (restrict-domain!
      x
      (remove-if-not (lambda (xe) (constraint xe ye ze))
		     (domain-variable-domain x))))))
  z))

(define (assert-unary-constraint-ac! constraint x)
 (restrict-domain!
  x (remove-if-not (lambda (xe) (constraint xe))
		   (domain-variable-domain x))))


(define (assert-binary-constraint-ac! constraint x y)
 (attach-after-demon!
  (lambda ()
   (restrict-domain!
    y (remove-if-not (lambda (ye)
		      (some (lambda (xe) (constraint xe ye))
			    (domain-variable-domain x)))
		     (domain-variable-domain y))))
  x)
 (attach-after-demon!
  (lambda ()
   (restrict-domain!
    x (remove-if-not (lambda (xe)
		      (some (lambda (ye) (constraint xe ye))
			    (domain-variable-domain y)))
		     (domain-variable-domain x))))
  y))

(define (assert-ternary-constraint-ac! constraint x y z)
 (attach-after-demon!
  (lambda ()
   (restrict-domain!
    y
    (remove-if-not
     (lambda (ye)
      (some (lambda (ze)
	     (some (lambda (xe) (constraint xe ye ze))
		   (domain-variable-domain x)))
	    (domain-variable-domain z)))
     (domain-variable-domain y)))
   (restrict-domain!
    z
    (remove-if-not
     (lambda (ze)
      (some (lambda (ye)
	     (some (lambda (xe) (constraint xe ye ze))
		   (domain-variable-domain x)))
	    (domain-variable-domain y)))
     (domain-variable-domain z))))
  x)
 (attach-after-demon!
  (lambda ()
   (restrict-domain!
    x
    (remove-if-not
     (lambda (xe)
      (some (lambda (ze)
	     (some (lambda (ye) (constraint xe ye ze))
		   (domain-variable-domain y)))
	    (domain-variable-domain z)))
     (domain-variable-domain x)))
   (restrict-domain!
    z
    (remove-if-not
     (lambda (ze)
      (some (lambda (xe)
	     (some (lambda (ye) (constraint xe ye ze))
		   (domain-variable-domain y)))
	    (domain-variable-domain x)))
     (domain-variable-domain z))))
  y)
 (attach-after-demon!
  (lambda ()
   (restrict-domain!
    x
    (remove-if-not
     (lambda (xe)
      (some (lambda (ye)
	     (some (lambda (ze) (constraint xe ye ze))
		   (domain-variable-domain z)))
	    (domain-variable-domain y)))
     (domain-variable-domain x)))
   (restrict-domain!
    y
    (remove-if-not
     (lambda (ye)
      (some (lambda (xe)
	     (some (lambda (ze) (constraint xe ye ze))
		   (domain-variable-domain z)))
	    (domain-variable-domain x)))
     (domain-variable-domain y))))
  z))

(define (assert-unary-constraint-efd! constraint x)
 (attach-after-demon!
  (lambda () (when (bound? x) (unless (constraint (binding x)) (fail))))
  x))

(define (assert-binary-constraint-efd! constraint x y)
 (for-each
   (lambda (v)
    (attach-after-demon!
     (lambda ()
      (when (and (bound? x) (bound? y))
       (unless (constraint (binding x) (binding y)) (fail))))
     v))
  (list x y)))

(define (assert-ternary-constraint-efd! constraint x y z)
 (for-each
   (lambda (v)
    (attach-after-demon!
     (lambda ()
      (when (and (bound? x) (bound? y) (bound? z))
       (unless (constraint (binding x) (binding y) (binding z)) (fail))))
     v))
  (list x y z)))

(define (assert-unary-constraint-fc! constraint x)
 (attach-after-demon!
  (lambda ()
   (unless (some (lambda (xe) (constraint xe)) (domain-variable-domain x))
    (fail)))
  x))

(define (assert-binary-constraint-fc! constraint x y)
 (for-each
   (lambda (v)
    (attach-after-demon!
     (lambda ()
      (when (bound? x)
       (unless (some (lambda (ye) (constraint (binding x) ye))
                     (domain-variable-domain y))
        (fail)))
      (when (bound? y)
       (unless (some (lambda (xe) (constraint xe (binding y)))
                     (domain-variable-domain x))
        (fail))))
     v))
  (list x y)))

(define (assert-ternary-constraint-fc! constraint x y z)
 (for-each
   (lambda (v)
    (attach-after-demon!
     (lambda ()
      (when (and (bound? x) (bound? y))
       (unless (some (lambda (ze) (constraint (binding x) (binding y) ze))
                     (domain-variable-domain z))
        (fail)))
      (when (and (bound? x) (bound? z))
       (unless (some (lambda (ye) (constraint (binding x) ye (binding z)))
                     (domain-variable-domain y))
        (fail)))
      (when (and (bound? y) (bound? z))
       (unless (some (lambda (xe) (constraint xe (binding y) (binding z)))
                     (domain-variable-domain x))
        (fail))))
     v))
  (list x y z)))

(define (assert-unary-constraint-vp! constraint x)
 (attach-after-demon!
  (lambda ()
   (when (one (lambda (xe) (constraint xe)) (domain-variable-domain x))
    (restrict-domain! x (list (find-if (lambda (xe) (constraint xe))
				       (domain-variable-domain x))))))
  x))

(define (assert-binary-constraint-vp! constraint x y)
 (for-each
   (lambda (v)
    (attach-after-demon!
     (lambda ()
      (when (bound? x)
       (when (one (lambda (ye) (constraint (binding x) ye))
                  (domain-variable-domain y))
        (restrict-domain!
         y (list (find-if (lambda (ye) (constraint (binding x) ye))
                          (domain-variable-domain y))))))
      (when (bound? y)
       (when (one (lambda (xe) (constraint xe (binding y)))
                  (domain-variable-domain x))
        (restrict-domain!
         x (list (find-if (lambda (xe) (constraint xe (binding y)))
                          (domain-variable-domain x)))))))
     v))
  (list x y)))

(define (assert-ternary-constraint-vp! constraint x y z)
 (for-each
   (lambda (v)
    (attach-after-demon!
     (lambda ()
      (when (and (bound? x) (bound? y))
       (when (one (lambda (ze) (constraint (binding x) (binding y) ze))
                  (domain-variable-domain z))
        (restrict-domain!
         z (list (find-if (lambda (ze) (constraint (binding x) (binding y) ze))
                          (domain-variable-domain z))))))
      (when (and (bound? x) (bound? z))
       (when (one (lambda (ye) (constraint (binding x) ye (binding z)))
                  (domain-variable-domain y))
        (restrict-domain!
         y (list (find-if (lambda (ye) (constraint (binding x) ye (binding z)))
                          (domain-variable-domain y))))))
      (when (and (bound? y) (bound? z))
       (when (one (lambda (xe) (constraint xe (binding y) (binding z)))
                  (domain-variable-domain x))
        (restrict-domain!
         x (list (find-if (lambda (xe) (constraint xe (binding y) (binding z)))
                          (domain-variable-domain x)))))))
     v))
  (list x y z)))

(define (assert-constraint! constraint domain-variables)
 (case *csp-strategy*
  ((efd)
   (case (length domain-variables)
    ((1) (assert-unary-constraint-efd! constraint (first domain-variables)))
    ((2) (assert-binary-constraint-efd!
          constraint (first domain-variables) (second domain-variables)))
    ((3) (assert-ternary-constraint-efd! constraint
                                         (first domain-variables)
                                         (second domain-variables)
                                         (third domain-variables)))
    (else (assert-constraint-efd! constraint domain-variables))))
  ((fc)
   (case (length domain-variables)
    ((1) (assert-unary-constraint-fc! constraint (first domain-variables)))
    ((2) (assert-binary-constraint-fc!
          constraint (first domain-variables) (second domain-variables)))
    ((3) (assert-ternary-constraint-fc! constraint
                                        (first domain-variables)
                                        (second domain-variables)
                                        (third domain-variables)))
    (else (assert-constraint-fc! constraint domain-variables))))
  ((vp)
   (case (length domain-variables)
    ((1) (assert-unary-constraint-vp! constraint (first domain-variables)))
    ((2) (assert-binary-constraint-vp!
          constraint (first domain-variables) (second domain-variables)))
    ((3) (assert-ternary-constraint-vp! constraint
                                        (first domain-variables)
                                        (second domain-variables)
                                        (third domain-variables)))
    (else (assert-constraint-vp! constraint domain-variables))))
  ((gfc)
   (case (length domain-variables)
    ((1) (assert-unary-constraint-gfc! constraint (first domain-variables)))
    ((2) (assert-binary-constraint-gfc!
          constraint (first domain-variables) (second domain-variables)))
    ((3) (assert-ternary-constraint-gfc! constraint
                                         (first domain-variables)
                                         (second domain-variables)
                                         (third domain-variables)))
    (else (assert-constraint-gfc! constraint domain-variables))))
  ((ac)
   (case (length domain-variables)
    ((1) (assert-unary-constraint-ac! constraint (first domain-variables)))
    ((2) (assert-binary-constraint-ac!
          constraint (first domain-variables) (second domain-variables)))
    ((3) (assert-ternary-constraint-ac! constraint
                                        (first domain-variables)
                                        (second domain-variables)
                                        (third domain-variables)))
    (else (assert-constraint-ac! constraint domain-variables))))
  (else (error "Unrecognized strategy"))))

(define (assert-constraint-efd! constraint xs)
 (for-each
   (lambda (x)
    (attach-after-demon!
     (lambda ()
      (when (every bound? xs)
       (unless (apply constraint (map binding xs)) (fail))))
     x))
  xs))

(define (assert-constraint-fc! constraint xs)
 (for-each
   (lambda (x)
    (attach-after-demon!
     (lambda ()
      (when (one (lambda (x) (not (bound? x))) xs)
       (let* ((i (position-if (lambda (x) (not (bound? x))) xs))
              (x (list-ref xs i)))
        (unless (some
                 (lambda (xe)
                  (apply
                   constraint
                   (map-indexed (lambda (x j) (if (= j i) xe (binding x))) xs)))
                 (domain-variable-domain x))
         (fail)))))
     x))
  xs))

(define (assert-constraint-vp! constraint xs)
 (for-each
   (lambda (x)
    (attach-after-demon!
     (lambda ()
      (when (one (lambda (x) (not (bound? x))) xs)
       (let* ((i (position-if (lambda (x) (not (bound? x))) xs))
              (x (list-ref xs i)))
        (when (one
               (lambda (xe)
                (apply
                 constraint
                 (map-indexed (lambda (x j) (if (= j i) xe (binding x))) xs)))
               (domain-variable-domain x))
         (restrict-domain!
          x
          (list
           (find-if
            (lambda (xe)
             (apply constraint
                    (map-indexed (lambda (x j) (if (= j i) xe (binding x))) xs)))
            (domain-variable-domain x))))))))
     x))
  xs))

(define (assert-constraint-gfc! constraint xs)
 (for-each
   (lambda (x)
    (attach-after-demon!
     (lambda ()
      (when (one (lambda (x) (not (bound? x))) xs)
       (let* ((i (position-if (lambda (x) (not (bound? x))) xs))
              (x (list-ref xs i)))
        (restrict-domain!
         x
         (remove-if-not
          (lambda (xe)
           (apply constraint
                  (map-indexed (lambda (x j) (if (= j i) xe (binding x))) xs)))
          (domain-variable-domain x))))))
     x))
  xs))

(define (assert-constraint-ac! constraint ds)
 (for-each-indexed
  (lambda (d k)
   (attach-after-demon!
    (lambda ()
     (for-each-indexed
      (lambda (d i)
       (unless (= i k)
	(restrict-domain!
	 d
	 (remove-if-not
	  (lambda (x)
	   (let loop ((ds ds) (xs '()) (j 0))
	    (if (null? ds)
		(apply constraint (reverse xs))
		(if (= j i)
		    (loop (rest ds) (cons x xs) (+ j 1))
		    (some (lambda (e) (loop (rest ds) (cons e xs) (+ j 1)))
			  (domain-variable-domain (first ds)))))))
	  (domain-variable-domain d)))))
      ds))
    d))
  ds))

;;; For QobiScheme compatibility

(define-structure logic-variable binding name noticers)

(define *logic-variable-counter* -1)

(define (create-logic-variable)
 (set! *logic-variable-counter* (+ *logic-variable-counter* 1))
 (let ((v (make-logic-variable
	   #f
	   (string->uninterned-symbol
	    (format #f "?~s" *logic-variable-counter*))
	   '())))
  (set-logic-variable-binding! v v)
  v))

(define (attach-noticer! x noticer)
 (cond ((logic-variable? x)
	(cond
	 ((eq? (logic-variable-binding x) x)
	  (local-set-logic-variable-noticers!
	   x (cons noticer (logic-variable-noticers x)))
	  (noticer))
	 (else (attach-noticer! (logic-variable-binding x) noticer))))
       ((pair? x)
	(attach-noticer! (car x) noticer)
	(attach-noticer! (cdr x) noticer))
       ((vector? x)
	(for-each-n (lambda (i) (attach-noticer! (vector-ref x i) noticer))
		    (vector-length x)))))

(define (value-of x)
 (cond ((logic-variable? x)
	(if (eq? (logic-variable-binding x) x)
	    x
	    (value-of (logic-variable-binding x))))
       ((pair? x) (cons (value-of (car x)) (value-of (cdr x))))
       ((vector? x) (map-vector value-of x))
       (else x)))

(define (ground? x)
 (cond ((logic-variable? x)
	(and (not (eq? (logic-variable-binding x) x))
	     (ground? (logic-variable-binding x))))
       ((pair? x) (and (ground? (car x)) (ground? (cdr x))))
       ((vector? x)
	(every-n (lambda (i) (ground? (vector-ref x i))) (vector-length x)))
       (else #t)))

(define (known?-equalv x y)
 (or (eq? x y)
     (eqv? x y)
     (and (logic-variable? x)
	  (not (eq? (logic-variable-binding x) x))
	  (known?-equalv (logic-variable-binding x) y))
     (and (logic-variable? y)
	  (not (eq? (logic-variable-binding y) y))
	  (known?-equalv x (logic-variable-binding y)))
     (and (pair? x)
	  (pair? y)
	  (known?-equalv (car x) (car y))
	  (known?-equalv (cdr x) (cdr y)))
     (and (not (logic-variable? x))
	  (not (logic-variable? y))
	  (vector? x)
	  (vector? y)
	  (= (vector-length x) (vector-length y))
	  (every-n
	   (lambda (i) (known?-equalv (vector-ref x i) (vector-ref y i)))
	   (vector-length x)))))

(define (assert!-equalv x y)
 (cond
  ((logic-variable? x)
   (cond ((and (logic-variable? y) (not (eq? (logic-variable-binding y) y)))
	  (assert!-equalv x (logic-variable-binding y)))
	 ((eq? (logic-variable-binding x) x)
	  (let loop ((y y))
	   (when (eq? x y) (fail))
	   (cond
	    ((logic-variable? y)
	     (unless (eq? (logic-variable-binding y) y)
	      (loop (logic-variable-binding y))))
	    ((pair? y) (loop (car y)) (loop (cdr y)))
	    ((vector? y) (for-each-n (lambda (i) (loop (vector-ref y i)))
				     (vector-length y)))))
	  (local-set-logic-variable-binding! x y)
	  (for-each (lambda (noticer) (noticer) (attach-noticer! y noticer))
		    (logic-variable-noticers x)))
	 (else (assert!-equalv (logic-variable-binding x) y))))
  ((logic-variable? y) (assert!-equalv y x))
  ((and (pair? x) (pair? y))
   (assert!-equalv (car x) (car y))
   (assert!-equalv (cdr x) (cdr y)))
  ((and (vector? x) (vector? y) (= (vector-length x) (vector-length y)))
   (for-each-n (lambda (i) (assert!-equalv (vector-ref x i) (vector-ref y i)))
	       (vector-length x)))
  ((not (eqv? x y)) (fail))))

(define (assert!-notv-equalv x y)
 (when (known?-equalv x y) (fail))
 (attach-noticer! x (lambda () (when (known?-equalv x y) (fail))))
 (attach-noticer! y (lambda () (when (known?-equalv x y) (fail)))))
)
