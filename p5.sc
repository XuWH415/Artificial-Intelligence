(define (attacks? qi qj delta-rows)
	(or (= qi qj) (= (abs (- qi qj)) (abs delta-rows)))
)

(define (for-each-indexed p l)
	(define (loop l i)
		(unless (null? l)
			(p (first l) i)
			(loop (rest l) (+ i 1))
		)
	)
	(loop l 0)
)

(define (check-queens new-column old-columns)
	(for-each-indexed
		(lambda (old-column i)
			(when (attacks? new-column old-column (+ i 1))
				(fail)
			)
		)
		old-columns
	)
)

(define (n-queens n)
	(define (loop columns)
		(if (= (length columns) n)
			columns
			(let ((column (an-integer-between 0 (- n 1))))
				(check-queens column columns)
				(place-queen (length columns) column)
				(loop (cons column columns))
			)
		)
	)
	(loop '())
)

(define (place-n-queens-by-backtracking N)
	(n-queens N)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;--------------------------------------------------------------------------------------;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (range start end row)
	(if (>= start end)
		'()
		(cons (list row start) (range (+ start 1) end row))
	)
)

(define (create-n-variables n dn)
	(if (equal? 0 n)
		'()
		(cons (create-domain-variable (range 0 dn (- n 1))) (create-n-variables (- n 1) dn))
	)
)

(define (not-attack? vi vj)
	(not (attacks? (second vi) (second vj) (- (first vi) (first vj))))
)

(define (place-n-queens-by-constraints n)
	;;; create n variables
	(let ((vars (reverse (create-n-variables n n))))
		;;; attack before-demon: print variable
		(for-each
			(lambda (var)
				(attach-after-demon!
					(lambda ()
						(when (bound? var)
							(place-queen (first (binding var)) (second (binding var)))
						)
					)
					var
				)
			)
			vars
		)
		;;; nested loop
		(define (loop vars constraint)
			(unless (null? vars)
				(define (loop2 var rest-vars constraint)
					(unless (null? rest-vars)
						(assert-constraint! constraint (list var (first rest-vars)))
						(loop2 var (rest rest-vars) constraint)
					)
				)
				(loop2 (first vars) (rest vars) constraint)
				(loop (rest vars) constraint)
			)
		)
		(loop vars not-attack?)
		;;; find solution
		(csp-solution vars first)
	)
	;;;
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;--------------------------------------------------------------------------------------;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (assert-unary-constraint-gfc! constraint x)
	(attach-after-demon!
		(lambda ()
			(restrict-domain!
				x
				(remove-if
					(lambda (xe) (not (constraint xe)))
					(domain-variable-domain x)
				)
			)
		)
		x
	)
)

(define (assert-binary-constraint-gfc! constraint x y)
	(for-each
		(lambda (v)
			(attach-after-demon!
				(lambda ()
					(when (bound? x)
						(restrict-domain!
							y
							(remove-if
								(lambda (ye) (not (constraint (binding x) ye)))
								(domain-variable-domain y)
							)
						)
					)
					(when (bound? y)
						(restrict-domain!
							x
							(remove-if
								(lambda (xe) (not (constraint xe (binding y))))
								(domain-variable-domain x)
							)
						)
					)
				)
				v
			)
		)
		(list x y)
	)
)

(define (assert-unary-constraint-ac! constraint x)
	(attach-after-demon!
		(lambda ()
			(restrict-domain!
				x
				(remove-if
					(lambda (xe) (not (constraint xe)))
					(domain-variable-domain x)
				)
			)
		)
		x
	)
)

(define (arc-restrict dx dy constraint) ;;; narrow down the domain of y (dy)
	(if (null? dy)
		'()
		(if (some (lambda (d) (constraint d (first dy))) dx)
			(cons (first dy) (arc-restrict dx (rest dy) constraint))
			(arc-restrict dx (rest dy) constraint)
		)
	)
)

(define (assert-binary-constraint-ac! constraint x y)
	(for-each
		(lambda (v)
			(attach-after-demon!
				(lambda ()
					(restrict-domain!
						x
						(arc-restrict (domain-variable-domain y) (domain-variable-domain x) constraint)
					)
				)
				v
			)
			(attach-after-demon!
				(lambda ()
					(restrict-domain!
						y
						(arc-restrict (domain-variable-domain x) (domain-variable-domain y) constraint)
					)
				)
				v
			)
		)
		(list x y)
	)
)







