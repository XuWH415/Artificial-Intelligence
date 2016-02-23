;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (initial-board n)
	(cond 
		((equal? n 0) '())
		((equal? n 1) '((0)))
		(else (map (lambda (x) (cons (first x) x)) (cons (first (initial-board (- n 1))) (initial-board (- n 1)))))
	)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (get-num l)
	(if (null? l) 0 (+ 1 (get-num (rest l))))
)

(define (gen-ref ir row)
	(if (null? row)
		'()
		(if (equal? (first row) 0)
			(cons (list ir (get-num row)) (gen-ref ir (rest row)))
			(gen-ref ir (rest row))
		)
	)
)

(define (moves b)
	(if (null? b)
		'()
		(append (gen-ref (get-num b) (first b)) (moves (rest b)))
	)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (player-to-move b)
	(if (equal? (map-reduce + 0 (lambda (row) (map-reduce + 0 (lambda (x) (if (equal? x 1) 1 0)) row)) b) (map-reduce + 0 (lambda (row) (map-reduce + 0 (lambda (x) (if (equal? x -1) 1 0)) row)) b))
		1
		-1
	)
)

(define (set-position k l v)
	(if (equal? k (get-num l))
		(cons v (rest l))
		(cons (first l) (set-position k (rest l) v))
	)
)

(define (replace-value m b v)
	(if (equal? (first m) (get-num b))
		(cons (set-position (second m) (first b) v) (rest b))
		(cons (first b) (replace-value m (rest b) v))
	)
)

(define (make-move m b)
	(replace-value m b (player-to-move b))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(Define (Or-Procedure X Y) (Or X Y))

(Define (And-Procedure X Y) (And X Y))

(Define (In? E L)
	(If (Null? L) #F (If (Equal? E (First L)) #T (In? E (Rest L))))
)

(define (initial-list n v)
	(cond
		((equal? n 0) '())
		((equal? n 1) (list v))
		(else (cons v (initial-list (- n 1) v)))
	)
)

(define (add-list l1 l2)
	(cond 
		((number? l1) (+ l1 l2))
		((null? l1) '())
		(else (cons (add-list (first l1) (first l2)) (add-list (rest l1) (rest l2))))
	)
)

(define (get-position k l)
	(if (equal? k (get-num l))
		(first l)
		(get-position k (rest l))
	)
)

(define (diagonal-sum n b)
	(if (equal? n 1)
		(get-position 1 (get-position 1 b))
		(+ (get-position n (get-position n b)) (diagonal-sum (- n 1) b))
	)
)

(define (back-diagonal-sum n b)
	(if (equal? n 1)
		(get-position (- (+ (get-num b) 1) n) (get-position n b))
		(+ (get-position (- (+ (get-num b) 1) n) (get-position n b)) (back-diagonal-sum (- n 1) b))
	)
)

(define (X-win? b)
	(or
		(map-reduce or-procedure #f (lambda (row) (equal? (get-num row) (reduce + row 0))) b)
		(in? (get-num b) (reduce add-list b (initial-list (get-num (first b)) 0)))
		(equal? (diagonal-sum (get-num b) b) (get-num b))
		(equal? (back-diagonal-sum (get-num b) b) (get-num b))
	)
)

(define (O-win? b)
	(or
		(map-reduce or-procedure #f (lambda (row) (equal? (* -1 (get-num row)) (reduce + row 0))) b)
		(in? (* -1 (get-num b)) (reduce add-list b (initial-list (get-num (first b)) 0)))
		(equal? (diagonal-sum (get-num b) b) (* -1 (get-num b)))
		(equal? (back-diagonal-sum (get-num b) b) (* -1 (get-num b)))
	)
)

(define (win b)
	(cond
		((X-win? b) 1)
		((O-win? b) -1)
		(else 0)
	)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (remove-if-not p l)
	(cond
		((null? l) '())
		((p (first l)) (cons (first l) (remove-if-not p (rest l))))
		(else (remove-if-not p (rest l)))
	)
)

(define (maximize f l limit)
	(define (loop best-so-far l)
		(cond
			((>= best-so-far limit) 1)
			((null? l) best-so-far)
			(else
				(loop (max (f (first l) best-so-far) best-so-far) (rest l))
			)
		)
	)
	(loop -1 l)
)

(define (w* b l)
	(if (or (not (equal? (win b) 0)) (null? (moves b)))
		(win b)
		(* (player-to-move b) (maximize (lambda (m l1) (* (player-to-move b) (w* (make-move m b) (* (player-to-move b) l1)))) (moves b) (* l (player-to-move b))))
	)
)

(define (m^ b)
	(if (not (equal? (win b) 0))
		'()
		(remove-if-not (lambda (m) (equal? (w* (make-move m b) (player-to-move (make-move m b))) (w* b (player-to-move b)))) (moves b))
	)
)

(define (aggregate-list l1 l2)
	(if (null? l1)
		'()
		(if (list? (first l1))
			(cons (append (first l1) (list (first l2))) (aggregate-list (rest l1) (rest l2)))
			(cons (list (first l1) (first l2)) (aggregate-list (rest l1) (rest l2)))
		)
	)
)

(define (transpose b)
	(reduce aggregate-list b (initial-list (get-num (first b)) '()))
)

(define (diagonal-check n b v)
	(if (equal? n 1)
		(or (equal? (get-position 1 (get-position 1 b)) 0) (equal? (get-position 1 (get-position 1 b)) v))
		(and (or (equal? (get-position n (get-position n b)) 0) (equal? (get-position n (get-position n b)) v)) (diagonal-check (- n 1) b v))
	)
)

(define (back-diagonal-check n b v)
	(if (equal? n 1)
		(or (equal? (get-position (- (+ (get-num b) 1) n) (get-position n b)) 0) (equal? (get-position (- (+ (get-num b) 1) n) (get-position n b)) v))
		(and (or (equal? (get-position (- (+ (get-num b) 1) n) (get-position n b)) 0) (equal? (get-position (- (+ (get-num b) 1) n) (get-position n b)) v)) (back-diagonal-check (- n 1) b v))
	)
)

(define (eval-X b)
	(+
		(map-reduce + 0 
			(lambda (row) 
				(if (map-reduce and-procedure #t (lambda (x) (or (equal? x 1) (equal? x 0))) row)
					;(expt 2 (map-reduce + 0 (lambda (x) (if (equal? x 1) 1 0)) row))
					;(* 2 (map-reduce + 0 (lambda (x) (if (equal? x 1) 1 0)) row))
					;(map-reduce + 0 (lambda (x) (if (equal? x 1) 1 0)) row)
					1
					0
				)
			) 
		b)
		(map-reduce + 0
			(lambda (row) 
				(if (map-reduce and-procedure #t (lambda (x) (or (equal? x 1) (equal? x 0))) row)
					;(expt 2 (map-reduce + 0 (lambda (x) (if (equal? x 1) 1 0)) row))
					;(* 2 (map-reduce + 0 (lambda (x) (if (equal? x 1) 1 0)) row))
					;(map-reduce + 0 (lambda (x) (if (equal? x 1) 1 0)) row)
					1
					0
				)
			)
		(transpose b))
		(if (diagonal-check (get-num b) b 1)
			;(expt 2 (diagonal-sum (get-num b) b))
			;(* 2 (diagonal-sum (get-num b) b))
			;(diagonal-sum (get-num b) b)
			1
			0
		)
		(if (back-diagonal-check (get-num b) b 1)
			;(expt 2 (back-diagonal-sum (get-num b) b))
			;(* 2 (back-diagonal-sum (get-num b) b))
			;(back-diagonal-sum (get-num b) b)
			1
			0
		)
	)
)

(define (eval-O b)
	(+
		(map-reduce + 0 
			(lambda (row) 
				(if (map-reduce and-procedure #t (lambda (x) (or (equal? x -1) (equal? x 0))) row)
					;(expt 2 (map-reduce + 0 (lambda (x) (if (equal? x -1) 1 0)) row))
					;(* 2 (map-reduce + 0 (lambda (x) (if (equal? x -1) 1 0)) row))
					;(map-reduce + 0 (lambda (x) (if (equal? x -1) 1 0)) row)
					1
					0
				)
			) 
		b)
		(map-reduce + 0
			(lambda (row) 
				(if (map-reduce and-procedure #t (lambda (x) (or (equal? x -1) (equal? x 0))) row)
					;(expt 2 (map-reduce + 0 (lambda (x) (if (equal? x -1) 1 0)) row))
					;(* 2 (map-reduce + 0 (lambda (x) (if (equal? x -1) 1 0)) row))
					;(map-reduce + 0 (lambda (x) (if (equal? x -1) 1 0)) row)
					1
					0
				)
			)
		(transpose b))
		(if (diagonal-check (get-num b) b -1)
			;(expt 2 (abs (diagonal-sum (get-num b) b)))
			;(* 2 (abs (diagonal-sum (get-num b) b)))
			;(abs (diagonal-sum (get-num b) b))
			1
			0
		)
		(if (back-diagonal-check (get-num b) b -1)
			;(expt 2 (abs (back-diagonal-sum (get-num b) b)))
			;(* 2 (abs (back-diagonal-sum (get-num b) b)))
			;(abs (back-diagonal-sum (get-num b) b))
			1
			0
		)
	)
)

(define (estimate b)
	(if (equal? (* -1 (player-to-move b)) 1)
		(cond
			((> (+ 1 (eval-X b)) (eval-O b)) 1)
			((< (+ 1 (eval-X b)) (eval-O b)) -1)
			(else 0)
		)
		(cond
			((> (eval-X b) (+ 1 (eval-O b))) 1)
			((< (eval-X b) (+ 1 (eval-O b))) -1)
			(else 0)
		)
	)
)

(define (w~ k b l)
	(cond
		((equal? k 0) 
			(cond
				((or (equal? (win b) 1) (equal? (estimate b) 1)) 1)
				((or (and (equal? (win b) 0) (null? (moves b))) (equal? (estimate b) 0)) 0)
				((or (equal? (win b) -1) (equal? (estimate b) -1)) -1)
			)
		)
		((or (not (equal? (win b) 0)) (null? (moves b))) (win b))
		(else
			(* (player-to-move b) (maximize (lambda (m l1) (* (player-to-move b) (w~ (- k 1) (make-move m b) (* (player-to-move b) l1)))) (moves b) (* l (player-to-move b))))
		)
	)
)

(define (m~ k b)
	(if (not (equal? (win b) 0))
		'()
		(remove-if-not (lambda (m) (>= (* (player-to-move b) (w~ (- k 1) (make-move m b) (player-to-move (make-move m b)))) (* (player-to-move b) (w~ k b (player-to-move b))))) (moves b))
	)
)

(define (optimal-moves~ k b)
	(if (or (equal? k infinity) (equal? k 0))
		(m^ b)
		(m~ k b)
	)
)