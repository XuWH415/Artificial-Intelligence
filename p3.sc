(Define (In? E L)
 (If (Null? L)
     #F
     (If (Equal? E (First L))
	 #T
	 (In? E (Rest L)))))

(Define (Repetition? L)
 (If (Null? L)
     #F
     (If (In? (First L) (Rest L))
	 #T
	 (Repetition? (Rest L)))))

(Define (Add-Element E L)
 (If (In? E L)
     L
     (Cons E L)))

(Define (Set-Union A B)
 (If (Null? A)
     (If (Repetition? B)
	 (Set-Union B (List))
	 B)
     (Set-Union (Rest A) (Add-Element (First A) B))))

;;; Inconsistence-In?(B I): Determine If A Binding B Is Inconsistent With Other Bindings In Truth Assignment I
(Define (Inconsistence-In? B I)
 (If (Null? I)
     #F
     (If (Equal? (First B) (First (First I)))
	 (If (Equal? (Second B) (Second (First I)))
	     (Inconsistence-In? B (Rest I))
	     #T)
	 (Inconsistence-In? B (Rest I)))))

;;; Inconsistence?(I): Determine If A Truth Assignment I Is Inconsistent
(Define (Inconsistence? I)
 (If (Null? I)
     #F
     (If (Inconsistence-In? (First I) (Rest I))
	 #T
	 (Inconsistence? (Rest I)))))

;;; Eliminate-Inconsistence(Truth-Table): Eliminate Rows Containing Inconsistent Truth Assignment, Return A Consistent Truth Table 
(Define (Eliminate-Inconsistence Truth-Table)
 (If (Null? Truth-Table)
     (List)
     (If (Inconsistence? (First (First Truth-Table)))
	 (Eliminate-Inconsistence (Rest Truth-Table))
	 (Cons (First Truth-Table) (Eliminate-Inconsistence (Rest Truth-Table))))))

;;; Not-Case(Row): Perform Not For Each Row In Truth Table By Flipping The Truth Value 
(Define (Not-Case Row)
 (If (Second Row)
     (Cons (First Row) (List #F))
     (Cons (First Row) (List #T))))

;;; And-Case(T1, T2): Perform And On Truth Table T1 And T2, Return A New Truth Table
(Define (And-Case T1 T2)
 (If (Null? T1)
     (List)
     (Eliminate-Inconsistence
      (Set-Union
       (Map
	(Lambda (X)
		(Cons
		 (Set-Union (First (First T1)) (First X))
		 (List (And (Second (First T1)) (Second X)))))
	T2)
       (And-Case (Rest T1) T2)))))

;;; Or-Case(T1, T2): Perform Or On Truth Table T1 And T2, Return A New Truth Table
(Define (Or-Case T1 T2)
 (If (Null? T1)
     (List)
     (Eliminate-Inconsistence
      (Set-Union
       (Map
	(Lambda (X)
		(Cons
		 (Set-Union (First (First T1)) (First X))
		 (List (Or (Second (First T1)) (Second X)))))
	T2)
       (Or-Case (Rest T1) T2)))))

;;; Truth-Table(Phi): Return A Truth Table For The Formula Phi
(Define (Truth-Table Phi)
 (Cond ((Boolean? Phi) (List (List (List) Phi)))
       ((Symbol? Phi) (List (List (List (List Phi #T)) #T) (List (List (List Phi #F)) #F)))
       ((List? Phi)
	(Case (First Phi)
	      ((Not) (Map Not-Case (Truth-Table (Second Phi))))
	      ((And)
	       (Case (Length Phi)
		     ((1) (List (List (List) #T)))
		     ((2) (Truth-Table (Second Phi)))
		     (Else (And-Case (Truth-Table (Second Phi)) (Truth-Table (Cons 'And (Rest (Rest Phi))))))))
	      ((Or)
	       (Case (Length Phi)
		     ((1) (List (List (List) #F)))
		     ((2) (Truth-Table (Second Phi)))
		     (Else (Or-Case (Truth-Table (Second Phi)) (Truth-Table (Cons 'Or (Rest (Rest Phi))))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(Define (Or-Procedure X Y) (Or X Y))

(Define (And-Procedure X Y) (And X Y))

(Define (Formula-Equal? Formula1 Formula2)
	(If (And (List? Formula1) (List? Formula2))
		(If (Equal? (Length Formula1) (Length Formula2))
			(If (Equal? (First Formula1) (First Formula2))
				(Map-Reduce And-Procedure #T (Lambda (F1) (Map-Reduce Or-Procedure #F (Lambda (F2) (Formula-Equal? F1 F2)) (Rest Formula2))) (Rest Formula1))
				#F
			)
			#F
		)
		(Equal? Formula1 Formula2)
	)
)

(Define (Formula-In? Formula Formula-List)
	(Map-Reduce Or-Procedure #F (Lambda (X) (Formula-Equal? Formula X)) Formula-List)
)

(Define (Basic-Simplify Phi)
	(Cond
		((Boolean? Phi) Phi)
		((Symbol? Phi) Phi)
		((List? Phi)
			(Case (First Phi)
				((Not) 
					(Cond
						((Boolean? (Basic-Simplify(Second Phi)))
							(Not (Basic-Simplify(Second Phi)))
						)
						((Symbol? (Basic-Simplify(Second Phi)))
							(List 'Not (Basic-Simplify(Second Phi)))
						)
						((List? (Basic-Simplify(Second Phi)))
							(If (Equal? 'Not (First (Basic-Simplify(Second Phi))))
								(Second (Basic-Simplify(Second Phi)))
								(List 'Not (Basic-Simplify(Second Phi)))
							)
						)
					)
				)
				((And)
					(Case (Length Phi)
						((1) #T)
						;;; (And Phi1) -~-> Phi1
						((2)
							(Basic-Simplify (Second Phi))
						)
						(Else
							(Cond
								;;; (And Phi1 #F) -~-> #F
								((Equal? #F (Basic-Simplify (Cons 'And (Rest (Rest Phi)))))
									#F
								)
								;;; (And Phi1 #T) -~-> (And Phi1) -~-> Phi1
								((Equal? #T (Basic-Simplify (Cons 'And (Rest (Rest Phi)))))
									(Basic-Simplify (Second Phi))
								)
								;;; (And Phi1 (And Phi2 ...)) -~-> (And Phi1 Phi2 ...)
								((And (List? (Basic-Simplify (Cons 'And (Rest (Rest Phi))))) (Equal? 'And (First (Basic-Simplify (Cons 'And (Rest (Rest Phi)))))))
									(Cond
										;;; (And #F (And Phi2 ...)) -~-> #F
										((Equal? #F (Basic-Simplify (Second Phi)))
											#F
										)
										;;; (And #T (And Phi2 ...)) -~-> (And Phi2 ...)
										((Equal? #T (Basic-Simplify (Second Phi)))
											(Basic-Simplify (Cons 'And (Rest (Rest Phi))))
										)
										;;; (And (And Phi1 ...) (And Phi2 ...)) -~-> (And Phi1 ... Phi2 ...)
										((And (List? (Basic-Simplify (Second Phi))) (Equal? 'And (First (Basic-Simplify (Second Phi)))))
											;;; Check ***
											(Basic-Simplify (Append (Basic-Simplify (Second Phi)) (Rest (Basic-Simplify (Cons 'And (Rest (Rest Phi)))))))
										)
										;;; (And Phi1 (And Phi2 ...)) -~-> (And Phi1 Phi2 ...)
										(Else
											;;; Check ***
											(Cond
												((Formula-In? (Basic-Simplify (Second Phi)) (Rest (Basic-Simplify (Cons 'And (Rest (Rest Phi))))))
													(Basic-Simplify (Cons 'And (Rest (Rest Phi))))
												)
												((Formula-In? (Basic-Simplify (Cons 'Not (List (Second Phi)))) (Rest (Basic-Simplify (Cons 'And (Rest (Rest Phi))))))
													#F
												)
												(Else
													(Cons 'And (Cons (Basic-Simplify (Second Phi)) (Rest (Basic-Simplify (Cons 'And (Rest (Rest Phi)))))))
												)
											)
										)
									)
								)
								;;; (And Phi1 Phi2) -~-> (And Phi1 Phi2)
								(Else
									(Cond
										;;; (And #F Phi2) -~-> #F
										((Equal? #F (Basic-Simplify (Second Phi)))
											#F
										)
										;;; (And #T Phi2) -~-> Phi2
										((Equal? #T (Basic-Simplify (Second Phi)))
											(Basic-Simplify (Cons 'And (Rest (Rest Phi))))
										)
										;;; (And (And Phi1 ...) Phi2) -~-> (And Phi1 ... Phi2)
										((And (List? (Basic-Simplify (Second Phi))) (Equal? 'And (First (Basic-Simplify (Second Phi)))))
											;;; Check ***
											(Cond
												((Formula-In? (Basic-Simplify (Cons 'And (Rest (Rest Phi)))) (Rest (Basic-Simplify (Second Phi))))
													(Basic-Simplify (Second Phi))
												)
												((Formula-In? (Basic-Simplify (Cons 'Not (List (Cons 'And (Rest (Rest Phi)))))) (Rest (Basic-Simplify (Second Phi))))
													#F
												)
												(Else
													(Append (Basic-Simplify (Second Phi)) (List (Basic-Simplify (Cons 'And (Rest (Rest Phi))))))
												)
											)
										)
										;;; (And Phi1 Phi2) -~-> (And Phi1 Phi2)
										(Else
											;;; Check ***
											(Cond
												((Formula-Equal? (Basic-Simplify (Second Phi)) (Basic-Simplify (Cons 'And (Rest (Rest Phi)))))
													(Basic-Simplify (Second Phi))
												)
												((Formula-Equal? (Basic-Simplify (Cons 'Not (List (Second Phi)))) (Basic-Simplify (Cons 'And (Rest (Rest Phi)))))
													#F
												)
												(Else
													(Cons 'And (Cons (Basic-Simplify (Second Phi)) (List (Basic-Simplify (Cons 'And (Rest (Rest Phi)))))))
												)
											)
										)
									)
								)
							)
						)
					)
				)
				((Or)
					(Case (Length Phi)
						((1) #F)
						;;; (Or Phi1) -~-> Phi1
						((2)
							(Basic-Simplify (Second Phi))
						)
						(Else
							(Cond
								;;; (Or Phi1 #T) -~-> #T
								((Equal? #T (Basic-Simplify (Cons 'Or (Rest (Rest Phi)))))
									#T
								)
								;;; (Or Phi1 #F) -~-> (Or Phi1) -~-> Phi1
								((Equal? #F (Basic-Simplify (Cons 'Or (Rest (Rest Phi)))))
									(Basic-Simplify (Second Phi))
								)
								;;; (Or Phi1 (Or Phi2 ...)) -~-> (Or Phi1 Phi2 ...)
								((And (List? (Basic-Simplify (Cons 'Or (Rest (Rest Phi))))) (Equal? 'Or (First (Basic-Simplify (Cons 'Or (Rest (Rest Phi)))))))
									(Cond
										;;; (Or #T (Or Phi2 ...)) -~-> #T
										((Equal? #T (Basic-Simplify (Second Phi)))
											#T
										)
										;;; (Or #F (Or Phi2 ...)) -~-> (Or Phi2 ...)
										((Equal? #F (Basic-Simplify (Second Phi)))
											(Basic-Simplify (Cons 'Or (Rest (Rest Phi))))
										)
										;;; (Or (Or Phi1 ...) (Or Phi2 ...)) -~-> (Or Phi1 ... Phi2 ...)
										((And (List? (Basic-Simplify (Second Phi))) (Equal? 'Or (First (Basic-Simplify (Second Phi)))))
											;;; Check ***
											(Basic-Simplify (Append (Basic-Simplify (Second Phi)) (Rest (Basic-Simplify (Cons 'Or (Rest (Rest Phi)))))))
										)
										;;; (Or Phi1 (Or Phi2 ...)) -~-> (Or Phi1 Phi2 ...)
										(Else
											;;; Check ***
											(Cond
												((Formula-In? (Basic-Simplify (Second Phi)) (Rest (Basic-Simplify (Cons 'Or (Rest (Rest Phi))))))
													(Basic-Simplify (Cons 'Or (Rest (Rest Phi))))
												)
												((Formula-In? (Basic-Simplify (Cons 'Not (List (Second Phi)))) (Rest (Basic-Simplify (Cons 'Or (Rest (Rest Phi))))))
													#T
												)
												(Else
													(Cons 'Or (Cons (Basic-Simplify (Second Phi)) (Rest (Basic-Simplify (Cons 'Or (Rest (Rest Phi)))))))
												)
											)
										)
									)
								)
								;;; (Or Phi1 Phi2) -~-> (Or Phi1 Phi2)
								(Else
									(Cond
										;;; (Or #T Phi2) -~-> #T
										((Equal? #T (Basic-Simplify (Second Phi)))
											#T
										)
										;;; (Or #F Phi2) -~-> Phi2
										((Equal? #F (Basic-Simplify (Second Phi)))
											(Basic-Simplify (Cons 'Or (Rest (Rest Phi))))
										)
										;;; (Or (Or Phi1 ...) Phi2) -~-> (Or Phi1 ... Phi2)
										((And (List? (Basic-Simplify (Second Phi))) (Equal? 'Or (First (Basic-Simplify (Second Phi)))))
											;;; Check ***
											(Cond
												((Formula-In? (Basic-Simplify (Cons 'Or (Rest (Rest Phi)))) (Rest (Basic-Simplify (Second Phi))))
													(Basic-Simplify (Second Phi))
												)
												((Formula-In? (Basic-Simplify (Cons 'Not (List (Cons 'Or (Rest (Rest Phi)))))) (Rest (Basic-Simplify (Second Phi))))
													#T
												)
												(Else
													(Append (Basic-Simplify (Second Phi)) (List (Basic-Simplify (Cons 'Or (Rest (Rest Phi))))))
												)
											)
										)
										;;; (Or Phi1 Phi2) -~-> (Or Phi1 Phi2)
										(Else
											;;; Check ***
											(Cond
												((Formula-Equal? (Basic-Simplify (Second Phi)) (Basic-Simplify (Cons 'Or (Rest (Rest Phi)))))
													(Basic-Simplify (Second Phi))
												)
												((Formula-Equal? (Basic-Simplify (Cons 'Not (List (Second Phi)))) (Basic-Simplify (Cons 'Or (Rest (Rest Phi)))))
													#T
												)
												(Else
													(Cons 'Or (Cons (Basic-Simplify (Second Phi)) (List (Basic-Simplify (Cons 'Or (Rest (Rest Phi)))))))
												)
											)
										)
									)
								)
							)
						)
					)
				)
			)
		)
		(Else (Panic "Error: Invalid Formula"))
	)
)

(Define (Boolean-Simplify Phi)
	(Basic-Simplify Phi)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(Define (Binding-Included? Row1 Row2)
	(If (Null? (First Row2))
		#T
		(If (Null? (First Row1))
			#F
			(Map-Reduce And-Procedure #T
				(Lambda (B2)
					(Map-Reduce Or-Procedure #F
						(Lambda (B1)
							(Equal? B2 B1))
					(First Row1)))
			(First Row2))
		)
	)
)

(Define (Proposition-Included? Row1 Row2)
	(If (Null? (First Row2))
		#T
		(If (Null? (First Row1))
			#F
			(Map-Reduce And-Procedure #T
				(Lambda (B2)
					(Map-Reduce Or-Procedure #F
						(Lambda (B1)
							(Equal? (First B2) (First B1)))
					(First Row1)))
			(First Row2))
		)
	)
)

(Define (Row-Match? Row1 Row2)
	(If (Proposition-Included? Row1 Row2)
		(If (Binding-Included? Row1 Row2)
			(If (Equal? (Second Row1) (Second Row2))
				#T
				#F
			)
			#T
		)
		#F
	)
)

(Define (Truth-Tables-Match? Phi1 Phi2)
	(Map-Reduce And-Procedure #T (Lambda (R2) (Map-Reduce And-Procedure #T (Lambda (R1) (Row-Match? R1 R2)) (Truth-Table Phi1))) (Truth-Table Phi2))
)
	 