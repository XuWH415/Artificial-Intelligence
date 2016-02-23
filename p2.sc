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
       (And-Case (Rest T1) T2)
	  )
	 )
	)
)

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
