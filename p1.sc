(Define (In? E L)
 (If (Null? L)
     #F
     (If (= E (First L))
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

(Define (Set-Intersection A B)
 (If (Null? A)
     (List)
     (If (In? (First A) B)
	 (Add-Element (First A) (Set-Intersection (Rest A) B))
	 (Set-Intersection (Rest A) B))))

(Define (Set-Minus A B)
 (If (Null? A)
     (List)
     (If (In? (First A) B)
	 (Set-Minus (Rest A) B)
	 (Add-Element (First A) (Set-Minus (Rest A) B)))))
