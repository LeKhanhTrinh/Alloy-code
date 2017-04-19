sig Orderable { 
    geq: Orderable -> one Bool 
} 
abstract sig Bool{}
one sig True, False extends Bool{}

sig SortedSet { 
    insert: Orderable -> one SortedSet, 
    isEmpty: one Bool, 
    isIn: Orderable -> one Bool,  
    largest: lone Orderable 
} 
one sig start { 
    empty: one SortedSet 
} 
fact SortedSetConstruction { 
   SortedSet in (start.empty).*{x: SortedSet, y: x.insert[Orderable]} 
} 
fact domainSortedSet0 { 
   all S:SortedSet | 
      S.isEmpty != True  implies one S.largest else no S.largest 
} 
fact axiomSortedSet4 { 
   all E: Orderable, S: SortedSet | 
      (S.isEmpty = True implies (S.insert[E].largest = E)) 
} 
// … other axioms of Orderable and SortedSet 
run axiomSortedSet4_1 {  
    some E : Orderable, S : SortedSet |  
        (S.isEmpty ! = True and (S.insert[E].largest != E))  
} for 6 but exactly 2 Orderable 
