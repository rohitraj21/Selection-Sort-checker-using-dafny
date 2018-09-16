predicate permutation (A:seq<int>, B:seq<int>)
{ multiset (A) == multiset (B)}

predicate partOrdered (A:array<int>, lo:int, hi:int)
	requires A != null
	requires 0 <= lo <= hi <= A.Length
	reads A
{ forall i,j:: lo <= i < j < hi ==> A[i] <= A[j] }

predicate ordered (A:array<int>)
	requires A != null
	reads A
	{
		partOrdered (A, 0, A.Length)
	}

method selectionSort (A:array<int>)
	requires A != null
	modifies A
	ensures ordered(A)
	ensures permutation (A[..], old(A[..]))
{
	if A.Length > 1
	{
		var i := A.Length-1;
		while i >= 0
			invariant -1 <= i < A.Length
			invariant forall j, k:int :: 0 <= j <= i && i < k < A.Length ==> A[j] <= A[k]
			invariant partOrdered (A, i+1, A.Length)
			invariant permutation (A[..], old(A[..]))
			decreases i - 0
		{
			select (A, i);
			i := i-1;
		}
	}
}

method findMax (A:array<int>, lo:int, hi:int) returns (index:int)
	requires A != null 
	requires 0 <= lo <= hi < A.Length
	ensures lo <= index <= hi
	ensures forall j:int :: (lo <= j <= hi) ==> A[index] >= A[j]
{
	index := hi ;
	var i := hi-1 ;
	
	while i >= lo
		invariant lo-1 <= i <= hi 
		invariant i < index <= hi
		invariant forall k:int :: (i < k <= hi) ==> (A[index] >= A[k])
		decreases i - lo
	{
		if(A[i] > A[index])
		{
			// m := A[i] ;
			index := i ;
		}
		i := i-1 ;
	}
} 

method select (A:array<int>, i:int)
	requires A != null && 0 <= i < A.Length
	requires partOrdered (A, i+1, A.Length)
	requires forall j,k :int :: 0 <= j <= i && i < k < A.Length ==> A[j] <= A[k]
	modifies A
	ensures forall j,k :int :: 0 <= j < i && i <= k < A.Length ==> A[j] <= A[k]
	ensures partOrdered (A, i, A.Length)
	ensures permutation (A[..], old(A[..]))
{
	var ind := findMax (A, 0, i) ;
	A[ind], A[i] := A[i], A[ind] ;
}

method Main ()
{
	var A:= new int[10];
	A[0],A[1],A[2],A[3],A[4],A[5],A[6],A[7],A[8],A[9] := 
	4,8,8,3,5,10,9,9,4,7;
	print "A = ", A[..], "\n";
	selectionSort (A);
	print "A = ", A[..], "\n\n";
	A[0],A[1],A[2],A[3],A[4],A[5],A[6],A[7],A[8],A[9] := 
	4,-8,-8,3,5,10,-9,9,4,-7;
	print "A = ", A[..], "\n";
	selectionSort (A);
	print "A = ", A[..], "\n\n";
	A[0],A[1],A[2],A[3],A[4],A[5],A[6],A[7],A[8],A[9] := 
	8,8,8,8,8,8,8,8,8,8;
	print "A = ", A[..], "\n";
	selectionSort (A);
	print "A = ", A[..], "\n\n";
	A[0],A[1],A[2],A[3],A[4],A[5],A[6],A[7],A[8],A[9] := 
	1,2,3,4,5,6,7,8,9,10;
	print "A = ", A[..], "\n";
	selectionSort (A);
	print "A = ", A[..], "\n";
}