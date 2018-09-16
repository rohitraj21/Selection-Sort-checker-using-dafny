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

method bubbleSort (A:array<int>)
	requires A != null
	modifies A
	ensures ordered(A)
	ensures permutation (A[..], old(A[..]))

{
	if A.Length > 1
	{
		var i := 1;
		while i < A.Length
			invariant 1 <= i <= A.Length
			invariant partOrdered (A, 0, i)
			invariant permutation (A[..], old(A[..]))
			decreases A.Length - i
		{
			bubble (A, i);
			i := i+1;
		}
	}
}

method bubble (A:array<int>, i:int)
	requires A != null && 0 <= i < A.Length
	requires partOrdered (A, 0, i)
	modifies A
	ensures partOrdered (A, 0, i+1)
	ensures permutation (A[..], old(A[..]))
{
	var j:= i;
	while j > 0 && A[j-1] > A[j]
		invariant 0 <= j <= i
		invariant partOrdered (A, 0, j) && partOrdered(A, j, i+1)
		invariant permutation (A[..], old(A[..]))
		invariant 1 < j+1 <= i ==> A[j-1] <= A[j+1]
		decreases j
	{
		A[j-1], A[j] := A[j], A[j-1];
		j := j-1;
	}
}

method Main ()
{
	var A:= new int[10];
	A[0],A[1],A[2],A[3],A[4],A[5],A[6],A[7],A[8],A[9] := 
	4,8,8,3,5,10,9,9,4,7;
	print "A = ", A[..], "\n";
	bubbleSort (A);
	print "A = ", A[..], "\n";
}