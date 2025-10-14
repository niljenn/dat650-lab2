predicate Ordered(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    forall i: nat :: 0 < left <= i < right ==> a[i-1] <= a[i]
}

twostate predicate Preserved(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    multiset(a[left..right]) == multiset(old(a[left..right]))
}

method MySort(a: array<int>)
    modifies a
    ensures Ordered(a,0,a.Length)
    ensures Preserved(a,0,a.Length)
{
    for i := 0 to a.Length
        invariant Ordered(a,0,i)
        invariant Preserved(a,0,a.Length)
    {
        var minValue := a[i];
        var minPos := i;
        for j := i + 1 to a.Length
            invariant minPos < a.Length
            invariant a[minPos] == minValue
        {
            if a[j] < minValue {
                minValue := a[j];
                minPos := j;
            }
        }
        if i != minPos {
            a[i], a[minPos] := minValue, a[i];
        }
    }
}