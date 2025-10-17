predicate sorted(a: array<int>, l: int, u: int)
  reads a
  {
    forall i, j :: 0 <= l <= i <= j < u <= a.Length ==> a[i] <= a[j]
  }

twostate predicate Preserved(a: array<int>, left: nat, right: nat)
    reads a
    requires left <= right <= a.Length
{
    multiset(a[left..right]) == multiset(old(a[left..right]))
}

method MySort(a: array<int>)
    modifies a
    ensures sorted(a,0,a.Length)
    ensures Preserved(a,0,a.Length)
{
    if a.Length == 0 {
        return;
    }
    for i := 0 to a.Length - 1
        invariant 0 <= i <= a.Length
        invariant Preserved(a,0,a.Length)
        invariant sorted(a, 0, i)
        invariant forall k :: 0 <= k < i ==> forall l :: i <= l < a.Length ==> a[k] <= a[l]
    {
        var minValue := a[i];
        var minPos := i;
        for j := i + 1 to a.Length
            invariant i <= j <= a.Length
            invariant i <= minPos < a.Length
            invariant a[minPos] == minValue
            invariant forall k :: i <= k < j ==> a[minPos] <= a[k]
            invariant sorted(a, 0, i)
            invariant forall k :: 0 <= k < i ==> forall l :: i <= l < a.Length ==> a[k] <= a[l]
        {
            if a[j] < minValue {
                minValue := a[j];
                minPos := j;
            }
        }
        assert forall k :: i <= k < a.Length ==> a[minPos] <= a[k];

        if minPos != i {
            var tmp := a[i];
            a[i] := a[minPos];
            a[minPos] := tmp;
        }
        assert forall k :: i < k < a.Length ==> a[i] <= a[k];
        assert forall k :: 0 <= k < i ==> a[k] <= a[i];
        assert sorted(a, 0, i + 1);
    }
}