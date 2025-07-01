module SortedSet {
    //Based on the work of Stefano Oppesisano
    class GrowableSortedSet {

        ghost var Repr: set<object>
        ghost var elems: seq<int>

        // Fields
        var arr: array<int> 
        var nElems: int // Number of elements in array

        // Implementations
        constructor (size: int)
            requires size > 0
            ensures Valid() && fresh(Repr - {this})
            ensures nElems == |elems| == 0
            ensures arr.Length == size
        {
            arr := new int[size](i => -1);
            nElems := 0;
            elems := [];
            Repr := {this, arr};
        }

        ghost predicate Valid()
            reads this, Repr
        {
            this in Repr 
            && arr in Repr
            && 0 <= nElems <= arr.Length // The number of elements is always in a valid range
            && 0 < arr.Length // The array has a valid length
            && nElems == |elems| // The array and its ghost counterpart are aligned in number of elements...
            && (forall i :: 0 <= i < nElems ==> arr[i] == elems[i]) // ... and value of elements
            && (forall i :: 0 < i < nElems ==> arr[i] > arr[i-1]) // The array is ordered
        }

        predicate IsFull()
            requires Valid()
            reads this, Repr, arr
            ensures IsFull() ==> nElems == arr.Length // If the predicate body is true then it means that nElems is equal to the array length
        {
            nElems == arr.Length
        }

        method GetValue(index: int) returns (value: int)
            requires Valid()
            requires 0 <= index < nElems
            ensures Valid()
        {
            value := arr[index];
        }

        method HasValue(value: int) returns (result: bool)
            requires Valid()
            ensures result ==> exists i :: 0 <= i < nElems && arr[i] == value
            ensures !result ==> forall i :: 0 <= i < nElems ==> arr[i] != value
        {
            OrderedImpliesSorted(arr, nElems);
            var low, high := 0, nElems;
            while low < high
                invariant 0 <= low <= high <= nElems 
                invariant forall i :: 0 <= i < nElems && !(low <= i < high) ==> arr[i] != value 
            {
                var mid := (low + high) / 2; 
                if arr[mid] < value { 
                    low := mid + 1; 
                } else if value < arr[mid] { 
                    high := mid; 
                } else { 
                    return true; 
                } 
            }
            return false; 
        }

        method IncreaseSize() returns ()
            requires Valid()
            modifies this, arr
            ensures Valid() && fresh(Repr - old(Repr))
            ensures !IsFull()
            ensures arr.Length > old(arr.Length)
            ensures arr[..nElems] == old(arr[..nElems])
        {   
            var newArr := new int[arr.Length*2];
            forall i | 0 <= i < arr.Length { newArr[i] := arr[i]; }
            forall i | arr.Length <= i < newArr.Length {newArr[i] := -1; }
            arr := newArr;
            this.Repr := this.Repr + {newArr};
            assert forall i :: 0 <= i < nElems ==> arr[i] == elems[i] by {
                forall i | 0 <= i < nElems
                    ensures arr[i] == elems[i]
                {
                    assert i < nElems;
                }
            }
        }

        method AddValue(value: int) returns (ghost index: int)
            requires Valid()
            requires value !in elems
            modifies Repr, this, arr
            ensures Valid() && fresh(Repr - old(Repr))
            ensures value in elems
            ensures 0 <= index <= old(nElems)
            ensures nElems == old(nElems) + 1
            ensures arr[index] == value
            ensures elems == old(elems[..index]) + [value] + old(elems[index..])
        {
            if IsFull() {
                IncreaseSize();
            }

            assert !IsFull();

            // Find insertion point
            var indexInsert := 0;
            while indexInsert < nElems && arr[indexInsert] < value
                invariant 0 <= indexInsert <= nElems
                invariant forall i :: 0 <= i < indexInsert ==> arr[i] < value
            {
                indexInsert := indexInsert + 1;
            }

            assert arr[..nElems] == elems by {
                forall i | 0 <= i < |elems| 
                    ensures arr[i] == elems[i]
                {
                    assert elems[i] == arr[i];
                }
            }
            elems := elems[..indexInsert] + [value] + elems[indexInsert..];
            label LoopStart: 
            // Shift elements to the right
            var j := nElems;
            while j > indexInsert
                invariant indexInsert <= j <= nElems
                invariant 0 <= j < arr.Length
                invariant arr[..j] == old(arr[..j]) // Array won't change up to indexInsert
                invariant arr[j+1..nElems+1] == old(arr[j..nElems]) // The element at j is the one at j-1
                modifies arr
                decreases j
            {
                arr[j] := arr[j-1];
                assert arr[j] == old(arr[j-1]);
                ArrayShift@LoopStart(arr, j, nElems);
                j := j - 1;
            }
            assert j == indexInsert;
            assert arr[indexInsert+1..nElems+1] == old(arr[indexInsert..nElems]);
            assert old(arr[indexInsert..nElems]) == elems[indexInsert+1..];


            // Increase the nElems as the elements are shifted to the right
            nElems := nElems + 1;

            // Insert the new value
            arr[indexInsert] := value;
            assert forall i :: 0 <= i < |elems| ==> arr[i] == elems[i] by {
                forall i | 0 <= i < |elems| 
                    ensures arr[i] == elems[i]
                {
                    assert i < nElems;
                    if i < indexInsert {
                        assert arr[i] == old(arr[i]);
                        assert elems[i] == arr[i];
                    } else if i == indexInsert {
                        assert elems[i] == arr[i];
                    } else {
                        assert i >= indexInsert+1;
                        assert elems[i] == arr[i];
                    }
                }
            }
            return indexInsert;
        }
        
        method AppendValue(value: int)
            requires Valid()
            requires value !in elems
            requires forall x :: x in elems ==> x < value
            modifies Repr, this, arr
            ensures Valid() && fresh(Repr - old(Repr))
            ensures value in elems
            ensures nElems == old(nElems) + 1
            ensures arr[nElems - 1] == value
            ensures elems == old(elems[..nElems]) + [value]
        {
            if IsFull() {
                IncreaseSize();
            }

            assert !IsFull();

            elems := elems + [value];
            // Increase the nElems as a new element was added
            nElems := nElems + 1;

            // Insert the new value
            arr[nElems-1] := value;
            if nElems == 1 {

            }else {
                assert elems[nElems-2] in old(elems);
                assert elems[nElems-2] < value;
            }
        }


        method Union(ss: GrowableSortedSet) returns (result: GrowableSortedSet)
            requires Valid()
            requires ss.Valid()
            // ensures forall x :: x in this.elems[..nElems] ==> x in result.elems
            // ensures forall x :: x in ss.elems[..ss.nElems] ==> x in result.elems
            ensures ToSet(result.elems) == ToSet(this.elems[..nElems])+ToSet(ss.elems[..ss.nElems])
            ensures result.Valid()
        {
            OrderedImpliesSorted(this.arr, nElems);
            OrderedImpliesSorted(ss.arr, ss.nElems);
            result := new GrowableSortedSet(ss.arr.Length + this.arr.Length);
            assert ss.nElems + this.nElems <= ss.arr.Length + this.arr.Length;
            ghost var sumSet: set<int>  := {};
            for i := 0 to this.nElems
                invariant result.Valid()
                invariant fresh(result.Repr)
                invariant ToSet(this.elems[..i]) !! ToSet(this.elems[i..nElems])
                invariant forall x :: x in this.elems[i..nElems] ==> x !in result.elems
                invariant sumSet == ToSet(this.elems[..i])
                invariant ToSet(result.elems) == sumSet
            {
                OrderedImpliesDistinct(result.arr, result.elems, result.nElems);
                ElementAppendedOne(result.elems, sumSet, this.elems, this.nElems, i);
                result.AppendValue(this.arr[i]);
                assert this.elems[i] == this.arr[i];
                assert this.elems[..i+1] == this.elems[..i]+[this.arr[i]];
                ToSetConcat(this.elems[..i], [this.arr[i]]);
                sumSet := sumSet + {this.arr[i]};
            }

            for i := 0 to ss.nElems
                invariant result.Valid()
                invariant fresh(result.Repr)
                invariant ToSet(ss.elems[..i]) !! ToSet(ss.elems[i..ss.nElems])
                invariant ToSet(result.elems) == sumSet
                invariant sumSet == ToSet(this.elems[..this.nElems]) + ToSet(ss.elems[..i])
            {
                ghost var oldElems := result.elems;
                var has_value := result.HasValue(ss.arr[i]);
                if !has_value {
                    var index := result.AddValue(ss.arr[i]);
                    ElementInserted(oldElems, sumSet, this.elems, this.nElems, ss.elems, ss.nElems, i, index);
                    assert 0 <= i < ss.nElems;
                    assert ss.arr[i] == ss.elems[i];
                    ToSetConcat(ss.elems[..i], [ss.arr[i]]);
                    ToSetConcat(this.elems[..this.nElems], ss.elems[..i+1]);
                    SetsCombined(sumSet, this.elems, this.nElems, ss.elems, ss.nElems, i);
                    sumSet := sumSet + {ss.arr[i]};
                }else{
                    assert 0 <= i < ss.nElems;
                    assert ss.arr[i] == ss.elems[i];
                    assert ss.arr[i] in sumSet;
                    assert ss.elems[i] in sumSet;
                    SetsCombined2(sumSet, this.elems, this.nElems, ss.elems, ss.nElems, i);
                }
                SortedArrayIsDisjoint(ss.arr, ss.nElems, ss.elems, i+1);
            }
            assert sumSet == ToSet(this.elems[..this.nElems]) + ToSet(ss.elems[..ss.nElems]);
            // SetsCombinedImplies(result.elems, this.elems, nElems, ss.elems, ss.nElems);
            // assert ToSet(result.elems) == sumSet;
           

        }

        method {:isolate_assertions} Union2(ss: GrowableSortedSet) returns (result: GrowableSortedSet)
            requires Valid()
            requires ss.Valid()
            // ensures forall x :: x in this.elems[..nElems] ==> x in result.elems
            // ensures forall x :: x in ss.elems[..ss.nElems] ==> x in result.elems
            ensures ToSet(result.elems) == ToSet(this.elems[..nElems])+ToSet(ss.elems[..ss.nElems])
            ensures result.Valid()
        {
            OrderedImpliesSorted(this.arr, nElems);
            OrderedImpliesSorted(ss.arr, ss.nElems);
            result := new GrowableSortedSet(ss.arr.Length + this.arr.Length);
            assert ss.nElems + this.nElems <= ss.arr.Length + this.arr.Length;
            ghost var sumSet: set<int>  := {};
            var i := 0;
            var j := 0;
            while i + j < ss.nElems + this.nElems
                invariant 0 <= i <= this.nElems
                invariant 0 <= j <= ss.nElems
                invariant fresh(result.Repr)
                invariant ToSet(result.elems) == sumSet
                invariant i < this.nElems ==> forall x :: x in result.elems ==> x < this.elems[i]
                invariant j < ss.nElems ==> forall x :: x in result.elems ==> x < ss.elems[j]
                invariant sumSet == ToSet(this.elems[..i] + ss.elems[..j])
                invariant result.Valid()
            {
                OrderedImpliesSorted(result.arr, result.nElems);
                if i < this.nElems && j < ss.nElems {
                    if this.arr[i] == ss.arr[j] {
                        var has_value := result.HasValue(this.arr[i]);
                        assert this.elems[..i+1] == this.elems[..i]+[this.arr[i]];
                        assert ss.elems[..j+1] == ss.elems[..j]+[ss.arr[j]];
                        ToSetConcat(this.elems[..i], [this.arr[i]]);
                        ToSetConcat(ss.elems[..j], [ss.arr[j]]);
                        ToSetConcat(this.elems[..i+1], ss.elems[..j]);
                        ToSetConcat(this.elems[..i+1], ss.elems[..j+1]);
                        if !has_value {
                            result.AppendValue(this.arr[i]);
                            sumSet := sumSet + {this.arr[i]};
                        }
                        i := i + 1;
                        j := j + 1;
                    }else if this.arr[i] < ss.arr[j] {
                        var has_value := result.HasValue(this.arr[i]);
                        assert this.elems[..i+1] == this.elems[..i]+[this.arr[i]];
                        ToSetConcat(this.elems[..i], [this.arr[i]]);
                        ToSetConcat(this.elems[..i+1], ss.elems[..j]);
                        if !has_value {
                            result.AppendValue(this.arr[i]);
                            sumSet := sumSet + {this.arr[i]};
                        }
                        i := i + 1;
                    }else{
                        assert j < ss.nElems;
                        var has_value := result.HasValue(ss.arr[j]);
                        assert ss.elems[..j+1] == ss.elems[..j]+[ss.arr[j]];
                        ToSetConcat(ss.elems[..j], [ss.arr[j]]);
                        ToSetConcat(this.elems[..i], ss.elems[..j+1]);
                        if !has_value {
                            result.AppendValue(ss.arr[j]);
                            sumSet := sumSet + {ss.arr[j]};
                        }
                        j := j + 1;
                    }
                }else if i < this.nElems {
                    var has_value := result.HasValue(this.arr[i]);
                    assert this.elems[..i+1] == this.elems[..i]+[this.arr[i]];
                    ToSetConcat(this.elems[..i], [this.arr[i]]);
                    ToSetConcat(this.elems[..i+1], ss.elems[..j]);
                    if !has_value {
                        result.AppendValue(this.arr[i]);
                        sumSet := sumSet + {this.arr[i]};
                    }
                    i := i + 1;
                }else {
                    assert j < ss.nElems;
                    var has_value := result.HasValue(ss.arr[j]);
                    assert ss.elems[..j+1] == ss.elems[..j]+[ss.arr[j]];
                    ToSetConcat(ss.elems[..j], [ss.arr[j]]);
                    ToSetConcat(this.elems[..i], ss.elems[..j+1]);
                    if !has_value {
                        result.AppendValue(ss.arr[j]);
                            sumSet := sumSet + {ss.arr[j]};
                    }
                    j := j + 1;
                }
            }
            assert i == this.nElems;
            assert j == ss.nElems;
            ToSetConcat(this.elems[..this.nElems], ss.elems[..ss.nElems]);
        }


    }

    method Main()
    {
        var gs := new GrowableSortedSet(5);
        assert gs.nElems == 0;
        var foo := gs.AddValue(5);
        assert 5 in gs.elems;
        foo := gs.AddValue(10);
        assert 10 in gs.elems;
        assert |gs.elems| == 2;
        foo := gs.AddValue(3);
    }

    function ToSet<A>(xs: seq<A>): set<A>
        ensures forall x :: x in ToSet(xs) ==> x in xs
        ensures forall x :: x !in ToSet(xs) ==> x !in xs
    {
        if xs == [] then {} else {xs[0]}+ToSet(xs[1..])
    }

    lemma ToSetConcat<T>(xs: seq<T>, ys: seq<T>)
        ensures ToSet(xs+ys) == ToSet(xs) + ToSet(ys)
    {

    }

    lemma ToSetPlusOne<T>(xs: seq<T>, x: T)
        requires x !in ToSet(xs)
        requires Distinct(xs)
        ensures ToSet(xs + [x]) == ToSet(xs) + {x}
    {
        if xs == [] {
            assert ToSet([x]) == {x};
        }else{
            assert xs[0] != x;
            ToSetPlusOne(xs[1..], x);
        }
    }

    twostate lemma ArrayShift(arr: array<int>, index: nat, nElems: nat)
        requires 0 < index <= nElems < arr.Length
        requires arr[index+1..nElems+1] == old(arr[index..nElems])
        requires arr[index] == old(arr[index-1])
        ensures arr[index..nElems+1] == old(arr[index-1..nElems])
    {
    }

    predicate OrderedArray(arr: array<int>, nElems: nat) 
        requires nElems <= arr.Length
        reads arr
    {
        forall i :: 0 < i < nElems ==> arr[i-1] < arr[i]
    }

    predicate SortedArray(arr: array<int>, nElems: nat) 
        requires nElems <= arr.Length
        reads arr
    {
        forall j,k :: 0 <= j < k  < nElems ==> arr[j] < arr[k]
    }

    lemma SortedArrayIsDisjoint(arr: array<int>, nElems: nat, elems: seq<int>, i: nat)
        requires nElems <= arr.Length
        requires SortedArray(arr, nElems)
        requires nElems == |elems|
        requires forall i: nat :: i < nElems ==> arr[i] == elems[i]
        requires i <= nElems
        ensures ToSet(elems[..i]) !! ToSet(elems[i..nElems])
    {

    }

    lemma SetsCombined(ss: set<int>, thisElems: seq<int>, nElems: nat, ssElems: seq<int>, ssNelems: nat, i: nat)
        requires |thisElems| == nElems
        requires i < ssNelems
        requires |ssElems| == ssNelems
        requires ssElems[i] !in ss
        requires ss == ToSet(thisElems[..nElems]) + ToSet(ssElems[..i])
        requires ss+{ssElems[i]} == ToSet(thisElems[..nElems]) + ToSet(ssElems[..i+1])
    {

    }

    lemma SetsCombined2(ss: set<int>, thisElems: seq<int>, nElems: nat, ssElems: seq<int>, ssNelems: nat, i: nat)
        requires |thisElems| == nElems
        requires i < ssNelems
        requires |ssElems| == ssNelems
        requires ssElems[i] in ss
        requires ss == ToSet(thisElems[..nElems]) + ToSet(ssElems[..i])
        requires ss == ToSet(thisElems[..nElems]) + ToSet(ssElems[..i+1])
    {

    }

    lemma SetsCombinedImplies(res: seq<int>, thisElems: seq<int>, nElems: nat, ssElems: seq<int>, ssNelems: nat)
        requires |thisElems| == nElems
        requires |ssElems| == ssNelems
        requires ToSet(res) == ToSet(thisElems[..nElems]) + ToSet(ssElems[..ssNelems])
        ensures forall x :: x in thisElems[..nElems] ==> x in res
        ensures forall x :: x in ssElems[..ssNelems] ==> x in res
    {

    }

    lemma ElementInserted(resultElems: seq<int>, ss: set<int>,  thisElems: seq<int>, nElems: nat, ssElems: seq<int>, ssNelems: nat, i: nat, index: nat)
        requires |thisElems| == nElems
        requires i < ssNelems
        requires |ssElems| == ssNelems
        requires ssElems[i] !in ss
        requires ss == ToSet(thisElems[..nElems]) + ToSet(ssElems[..i])
        requires index <= |resultElems|
        requires ToSet(resultElems) == ToSet(thisElems[..nElems]) + ToSet(ssElems[..i])
        ensures ToSet(resultElems[..index]+[ssElems[i]]+resultElems[index..]) == ss+{ssElems[i]}
    {

    }

    lemma ElementAppendedOne(resultElems: seq<int>, ss: set<int>,  thisElems: seq<int>, nElems: nat, i: nat)
        requires |thisElems| == nElems
        requires i < nElems
        requires thisElems[i] !in ss
        // requires Distinct(thisElems)
        requires Distinct(resultElems)
        requires ToSet(resultElems) == ss
        requires ss == ToSet(thisElems[..i])
        ensures ToSet(resultElems + [thisElems[i]]) == ss+{thisElems[i]}
    {
        assert thisElems[i] !in ToSet(resultElems);
        ToSetPlusOne(resultElems, thisElems[i]);
    }

    // lemma ElementAppendedTwo(resultElems: seq<int>, ss: set<int>,  thisElems: seq<int>, nElems: nat, ssElems: seq<int>, ssNelems: nat, i: nat)
    //     requires |thisElems| == nElems
    //     requires i < ssNelems
    //     requires |ssElems| == ssNelems
    //     requires ssElems[i] !in ss
    //     requires ss == ToSet(thisElems[..nElems]) + ToSet(ssElems[..i])
    //     requires ToSet(resultElems) == ToSet(thisElems[..nElems]) + ToSet(ssElems[..i])
    //     ensures ToSet(resultElems[ssElems[i]]) == ss+{ssElems[i]}
    // {

    // }

    predicate Distinct<T(==)>(ss: seq<T>) {
        forall i, j :: 0 <= i < j < |ss| ==> ss[i] != ss[j]
    }

    lemma OrderedImpliesDistinct(arr: array<int>, elems: seq<int>, nElems: nat)
        requires nElems <= arr.Length
        requires nElems == |elems|
        requires OrderedArray(arr, nElems)
        requires forall i :: 0 <= i < nElems ==> arr[i] == elems[i]
        ensures Distinct(elems)
    {
        forall i, j | 0 <= i < j < nElems
            ensures elems[i] != elems[j]
        {
            IncreasingIndexIsGreater(arr, nElems, i, j);
        }
    }


    lemma IncreasingIndexIsGreater(arr: array<int>, nElems: nat, i: nat, j: nat)
        requires nElems <= arr.Length
        requires OrderedArray(arr, nElems)
        requires i < j < nElems
        ensures arr[i] < arr[j]
    {
        if j == i + 1 {
            assert arr[i] < arr[j];
        }else{
            IncreasingIndexIsGreater(arr, nElems, i, j-1);
            assert arr[i] < arr[j-1] < arr[j];
        }
    }


    lemma OrderedImpliesSorted(arr: array<int>, nElems: nat)
        requires nElems <= arr.Length
        requires OrderedArray(arr, nElems)
        ensures SortedArray(arr, nElems)
    {
        forall i, j | 0 <= i < j < nElems
            ensures arr[i] < arr[j]
        {
            IncreasingIndexIsGreater(arr, nElems, i, j);
        }
    }
}