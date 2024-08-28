
//https://whileydave.com/2023/09/16/efficient-functions-in-dafny/
//https://github.com/Consensys/evm-dafny/blob/37b638546f7449e78d745a74cbdd2b1a14d60ccb/src/dafny/util/int.dfy#L282
module EfficientFunctions {
    type u8 = bv8
    function ToBytes(v:nat) : (r:seq<u8>)
    ensures |r| > 0
    {
        // Extract the byte
        var b : u8 := (v % 256) as u8;
        // Determine what's left
        var w : nat := v/256;
        if w == 0 then [b]
        else
            ToBytes(w) + [b]
    }

   lemma LemmaFromBytes(bytes:seq<u8>,i:nat)
    requires i < |bytes|
    ensures FromBytes(bytes[..i+1]) == (FromBytes(bytes[..i]) * 256) + bytes[i] as nat {
        if i != 0 {
            var cons := bytes[..i+1];
            var tail := bytes[..i];
            var head := bytes[i];
            // For reasons unknown, Dafny cannot figure this out for itself.
            assert (cons == tail + [head]);
        }
    }

    lemma LemmaFromToBytes(v: nat)
    ensures FromBytes(ToBytes(v)) == v
    {}

    function FromBytes(bytes:seq<u8>) : (r: nat)
    {
        if |bytes| == 0 then 0
        else
            var last := |bytes| - 1;
            var byte := bytes[last] as nat;
            var msw := FromBytes(bytes[..last]);
            (msw * 256) + byte
    } by method {
        r := 0;
        for i := 0 to |bytes|
        invariant r == FromBytes(bytes[..i])
        {
            var ith := bytes[i] as nat;
            r := (r * 256) + ith;
            LemmaFromBytes(bytes,i);
        }
        // Dafny needs help here :)
        assert bytes[..|bytes|] == bytes;
        // Done
        return r;
    }

    function sum(items: seq<nat>) : (r:nat)
    {
        if |items| == 0 then 0
        else items[0] + sum(items[1..])
    } by method {
        r := 0;
        var i : nat := |items|;
        while i > 0
        invariant r == sum(items[i..]) {
            i := i - 1;
            r := r + items[i];
        }
    }

    function add(v1: seq<int>, c: int): (r: seq<int>)
        ensures |r| == |v1|
        ensures forall i :: 0 <= i < |r| ==> r[i] == v1[i] + c
    {
        if |v1| == 0 then []
        else
            [v1[0] + c] + add(v1[1..], c)
    } by method {
        r := [];
        var i : nat := |v1|;
        while i > 0
            invariant |r| == |v1| - i
            invariant r == add(v1[i..], c)
        {
            i := i - 1;
            r := [v1[i] + c] + r;
        }
    }

}