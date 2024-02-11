//https://leino.science/papers/krml190.pdf

module krml190 {

    class Node<T(==)> {
        ghost var list: seq<T>
        ghost var footprint: set<Node<T>>

        var data: T
        var next: Node?<T>

        constructor(d: T) 
            ensures this.data == d
            ensures this.list == [d]
            ensures Valid()
        {
            this.data := d;
            this.list := [d];
            this.next := null;
            this.footprint := {this};
        }

        ghost predicate Valid()
            reads this, footprint
        {
            this in this.footprint &&
            null !in footprint &&
            (next == null ==> list == [data]) &&
            (next != null ==>
                next in footprint && 
                this !in next.footprint &&
                next.footprint < footprint &&
                list == [data]+next.list &&
                next.Valid()
                )
        }

        method SkipHead() returns (r: Node?<T>)
            requires Valid()
            ensures r == null ==> |list| == 1
            ensures r != null ==> r.Valid() && r.footprint < footprint
            ensures r != null ==> r.list == list[1..]
        {
            r := this.next;
        }

        method Prepend(d: T) returns (r: Node<T>)
            requires Valid()
            ensures r.Valid() && fresh(r.footprint-old(footprint))
            ensures r.list == [d]+list
        {
            r := new Node(d);
            r.next := this;
            r.footprint := {r}+footprint;
            r.list := [d]+r.next.list;
        }

        method ReverseInPlace() returns (reverse: Node<T>)
            requires Valid()
            modifies footprint
            ensures reverse != null && reverse.Valid()
            ensures fresh(reverse.footprint - old(footprint))
            ensures |reverse.list| == |old(list)|
            ensures forall i :: 0 <= i < |old(list)| ==> old(list)[i] == reverse.list[|old(list)|-i-1]
        {
            var curr:= next;
            reverse := this;
            reverse.next := null;
            reverse.footprint := {reverse};
            reverse.list := [data];

            while curr != null 
                invariant reverse != null && reverse.Valid()
                invariant reverse.footprint <= old(footprint)
                invariant curr == null ==> |old(list)| == |reverse.list|
                invariant curr != null ==> 
                    curr.Valid() &&
                    curr in old(footprint) &&
                    curr.footprint <= old(footprint) &&
                    curr.footprint !! reverse.footprint &&
                    |old(list)| == |reverse.list|+|curr.list| &&
                    forall i :: 0 <= i < |curr.list| ==> curr.list[i] == old(list)[|reverse.list|+i]
                invariant forall i :: 0 <= i < |reverse.list| ==> old(list)[i] == reverse.list[|reverse.list|-1-i]
                decreases if curr != null then  curr.footprint else {}
            {
                var nx:= curr.next;
                assert nx != null ==> forall i :: 0 <= i < |nx.list| ==> curr.list[1+i] == nx.list[i];
                assert curr.data == curr.list[0];
                curr.next:= reverse;
                curr.footprint := {curr}+reverse.footprint;
                curr.list := [curr.data]+reverse.list;
                assert curr.Valid();
                reverse := curr;
                curr := nx;
            }
        }

    }
}