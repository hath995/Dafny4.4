//https://leino.science/papers/krml190.pdf

module krml190 {

    function toMultiset<T>(node: Node?<T>): multiset<T>
        reads set x | node != null && x in node.footprint
        requires node != null ==> node.Valid()
        decreases if node == null then {} else node.footprint
    {
       if node == null then multiset{} else
       assert node.Valid();
       multiset{node.data}+toMultiset(node.next) 
    }

    class Node<T(==)> {
        ghost var list: seq<T>
        ghost var parent: Node?<T>
        ghost var footprint: set<Node<T>>
        ghost var ancestorRepr: set<Node<T>>

        var data: T
        var next: Node?<T>

        constructor(d: T, ghost parent: Node?<T>) 
            // requires parent != null ==> parent.AncestorValid()
            ensures this.data == d
            ensures this.list == [d]
            ensures this.parent == parent
            ensures Valid()
            // ensures AncestorValid()
        {
            this.data := d;
            this.list := [d];
            this.next := null;
            this.parent := parent;
            // this.parent.next := this;
            this.ancestorRepr := if parent == null then {} else {parent}+parent.ancestorRepr;
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

        ghost predicate AncestorValid() 
            reads this, ancestorRepr
            decreases ancestorRepr
        {
            this !in ancestorRepr &&
            (parent == null ==> ancestorRepr == {}) &&
            (parent != null ==> 
                parent in ancestorRepr &&
                ancestorRepr == {parent}+parent.ancestorRepr && 
                (parent !in parent.ancestorRepr) &&
                parent.next == this &&
                (parent.parent != null ==> parent.AncestorValid()))
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
            ensures multiset(r.list) == multiset(list)+multiset{d}
        {
            r := new Node(d, null);
            r.next := this;
            r.footprint := {r}+footprint;
            r.list := [d]+r.next.list;
        }

        method InsertAfter(d: T) returns (head: Node<T>)
            requires Valid()
            requires AncestorValid()
            ensures head.Valid()
            ensures fresh(head.footprint - old(footprint)-old(ancestorRepr))
        {
            if head.parent == null {
                
            }else{

            }
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