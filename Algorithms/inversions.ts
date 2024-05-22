function countInversions(xs: number[]): number {
    let count = 0;
    for (let i = 0; i < xs.length -1; i++) {
        for (let j = i + 1; j < xs.length; j++) {
            if (xs[i] > xs[j]) {
                count++;
            }
        }
    }
    return count;
}

function SortAndCountInv(xs: number[]): [number, number[]] {
    if (xs.length <= 1) {
        return [0, xs];
    }
    const n = xs.length;
    const m = Math.floor(n / 2);
    const [a, b] = [xs.slice(0, m), xs.slice(m)];
    // console.log("a b", a, b);
    const [ra, sa] = SortAndCountInv(a);
    const [rb, sb] = SortAndCountInv(b);
    // console.log("ra sa rb sb", ra, sa, rb, sb);
    const [r, s] = MergeAndCountSplitInv(sa, sb);
    return [ra + rb + r, s];
}

function MergeAndCountSplitInv(xs: number[], ys: number[]): [number, number[]] {
    const zs: number[] = [];
    const n = xs.length + ys.length;
    let i = 0;
    let j = 0;
    var k = 0;
    let count = 0;
    while (k < n) {
        // console.log("i j", i, j, xs[i], ys[j]);
        if (i < xs.length && xs[i] <= ys[j] || j >= ys.length) {
            zs.push(xs[i]);
            i++;
        } else {
            zs.push(ys[j]);
            j++;
            count += (xs.length - i);
        }
        k++;
    }
    return [count, zs];
}
// var sample = [1, 3, 5, 2, 4, 6];
// var sample = [4, 5, 6, 1, 2, 3];
var sample = [1, 2, 5, 6, 7, 7, 8];
console.log(SortAndCountInv(sample), countInversions(sample));