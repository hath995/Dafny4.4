/*
function isPalindrome(s: string): boolean {
    const length = s.length;
    const halfLength = length >> 1;
    if(s.length == 1) return true;
    for(let i = 0; i < halfLength; i++) {
        if(s[i] !== s[length - 1 - i]) return false;
    }
    return true;
}

function isPalindrome2(s: string, start: number, length: number): boolean {
    const halfLength = length >> 1;
    if(length == 1) return true;
    for(let i = 0; i < halfLength; i++) {
        if(s[start+i] !== s[(start+length) - 1 - i]) return false;
    }
    return true;
}

function longestPalindrome(s: string): string {
    if(s.length == 1) return s;
    for(let i = s.length; i > 0; i--) {
        for(let j=0; j+i<=s.length; j++) {
            //let slice = s.slice(j,j+i);
            //console.log(i, j, slice, j,j+i);
            if(isPalindrome2(s, j, i)) return s.slice(j, j+i);
        }
    }
    throw new Error("got here:"+s);
}
*/

function isPalindrome(s: string, i: nat): bool
    requires i <= |s|/2
    decreases |s|-i
{
    if |s| == 1 then true else if i < |s|/2 then s[i] == s[ |s| - 1 - i ] && isPalindrome(s, i+1) else true
}

method isPalindromeMethod(s: string) returns (palindrome: bool) 
    ensures palindrome <==> isPalindrome(s, 0)
{
    if |s| == 1 {
        return true;
    }
    for i := 0 to |s|/2 
        invariant forall k :: 0 <= k < i ==> s[i] == s[|s|-1-i]
    {
        if s[i] != s[|s| - 1 - i] {
            return false;
        }
    }
    return true;
}

method TesT() {
    var sample := "a";
    var sampleaba := "aba";
    var samplebb := "bb";
    assert isPalindrome(sample, 0);
    assert isPalindrome(sampleaba, 0);
    assert isPalindrome(samplebb, 0);
    assert !isPalindrome("dcbbc",0);
}