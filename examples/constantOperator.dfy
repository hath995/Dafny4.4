module IndexOf {
    method IndexOf( s: seq<int>, value: int) returns (index: int)
        // Answers the index of value in s:
        requires value in s
        ensures 0 <= index < |s|
        ensures s[index] == value
        ensures value !in s[0..index]
    {
        ghost var numIterations := 0;
        ghost var numFirstBranch := 0;
        var result := -1;
        for i := 0 to |s|
            invariant result == -1 ==> value !in s[0..i]
            invariant result < |s|
            invariant result >= 0 ==> value !in s[0..result]
            invariant result >= 0 ==> s[result] == value
            invariant numIterations == i
            invariant result != -1 ==> numFirstBranch==1
            invariant result == -1 ==> numFirstBranch==0
            { 
                numIterations := numIterations + 1;
                if (s[i] == value) && (result == -1) 
                {
                    numFirstBranch := numFirstBranch + 1;
                    result := i;
                    break;
                }
            }
        assert numIterations <= |s|;
        assert numFirstBranch == 1;
        return result;
    }
}