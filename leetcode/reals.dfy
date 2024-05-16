
function divq(x: real, y: real): (z: real)
    requires y != 0.0
{
    x/y
}

lemma sqrt(x: real, y: real) 
    requires x > 0.0
    requires y > 0.0 && y*y ==x
{
    assert divq(x, y) == y;
    var sq :| sq != 0.0 && divq(x, sq) == sq;
}