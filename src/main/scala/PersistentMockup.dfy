class PersistentAVLTree {
  ghost var Repr: set<object>
  var roots: seq<AVLTree?>
  var time: int

  predicate Valid()
    reads this
  {
    |roots| > 0 && roots[0] == null && time >= 0 && time == |roots| - 1 &&
    (forall r :: r in roots && r != null ==> r.isAVL())
  } 

  constructor Init()
    ensures Valid() && fresh(Repr)
  {
    roots := [null];
    time := 0;
    Repr := {this};
  }

  function method Root() : (r: AVLTree?)
    reads this
    requires Valid()
    ensures Valid() 
    ensures r != null ==> r.isAVL()
  {
    roots[|roots| - 1]
  }

  method Insert(x: int) 
    requires Valid()
    modifies this
  {
    var r := Root();
    if r == null {
      var newR := new AVLTree.Init();
      roots := roots + [newR];
    } else {
      var newR := Root().Insert(x);
      roots := roots + [newR];
    }
  }

  method Remove(x: int) 
    requires Valid()
    modifies this
  {
    var r := Root();
    if r == null {
      roots := roots + [null];
    } else {
      var newR := Root().Remove(x);
      roots := roots + [newR];
    }
  }

  function method Contains(x: int, t: int) : (found: bool)
    reads this
    requires Valid()
    requires t >= 0
  {
    if t <= time then
      var r := roots[t];
      if r != null then
        r.Contains(x)
      else
        false
    else  
      var r := Root();
      if r != null then
        r.Contains(x)
      else
        false
  }
}

class AVLTree {
    predicate isAVL() {
        true
    }

    constructor Init()
    ensures isAVL()
  {
  }

    method Insert(x: int) returns (t: AVLTree) {
      t := this;
    }

    method Remove(x: int) returns (t: AVLTree) {
      t := this;
    }

    function method Contains(x: int) : (found: bool) {
      true
    }
}