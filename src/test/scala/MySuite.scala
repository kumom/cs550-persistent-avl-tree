// For more information on writing tests, see
// https://scalameta.org/munit/docs/getting-started.html
class MySuite extends munit.FunSuite {
  import Array._

  test("simple") {
    val tree: AVLTree = Empty.insert(0)

    assert(tree.has(0))
    assert(!tree.has(1))
  }

  test("inserting big") {
    var tree: AVLTree = Empty
    range(-1000, 1000).foreach((x: Int) => {
      tree = tree.insert(BigInt(x))
    })
    range(-1000, 1000).foreach((x: Int) => {
      assert(tree.has(BigInt(x)))
    })
  }

  test("immutability") {
    val tree = Empty.insert(0)
    val tree2 = tree.insert(1)

    assert(tree2.has(1))
    assert(tree2.has(0))
    assert(!tree.has(1))
  }

  test("non-ordered insertions") {
    var tree: AVLTree = Empty

    // inserts 0, -1, 2, -3, ...
    range(0, 150).foreach((x: Int) => {
      tree = tree.insert(x * BigInt(-1).pow(x))
    })

    range(0, 150).foreach((x: Int) => {
      assert(tree.has(x * BigInt(-1).pow(x)))
    })
  }

  test("simple delete") {
    var tree: AVLTree = Empty.insert(15)
    tree = tree.delete(15)

    assert(!tree.has(15))
  }

  test("big delete") {
    var tree: AVLTree = Empty
    range(-500, 500).permutations.next().foreach((x: Int) => {
      tree = tree.insert(x)
    })
    
    range(-500, 500).permutations.next().foreach((x: Int) => {
      tree = tree.delete(x)
    })

    // every element was deleted
    assert(range(-500, 500).forall((x: Int) => {
      !tree.has(x)
    }))
  }

  test("multiple delete") {
    val arr = Array(-15, 20, 30, 14, -11, 20340)
    var tree: AVLTree = Empty
    
    for (v <- arr) {
      tree = tree.insert(v)
    }
    
    for (v <- arr) {
      assert(tree.has(v))
    }

    for (v <- arr) {
      assert(tree.has(v))
      tree = tree.delete(v)
      assert(!tree.has(v))
    }
  }

  test("double insert") {
    // double insert should be ignored
    val tree = Empty.insert(5).insert(5).delete(5)
    assert(tree == Empty)
  }

  test("remove not existing") {
    val tree = Empty.insert(12).delete(5)

    assert(tree.has(12))
    assert(!tree.has(5))
  }

}
