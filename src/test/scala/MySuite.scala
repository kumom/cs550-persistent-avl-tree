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
}
