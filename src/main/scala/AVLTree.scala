import stainless.collection._
import stainless.proof._
import stainless.lang._
import stainless.annotation._

sealed abstract class AVLTree {
    def content: Set[BigInt]

    def balanceFactor: BigInt
    def height: BigInt

    // impl only to make stainless happy
    def insert(v: BigInt): AVLTree = {
        require(this.isAVL())
        this
    }

    def has(v: BigInt): Boolean

    // impl only to make stainless happy
    def delete(v: BigInt): AVLTree = {
        require(this.isAVL())
        this
    }

    // impl only to make stainless happy
    def balanced(): AVLTree = {
        require(this.isAlmostAVL())
        this
    }

    // for verification
    def isAVL(): Boolean
    def isAlmostAVL(): Boolean
    
    def isBST(): Boolean

    def inorder(): List[BigInt]
}

case object Empty extends AVLTree {
    override def content: Set[BigInt] = Set.empty

    override def balanceFactor: BigInt = 0
    override def height: BigInt = {
        BigInt(-1)
    }.ensuring(res => res >= -1)
    override def insert(v: BigInt): AVLTree = Branch(v, Empty, Empty)

    override def delete(v: BigInt): AVLTree = this

    override def has(v: BigInt): Boolean = false

    override def balanced(): AVLTree = this

    override def isAlmostAVL(): Boolean = true

    override def isAVL(): Boolean = true

    override def isBST(): Boolean = true

    override def inorder(): List[BigInt] = List.empty[BigInt]
}

def maxBigInt(a: BigInt, b: BigInt): BigInt = {
    if a > b then a else b
}

case class Branch(v: BigInt, left: AVLTree, right: AVLTree) extends AVLTree {
    override def content: Set[BigInt] = left.content ++ Set(v) ++ right.content

    override def balanceFactor: BigInt = right.height - left.height
    
    override def height: BigInt = {
        maxBigInt(left.height, right.height) + 1
    }.ensuring(res => res >= -1)
    override def has(v: BigInt): Boolean = {
        if this.v == v then
            true 
        else if v < this.v then
            left.has(v)
        else
            right.has(v)
    }

    override def insert(v: BigInt): AVLTree = {
        require(this.isAVL())
        if this.v == v then
            this
        else if v < this.v then {
            val res = Branch(this.v, this.left.insert(v), this.right)
            assert(res.isBST())
            res.balanced()
        }
            
        else
            Branch(this.v, this.left, this.right.insert(v)).balanced()
    }.ensuring(res => res.isAVL() && res.height <= this.height + 1 && res.height >= this.height)

    override def delete(v: BigInt): AVLTree = {
        require(this.isAVL())
        if this.v == v then {
            if this.left == Empty then
                this.right
            else if this.right == Empty then 
                this.left
            else {
                // find biggest in left subtree -> it has no right child
                // move value from it into root of result
                val left = this.left.asInstanceOf[Branch]
                val max = left.max()
                Branch(max, left.delete(max), this.right).balanced() // left.delete(max) is simple since max has no right child
            }
        } else if v < this.v then
            Branch(this.v, this.left.delete(v), this.right).balanced()
        else 
            Branch(this.v, this.left, this.right.delete(v)).balanced()
    }.ensuring(res => res.isAVL() && res.height <= this.height && res.height >= this.height - 1)

    def max(): BigInt = {
        this.right match {
            case Empty => v
            case b: Branch => b.max()
        }
    }
    override def balanced(): AVLTree = {
        require(this.isAlmostAVL())
        if this.balanceFactor == 2 then {
            if this.right.balanceFactor == -1 then
                this.rotateRightLeft()
            else if this.right.balanceFactor == 1 then
                this.rotateLeft()
            else
                this.rotatePlus()
        } else if this.balanceFactor == -2 then {
            if this.left.balanceFactor == 1 then
                this.rotateLeftRight()
            else if this.left.balanceFactor == -1 then
                this.rotateRight()
            else
                this.rotateMinus()
        } else
            this
    }.ensuring(res => res.isAVL())

    def rotatePlus(): AVLTree = {
        require(this.isAlmostAVL() && this.balanceFactor == 2 && this.right.balanceFactor == 0)
        assert(this.left.height >= -1)
        assert(this.right.height >= 1)
        val Branch(u, a, x) = this
        // argument: just simple rotation is enough
        val Branch(v, b, c) = x.asInstanceOf[Branch]
        Branch(v, Branch(u, a, b), c)
    }.ensuring(res => res.isAVL())

    // this is +2, right child is +1
    def rotateLeft(): AVLTree = {
        require(this.isAlmostAVL() && this.balanceFactor == 2 && this.right.balanceFactor == 1)
        val Branch(w, a, rChild) = this
        val Branch(u, b, c) = rChild.asInstanceOf[Branch]
        assert(b.isAVL())
        assert(a.isAVL())
        val res = Branch(u, Branch(w, a, b), c)
        assert(this == Branch(w, a, Branch(u, b, c)))
        assert(Branch(w, a, Branch(u, b, c)).inorder() == a.inorder() ++ (w :: Branch(u, b, c).inorder()))
        assert(a.inorder() ++ (w :: Branch(u, b, c).inorder()) == a.inorder() ++ (w :: (b.inorder() ++ (u :: c.inorder()))))
        assert(this.inorder() == a.inorder() ++ (w :: (b.inorder() ++ (u :: c.inorder()))))

        assert(res == Branch(u, Branch(w, a, b), c))
        assert(Branch(u, Branch(w, a, b), c).inorder() == Branch(w, a, b).inorder() ++ (u :: c.inorder()))
        assert(Branch(w, a, b).inorder() ++ (u :: c.inorder()) == a.inorder() ++ (w :: b.inorder()) ++ (u :: c.inorder()))
        assert(res.inorder() == a.inorder() ++ (w :: b.inorder()) ++ (u :: c.inorder()))

        val two = (w :: b.inorder()) ++ (u :: c.inorder())

        ListSpecs.appendAssoc(a.inorder(), w :: b.inorder(), u :: c.inorder())
        assert(a.inorder() ++ (w :: b.inorder()) ++ (u :: c.inorder()) == a.inorder() ++ ((w :: b.inorder()) ++ (u :: c.inorder())))
        // here is assoc of append
        assert(a.inorder() ++ (w :: b.inorder()) ++ (u :: c.inorder()) == a.inorder() ++ two)

        val one = w :: (b.inorder() ++ (u :: c.inorder()))

        assert(res.inorder() == a.inorder() ++ two)
        assert(this.inorder() == a.inorder() ++ one)

        assert(ugly(w, u, b, c))
        assert(one == two || two == one)
        assert(a.inorder() ++ one == a.inorder() ++ two)
 
        assert(this.inorder() == res.inorder())
        assert(this.isBST())
        assert(sorted(this.inorder()))
        assert(sorted(res.inorder()))
        assert(res.isBST())
        // remaind what res is
        assert(res == Branch(u, Branch(w, a, b), c))
        assert(this.isAlmostAVL())
        inorderPropMore(Branch(w, a, b))
        assert(b.inorder().forall(_ > w))
        assert(sorted(b.inorder()))
        prependOneSorted(w, b.inorder())
        assert(sorted(w :: b.inorder())) // !

        assert(sorted(a.inorder()))
        inorderPropLess(Branch(w, a, b))
        assert(a.inorder().forall(_ < w))
        appendOneSorted(w, a.inorder())
        assert(sorted(a.inorder() :+ w)) // !

        mergeSorted(a.inorder(), w, b.inorder())
        assert(Branch(w, a, b).isBST())
        assert(Branch(w, a, b).isAVL())
        assert(res.isAlmostAVL())
        assert(res.isAVL())
        res
    }.ensuring(res => res.isAVL() && res.inorder() == this.inorder())

    private def hasLeftBranch() = {
        require(this.isAVL() && this.balanceFactor == -1)
    }.ensuring(_ => this.left.isInstanceOf[Branch])
    
    // this is on +2, right child is on -1
    def rotateRightLeft(): AVLTree = {
        require(this.isAlmostAVL() && this.balanceFactor == 2 && this.right.balanceFactor == -1)
        val Branch(w, a, rChild) = this
        val rBranch = rChild.asInstanceOf[Branch]
        val Branch(u, lGrandchild, d) = rBranch
        rBranch.hasLeftBranch()
        val Branch(z, b, c) = lGrandchild.asInstanceOf[Branch]
        Branch(z, Branch(w, a, b), Branch(u, c, d))
    }.ensuring(res => res.isAVL())

    def rotateMinus(): AVLTree = {
        require(this.isAlmostAVL() && this.balanceFactor == -2 && this.left.balanceFactor == 0)
        assert(this.right.height >= -1)
        assert(this.left.height >= 1)
        val Branch(u, x, c) = this
        // argument: just simple rotation is enough
        val Branch(v, a, b) = x.asInstanceOf[Branch]
        Branch(v, a, Branch(u, b, c))
    }.ensuring(res => res.isAVL())


    def rotateRight(): AVLTree = {
        require(this.isAlmostAVL() && this.balanceFactor == -2 && this.left.balanceFactor == -1)
        val Branch(w, lChild, c) = this
        val Branch(u, a, b) = lChild.asInstanceOf[Branch]
        Branch(u, a, Branch(w, b, c))
    }.ensuring(res => res.isAVL())

    private def hasRightBranch() = {
        require(this.isAVL() && this.balanceFactor == 1)
    }.ensuring(_ => this.right.isInstanceOf[Branch])

    def rotateLeftRight(): AVLTree = {
        require(this.isAlmostAVL() && this.balanceFactor == -2 && this.left.balanceFactor == 1)
        val Branch(w, lChild, d) = this
        val lBranch = lChild.asInstanceOf[Branch]
        val Branch(u, a, rGrandchild) = lBranch
        lBranch.hasRightBranch()
        val Branch(z, b, c) = rGrandchild.asInstanceOf[Branch]
        Branch(z, Branch(u, a, b), Branch(w, c, d))
    }.ensuring(res => res.isAVL())

    override def isAVL(): Boolean = {
        this.isAlmostAVL() && this.balanceFactor < 2 && this.balanceFactor > -2
    }

    override def isAlmostAVL(): Boolean = {
        this.isBST() && this.balanceFactor <= 2 && this.balanceFactor >= -2 && this.left.isAVL() && this.right.isAVL()
    }
    override def isBST(): Boolean = {
        sorted(this.inorder())
    }

    override def inorder(): List[BigInt] = {
        this.left.inorder() ++ (this.v :: this.right.inorder())
    }.ensuring(res => res.content == this.content)
}

def inorderSpread(@induct xs: List[BigInt], ys: List[BigInt]): Boolean = (
    sorted(xs ++ ys) == (
        sorted(xs) &&
        sorted(ys) &&
        (xs.isEmpty || ys.isEmpty || xs.last < ys.head)
    )
).holds

def mergeSorted(@induct xs: List[BigInt], y: BigInt, ys: List[BigInt]): Boolean = (
    sorted(xs ++ (y :: ys)) == (
        sorted(xs :+ y) &&
        sorted(y :: ys)
    ) && inorderSpread(xs, y :: ys)
).holds


def inorderPropLess(n: AVLTree): Boolean = {
    n match
        case Empty => true
        case Branch(v, left, right) => left.inorder().forall(_ < v)
}.holds

def inorderPropMore(n: AVLTree): Boolean = {
    n match
        case Empty => true
        case Branch(v, left, right) => right.inorder().forall(_ > v)
}.holds


// w :: (b.inorder() ++ (u :: c.inorder())) == (w :: b.inorder()) ++ (u :: c.inorder())
def ugly(w: BigInt, u: BigInt, b: AVLTree, c: AVLTree): Boolean = {
    w :: (b.inorder() ++ (u :: c.inorder())) == (w :: b.inorder()) ++ (u :: c.inorder())
}.holds

def sorted(list: List[BigInt]): Boolean = {
    list match
        case Cons(x, Cons(y, ys)) => x < y && sorted(Cons(y, ys))
        case _ => true
}

def greater(x: BigInt, a: List[BigInt]): Boolean = {
    a match
        case Cons(h, t) => x > h && greater(x, t) 
        case Nil() => true
}

def appendOneSorted(x: BigInt, @induct a: List[BigInt]): Boolean = {
    require(sorted(a) && a.forall(_ < x))
    sorted(a :+ x)
}.holds


def prependOneSorted(x: BigInt, @induct a: List[BigInt]): Boolean = {
    require(sorted(a) && a.forall(_ > x))
    sorted(x :: a)
}.holds

def syntaxSugar(xs: List[BigInt], x: BigInt): Boolean = {
    (xs :+ x) == xs ++ List(x) && (x :: xs) == (List(x) ++ xs)
}.holds

def treeAssocLeft(n: AVLTree): Option[(List[BigInt], List[BigInt], List[BigInt])] = {
    n match {
        case Empty => None()
        case Branch(v, left, right) => {
            left match {
                case Empty => None()
                case Branch(lv, ll, lr) => {
                    val l1 = ll.inorder()
                    val l2 = lv :: lr.inorder()
                    val l3 = v :: right.inorder()
                    ListSpecs.appendAssoc(l1, l2, l3)
                    Some((l1, l2, l3))
                }
            }
        }
    }
}

def treeAssocLeftHolds(n: AVLTree): Boolean = {
    val opt = treeAssocLeft(n)
    opt match
        case Some((l1, l2, l3)) => n.inorder() == l1 ++ (l2 ++ l3)
        case None() => true
}.holds

def treeAssocRight(n: AVLTree): Option[(List[BigInt], List[BigInt], List[BigInt])] = {
    n match {
        case Empty => None()
        case Branch(v, left, right) => {
            right match {
                case Empty => None()
                case Branch(rv, rl, rr) => {
                    val l1 = left.inorder()
                    val l2 = v :: rl.inorder()
                    val l3 = rv :: rr.inorder()
                    ListSpecs.appendAssoc(l1, l2, l3)
                    // n.inorder() == (l1 ++ l2) ++ l3
                    Some((l1, l2, l3))
                }
            }
        }
    }
}

def treeAssocRightHolds(n: AVLTree): Boolean = {
    val opt = treeAssocRight(n)
    opt match
        case Some((l1, l2, l3)) => n.inorder() == (l1 ++ l2) ++ l3
        case None() => true
}.holds
