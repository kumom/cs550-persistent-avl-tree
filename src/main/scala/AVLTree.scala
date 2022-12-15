import stainless.collection._
import stainless.proof._
import stainless.lang._
import stainless.annotation._
// import StrictlyOrderedList._

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
    }.ensuring(this.inorder() == _.inorder())

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
        if this.v == v then {
            assert(StrictlyOrderedList.insertEqualLemma(this.left.inorder(), this.v, this.right.inorder(), v))
            assert(this.left.inorder() ++ (this.v :: this.right.inorder()) == StrictlyOrderedList.inorderInsert(this.inorder(), v))
            this
        }
        else if v < this.v then {
            val resLeft = this.left.insert(v)
            val res = Branch(this.v, resLeft, this.right)
            // we need: res.isBST()
            // we know: this.right.isBST()
            assert(res.right.isBST())
            assert(res.left.isBST())

            assert(StrictlyOrderedList.insertSmallerLemma(this.left.inorder(), this.v, this.right.inorder(), v))
            assert(resLeft.inorder() ++ (this.v :: this.right.inorder()) == StrictlyOrderedList.inorderInsert(this.inorder(), v))
            
            val finalRes = res.balanced()
            assert(finalRes.height <= this.height + 1)

            finalRes
        }
        else {
            val resRight = this.right.insert(v)
            val res = Branch(this.v, this.left, resRight)
            assert(res.right.isBST())
            assert(res.left.isBST())

            assert(StrictlyOrderedList.insertBiggerLemma(this.left.inorder(), this.v, this.right.inorder(), v))
            assert(this.left.inorder() ++ (this.v :: resRight.inorder()) == StrictlyOrderedList.inorderInsert(this.inorder(), v))

            val finalRes = res.balanced()
            assert(finalRes.height <= this.height + 1)

            finalRes
        }
    }.ensuring(res => res.isAVL() && res.height <= this.height + 1 && res.height >= this.height - 1 && (res.inorder() == StrictlyOrderedList.inorderInsert(this.inorder(), v)))

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
    }.ensuring(res => res.isAVL() && res.inorder() == this.inorder())

    def rotatePlus(): AVLTree = {
        require(this.isAlmostAVL() && this.balanceFactor == 2 && this.right.balanceFactor == 0)
        assert(this.left.height >= -1)
        assert(this.right.height >= 1)
        val Branch(u, a, x) = this
        // argument: just simple rotation is enough
        val Branch(v, b, c) = x.asInstanceOf[Branch]
        val res = Branch(v, Branch(u, a, b), c)

        assert(this.inorder() == a.inorder() ++ (u :: (b.inorder() ++ (v :: c.inorder()))))
        assert(res.inorder() == (a.inorder() ++ (u :: b.inorder())) ++ (v :: c.inorder()))
        ListSpecs.appendAssoc(a.inorder(), u :: b.inorder(), v :: c.inorder())
        assert(res.inorder() == this.inorder())
        assert(StrictlyOrderedList.isInorder(res.inorder()))
        res.bstTrans()
        assert(res.left.isAVL() && res.right.isAVL())
        assert(res.balanceFactor <= 2 && res.balanceFactor >= -2)
        assert(res.isAlmostAVL())

        res
    }.ensuring(res => res.isAVL() && res.inorder() == this.inorder())

    // this is +2, right child is +1
    def rotateLeft(): AVLTree = {
        require(this.isAlmostAVL() && this.balanceFactor == 2 && this.right.balanceFactor == 1)
        val Branch(w, a, rChild) = this
        val Branch(u, b, c) = rChild.asInstanceOf[Branch]
        assert(b.isAVL())
        assert(a.isAVL())
        val res = Branch(u, Branch(w, a, b), c)

        assert(this.inorder() == a.inorder() ++ (w :: (b.inorder() ++ (u :: c.inorder()))))
        assert(res.inorder() == a.inorder() ++ (w :: b.inorder()) ++ (u :: c.inorder()))
        
        ListSpecs.appendAssoc(a.inorder(), w :: b.inorder(), u :: c.inorder())
        assert(this.inorder() == res.inorder())
        assert(StrictlyOrderedList.isInorder(res.inorder()))
        res.bstTrans()
        assert(res.left.isBST())
        assert(res.left.isAVL())
        assert(res.right.isBST())
        assert(res.right.isAVL())
        // this.isBST() && this.balanceFactor <= 2 && this.balanceFactor >= -2 && this.left.isAVL() && this.right.isAVL()
        assert(res.balanceFactor <= 2 && res.balanceFactor >= -2)
        assert(res.isAlmostAVL())
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
        val res = Branch(z, Branch(w, a, b), Branch(u, c, d))
        // stuff to remember
        assert(res.balanceFactor <= 2 && res.balanceFactor >= -2)
        assert(res.left.isBST() ==> res.left.isAVL())
        assert(res.right.isBST() ==> res.right.isAVL())
        //

        assert(this.inorder() == a.inorder() ++ (w :: ((b.inorder() ++ (z :: c.inorder())) ++ (u :: d.inorder()))))
        assert(res.inorder() == (a.inorder() ++ (w :: b.inorder())) ++ (z :: (c.inorder() ++ (u :: d.inorder()))))
        ListSpecs.appendAssoc(a.inorder(), w :: b.inorder(), (z :: (c.inorder() ++ (u :: d.inorder()))))
        assert((a.inorder() ++ (w :: b.inorder())) ++ (z :: (c.inorder() ++ (u :: d.inorder()))) == a.inorder() ++ ((w :: b.inorder()) ++ (z :: (c.inorder() ++ (u :: d.inorder())))))

        ListSpecs.appendAssoc(a.inorder(), w :: b.inorder(), z :: c.inorder())
        ListSpecs.appendAssoc(w :: b.inorder(), z :: c.inorder(), u :: d.inorder())
        assert(this.inorder() == res.inorder())

        res.bstTrans()
        assert(res.left.isBST())
        assert(res.right.isBST())
        assert(res.left.isAVL())
        assert(res.right.isAVL())
        assert(res.balanceFactor <= 2 && res.balanceFactor >= -2) // remainder
        assert(res.isAlmostAVL())

        res
    }.ensuring(res => res.isAVL() && res.inorder() == this.inorder())

    def rotateMinus(): AVLTree = {
        require(this.isAlmostAVL() && this.balanceFactor == -2 && this.left.balanceFactor == 0)
        assert(this.right.height >= -1)
        assert(this.left.height >= 1)
        val Branch(u, x, c) = this
        val Branch(v, a, b) = x.asInstanceOf[Branch]
        val res = Branch(v, a, Branch(u, b, c))
        assert(res.balanceFactor <= 2 && res.balanceFactor >= -2)
        assert(res.left.isBST() ==> res.left.isAVL())
        assert(res.right.isBST() ==> res.right.isAVL())

        assert(this.inorder() == (a.inorder() ++ (v :: b.inorder())) ++ (u :: c.inorder()))
        assert(res.inorder() == a.inorder() ++ (v :: (b.inorder() ++ (u :: c.inorder()))))
        ListSpecs.appendAssoc(a.inorder(), v :: b.inorder(), u :: c.inorder())
        assert(res.inorder() == this.inorder())
        assert(StrictlyOrderedList.isInorder(res.inorder()))
        res.bstTrans()
        assert(res.balanceFactor <= 2 && res.balanceFactor >= -2)
        assert(res.isAlmostAVL())
        res
    }.ensuring(res => res.isAVL() && res.inorder() == this.inorder())


    def rotateRight(): AVLTree = {
        require(this.isAlmostAVL() && this.balanceFactor == -2 && this.left.balanceFactor == -1)
        val Branch(w, lChild, c) = this
        val Branch(u, a, b) = lChild.asInstanceOf[Branch]
        val res = Branch(u, a, Branch(w, b, c))
        assert(this.inorder() == (a.inorder() ++ (u :: b.inorder())) ++ (w :: c.inorder()))
        assert(res.inorder() == a.inorder() ++ (u :: (b.inorder() ++ (w :: c.inorder()))))
        ListSpecs.appendAssoc(a.inorder(), u :: b.inorder(), w :: c.inorder())

        assert(res.inorder() == this.inorder())
        assert(res.isBST())
        res.bstTrans()
        assert(res.balanceFactor <= 2 && res.balanceFactor >= -2)
        assert(res.isAlmostAVL())
        res
    }.ensuring(res => res.isAVL() && res.inorder() == this.inorder())

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
        val res = Branch(z, Branch(u, a, b), Branch(w, c, d))
        // stuff to remember
        assert(res.balanceFactor <= 2 && res.balanceFactor >= -2)
        assert(res.left.isBST() ==> res.left.isAVL())
        assert(res.right.isBST() ==> res.right.isAVL())
        //
        assert(this.inorder() == (a.inorder() ++ (u :: (b.inorder() ++ (z :: c.inorder())))) ++ (w :: d.inorder()))
        assert(res.inorder() == (a.inorder() ++ (u :: b.inorder())) ++ (z :: (c.inorder() ++ (w :: d.inorder()))))

        appendAssocFour(a.inorder(), u :: b.inorder(), z :: c.inorder(), w :: d.inorder())
        ListSpecs.appendAssoc(a.inorder(), u :: (b.inorder() ++ (z :: c.inorder())), w :: d.inorder())
        assert((a.inorder() ++ (u :: b.inorder())) ++ (z :: (c.inorder() ++ (w :: d.inorder()))) == (a.inorder() ++ (u :: b.inorder())) ++ (z :: (c.inorder()) ++ (w :: d.inorder())))
        assert(res.inorder() == (a.inorder() ++ (u :: b.inorder())) ++ (z :: (c.inorder()) ++ (w :: d.inorder())))
        assert(res.inorder() == a.inorder() ++ ((u :: b.inorder()) ++ (z :: (c.inorder()) ++ (w :: d.inorder()))))

        assert(this.inorder() == (a.inorder() ++ (u :: (b.inorder() ++ (z :: c.inorder())))) ++ (w :: d.inorder()))
        // ListSpecs.appendAssoc(a.inorder(), u :: (b.inorder() ++ (z :: c.inorder())), w :: d.inorder())
        // assert((a.inorder() ++ (u :: b.inorder())) ++ (z :: (c.inorder()) ++ (w :: d.inorder())) == (a.inorder() ++ (u :: b.inorder())) ++ (z :: (c.inorder())) ++ (w :: d.inorder()))

        ListSpecs.appendAssoc(a.inorder(), u :: b.inorder(), z :: c.inorder())
        ListSpecs.appendAssoc(u :: b.inorder(), z :: c.inorder(), w :: d.inorder())
        assert(this.inorder() == res.inorder())

        res.bstTrans()
        assert(res.left.isBST())
        assert(res.right.isBST())
        assert(res.left.isAVL())
        assert(res.right.isAVL())
        assert(res.balanceFactor <= 2 && res.balanceFactor >= -2) // remainder
        assert(res.isAlmostAVL())

        res
    }.ensuring(res => res.isAVL() && res.inorder() == this.inorder())

    override def isAVL(): Boolean = {
        this.isAlmostAVL() && this.balanceFactor < 2 && this.balanceFactor > -2
    }

    override def isAlmostAVL(): Boolean = {
        this.isBST() && this.balanceFactor <= 2 && this.balanceFactor >= -2 && this.left.isAVL() && this.right.isAVL()
    }
    override def isBST(): Boolean = {
        StrictlyOrderedList.isInorder(this.inorder())
    }

    override def inorder(): List[BigInt] = {
        this.left.inorder() ++ (this.v :: this.right.inorder())
    }.ensuring(res => res.content == this.content)

    def bstTrans(): Boolean = {
        require(this.isBST())
        this.left.isBST() && this.right.isBST()
    }.holds because {
        StrictlyOrderedList.inorderSpread(this.left.inorder(), this.v, this.right.inorder())
    }
}


def appendAssocFour(@induct as: List[BigInt], bs: List[BigInt], cs: List[BigInt], ds: List[BigInt]): Boolean = {
    val x = as ++ (bs ++ (cs ++ ds))
    val y = as ++ ((bs ++ cs) ++ ds)
    val z = (as ++ bs) ++ (cs ++ ds)
    val w = (as ++ (bs ++ cs)) ++ ds
    x == y && x == z && x == w && y == z && y == w && z == w
}.holds because {
    ListSpecs.appendAssoc(as, bs, cs) && ListSpecs.appendAssoc (as, bs, ds) && ListSpecs.appendAssoc(bs, cs, ds) && ListSpecs.appendAssoc(as, cs, ds)
}

def prependOneSorted(x: BigInt, @induct a: List[BigInt]): Boolean = {
    require(StrictlyOrderedList.isInorder(a) && (a.isEmpty || a.head > x))
    StrictlyOrderedList.isInorder(x :: a)
}.holds


object StrictlyOrderedList {
    // Some helpers
    def concatLast(@induct left: List[BigInt], right: List[BigInt]): Boolean = {
        right.nonEmpty ==> ((left ++ right).last == right.last)
    }.holds

    def addLast(left: List[BigInt], elem: BigInt): Boolean = {
        (left :+ elem) == (left ++ List(elem))
    }.holds

    def concatElem(@induct left: List[BigInt], elem: BigInt, right: List[BigInt]): Boolean = {
        (left ++ (elem :: right)) == ((left :+ elem) ++ right)
    }.holds

    // StrictlyOrderedList is a strictly sorted List
    def isInorder(l: List[BigInt]): Boolean = l match {
        case Cons(h1, Cons(h2, _)) if(h1 >= h2) => false
        case Cons(_, t) => isInorder(t)
        case _ => true
    }

    // Validity spreads to sub-parts
    def inorderSpread(@induct xs: List[BigInt], y: BigInt): Boolean = (
        isInorder(xs :+ y) == (
            isInorder(xs) &&
            (xs.isEmpty || xs.last < y)
        )
    ).holds

    def inorderSpread(@induct xs: List[BigInt], ys: List[BigInt]): Boolean = (
        isInorder(xs ++ ys) == (
            isInorder(xs) &&
            isInorder(ys) &&
            (xs.isEmpty || ys.isEmpty || xs.last < ys.head)
        )
    ).holds

    def inorderSpread(@induct xs: List[BigInt], y: BigInt, ys: List[BigInt]): Boolean = (
        isInorder(xs ++ (y :: ys)) == (
            isInorder(xs :+ y) &&
            isInorder(y :: ys)
        ) && inorderSpread(xs, y :: ys)
    ).holds

    def inorderSpread(x: BigInt, @induct xs: List[BigInt], y: BigInt, ys: List[BigInt]): Boolean = (
        isInorder((x :: xs) ++ (y :: ys)) == (
            x < y &&
            isInorder(x :: xs) &&
            isInorder(xs :+ y) &&
            isInorder(y :: ys)
        ) && inorderSpread(x :: xs, y, ys)
    ).holds

    // Inequalities and contains
    def bigger(@induct xs: List[BigInt], y: BigInt, e: BigInt): Boolean = {
        require(isInorder(xs :+ y) && y <= e)
        xs.forall(_ < e) && !xs.contains(e)
    }.holds

    def bigger(xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
        require(isInorder(xs ++ (y :: ys)) && y <= e)
        inorderSpread(xs, y, ys)
        bigger(xs, y, e)
        xs.forall(_ < e) && !xs.contains(e)
    }.holds

    def smaller(y: BigInt, @induct ys: List[BigInt], e: BigInt): Boolean = {
        require(isInorder(y :: ys) && e <= y)
        ys.forall(e < _) && !ys.contains(e)
    }.holds

    def smaller(xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
        require(isInorder(xs ++ (y :: ys)) && e <= y)
        inorderSpread(xs, y, ys)
        smaller(y, ys, e)
        ys.forall(e < _) && !ys.contains(e)
    }.holds

    def contains(xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
        require(isInorder(xs ++ (y :: ys)))
        val l = xs ++ (y :: ys)

        if(e < y) {
            smaller(xs, y, ys, e) && (l.contains(e) == xs.contains(e))
        } else {
            bigger(xs, y, ys, e) && (l.contains(e) == (y :: ys).contains(e))
        }
    }

    // Insert
    def inorderInsert(l: List[BigInt], e: BigInt): List[BigInt] = {
        require(isInorder(l))
        decreases(l.length)
        l match {
            case Nil() => Cons(e, Nil())
            case Cons(h, t) if(h == e) => l
            case Cons(h, t) if(e < h) => Cons(e, l)
            case Cons(h, t) => Cons(h, inorderInsert(t, e))
        }
    }.ensuring(res =>
        isInorder(res) &&
        (res.content == (l.content + e))
    )

    def insertLemma(@induct xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
        require(isInorder(xs ++ (y :: ys)))
        inorderInsert(xs ++ (y :: ys), e) == (
            if(e < y)
                inorderInsert(xs, e) ++ (y :: ys)
            else
                xs ++ inorderInsert(y :: ys, e)
        )
    }.holds

    def insertSmallerLemma(@induct xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
        require(isInorder(xs ++ (y :: ys)) && e < y)
        inorderInsert(xs ++ (y :: ys), e) == (inorderInsert(xs, e) ++ (y :: ys))
    }.holds

    def insertEqualLemma(xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
        require(isInorder(xs ++ (y :: ys)) && y == e)
        check(insertBiggerLemma(xs, y, ys, e))
        inorderInsert(xs ++ (y :: ys), e) == (xs ++ (y :: ys))
    }.holds

    def insertBiggerLemma(@induct xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
        require(isInorder(xs ++ (y :: ys)) && y <= e)
        inorderInsert(xs ++ (y :: ys), e) == (xs ++ inorderInsert(y :: ys, e))
    }.holds

    // Delete
    def deleteFirst(@induct l: List[BigInt], e: BigInt): List[BigInt] = {
        require(isInorder(l))
        l match {
            case Cons(h, t) if(h == e) => t
            case Cons(h, t) => Cons(h, deleteFirst(t, e))
            case _ => l
        }
    }.ensuring(res =>
        isInorder(res) &&
        (if(l.contains(e)) res.size == l.size - 1 else res == l)
    )

    def deleteFirstLemma(@induct xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
        require(isInorder(xs ++ (y :: ys)))
        deleteFirst(xs ++ (y :: ys), e) == {
            contains(xs, y, ys, e)
            if(e < y) {
                deleteFirst(xs, e) ++ (y :: ys)
            } else {
                xs ++ deleteFirst(y :: ys, e)
            }
        }
    }.holds

    def deleteSmallerLemma(@induct xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
        require(isInorder(xs ++ (y :: ys)) && e < y)
        check(smaller(y, ys, e))
        deleteFirst(xs ++ (y :: ys), e) == (deleteFirst(xs, e) ++ (y :: ys))
    }.holds

    def deleteEqualLemma(xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
        require(isInorder(xs ++ (y :: ys)) && y == e)
        check(deleteBiggerLemma(xs, y, ys, e))
        deleteFirst(xs ++ (y :: ys), e) == (xs ++ ys)
    }.holds

    def deleteBiggerLemma(@induct xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
        require(isInorder(xs ++ (y :: ys)) && y <= e)
        check(bigger(xs, y, e))
        deleteFirst(xs ++ (y :: ys), e) == (xs ++ deleteFirst(y :: ys, e))
    }.holds
}