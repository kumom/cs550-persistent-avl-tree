sealed abstract class AVLTree {
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

    def isAVL(): Boolean
    def isAlmostAVL(): Boolean
    
    def isBST(): Boolean
}

case object Empty extends AVLTree {
    override def balanceFactor: BigInt = 0
    override def height: BigInt = -1

    override def insert(v: BigInt): AVLTree = Branch(v, Empty, Empty)

    override def delete(v: BigInt): AVLTree = this

    override def has(v: BigInt): Boolean = false

    override def balanced(): AVLTree = this

    override def isAlmostAVL(): Boolean = true

    override def isAVL(): Boolean = true

    override def isBST(): Boolean = true
}

def maxBigInt(a: BigInt, b: BigInt): BigInt = {
    if a > b then a else b
}

case class Branch(v: BigInt, left: AVLTree, right: AVLTree) extends AVLTree {
    override def balanceFactor: BigInt = right.height - left.height
    override def height: BigInt = maxBigInt(left.height, right.height) + 1

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
        else if v < this.v then
            val lefter = this.left.insert(v)
            // assert(lefter.height <= this.left.height + 1)
            // assert(this.left.height <= )
            val res = Branch(this.v, lefter, this.right)
            // assert(res.isBST())
            assert(lefter.height <= this.left.height + 1)
            assert(res.right.height - res.left.height >= -2)

            assert(res.right.height == this.right.height)
            assert(res.left.height >= this.left.height - 1)
            // right is the same, left might have increased by one
            assert(res.right.height - res.left.height <= 2)

            assert(res.balanceFactor >= -2 && res.balanceFactor <= 2)
            assert(res.off())
            assert(res.isAlmostAVL())
            res.balanced()
        else
            Branch(this.v, this.left, this.right.insert(v)).balanced()
    }.ensuring(res => res.isAVL() && res.height <= this.height + 1 && res.height >= this.height - 1)

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
    }.ensuring(res => res.isAVL())

    def max(): BigInt = {
        this.right match {
            case Empty => v
            case b: Branch => b.max()
        }
    }
    override def balanced(): AVLTree = {
        require(this.isAlmostAVL())
        // require((!(this.balanceFactor == 2) || (this.right.balanceFactor == 1 || this.right.balanceFactor == -1))&& (!(this.balanceFactor == -2) || (this.left.balanceFactor == 1 || this.left.balanceFactor == -1)))
        if this.balanceFactor == 2 then {
            assert(this.right.balanceFactor == 1 || this.right.balanceFactor == -1)
            if this.right.balanceFactor == -1 then
                this.rotateRightLeft()
            else
                this.rotateLeft()
        } else if this.balanceFactor == -2 then {
            if this.left.balanceFactor == 1 then
                this.rotateLeftRight()
            else
                this.rotateRight()
        } else
            this
    }.ensuring(res => res.isAVL())

    // this is +2, right child is +1
    def rotateLeft(): AVLTree = {
        require(this.isAlmostAVL() && this.balanceFactor == 2 && this.right.balanceFactor == 1)
        val Branch(w, a, rChild) = this
        val Branch(u, b, c) = rChild.asInstanceOf[Branch]
        Branch(u, Branch(w, a, b), c)
    }.ensuring(res => res.isAVL())

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

    override def isAVL(): Boolean = this.isAlmostAVL() && this.balanceFactor < 2 && this.balanceFactor > -2

    private def proof(): Unit = {
        require(this.isAlmostAVL() && this.balanceFactor == 2)
        assert(this.off())
    }.ensuring(_ => this.right.balanceFactor == 1 || this.right.balanceFactor == -1)

    private def off(): Boolean = {
        if this.balanceFactor == 2 then
            this.right match
                case Empty => false
                case z => z.balanceFactor == 1 || z.balanceFactor == -1
        else if this.balanceFactor == -2 then
            this.left match
                case Empty => false
                case z => z.balanceFactor == 1 || z.balanceFactor == -1
        else
            true
    }
    override def isAlmostAVL(): Boolean = {
        off() &&  this.balanceFactor <= 2 && this.balanceFactor >= -2 && this.left.isAVL() && this.right.isAVL()
    }
    override def isBST(): Boolean = {
        if !this.left.isBST() || !this.right.isBST() then
            false 
        else if this.left == Empty && this.right == Empty then
            true
        else if this.left == Empty && this.right != Empty then {
            val Branch(v2, _, _) = this.right: @unchecked
            v < v2
        }
        else if this.left != Empty && this.right == Empty then {
            val Branch(v2, _, _) = this.left: @unchecked
            v > v2
        }
        else {
            val Branch(v1, _, _) = this.left: @unchecked
            val Branch(v2, _, _) = this.right: @unchecked
            v1 < v && v < v2
        }
    }
    
}