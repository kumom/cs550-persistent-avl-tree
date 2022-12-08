import java.rmi.UnexpectedException
abstract class AVLTree {
    def balanceFactor: BigInt
    def height: BigInt

    def insert(v: BigInt): AVLTree

    def has(v: BigInt): Boolean

    def delete(v: BigInt): AVLTree

    def balanced(): AVLTree
}

case object Empty extends AVLTree {
    override def balanceFactor: BigInt = 0
    override def height: BigInt = -1

    override def insert(v: BigInt): AVLTree = Branch(v, Empty, Empty)

    override def delete(v: BigInt): AVLTree = this

    override def has(v: BigInt): Boolean = false

    override def balanced(): AVLTree = this
}

case class Branch(v: BigInt, left: AVLTree, right: AVLTree) extends AVLTree {
    override def balanceFactor: BigInt = right.height - left.height
    override def height: BigInt = left.height.max(right.height) + 1

    override def has(v: BigInt): Boolean = {
        if this.v == v then
            true 
        else if v < this.v then
            left.has(v)
        else
            right.has(v)
    }

    override def insert(v: BigInt): AVLTree = {
        if this.v == v then
            this
        else if v < this.v then
            Branch(this.v, this.left.insert(v), this.right).balanced()
        else
            Branch(this.v, this.left, this.right.insert(v)).balanced()
    }

    def delete(v: BigInt): AVLTree = {
        if this.v == v then {
            // move left child into root (if nonempty)
            if this.left == Empty then
                this.right
            else {
                ???
            }
        } else if v < this.v then
            Branch(this.v, this.left.delete(v), this.right).balanced()
        else 
            Branch(this.v, this.left, this.right.delete(v)).balanced()
    }

    override def balanced(): AVLTree = {
        if this.balanceFactor == 2 then {
            if this.right.balanceFactor == 1 then
                this.rotateLeft()
            else
                this.rotateRightLeft()
        } else if this.balanceFactor == -2 then {
            if this.left.balanceFactor == -1 then
                this.rotateRight()
            else
                this.rotateLeftRight()
        } else
            this
    }

    // this is +2, right child is +1
    def rotateLeft(): AVLTree = {
        val Branch(w, a, rChild) = this
        val Branch(u, b, c) = rChild match {
            case b: Branch => b
            case Empty => throw UnexpectedException("invalid rotateLeft call")
        }
        Branch(u, Branch(w, a, b), c)
    }

    // this is on +2, right child is on -1
    def rotateRightLeft(): AVLTree = {
        val Branch(w, a, rChild) = this
        val Branch(u, lGrandchild, d) = rChild match {
            case b: Branch => b
            case Empty => throw UnexpectedException("invalid rotateRightLeft call")
        }
        val Branch(z, b, c) = lGrandchild match {
            case b: Branch => b
            case Empty => throw UnexpectedException("invalid rotateRightLeft call")
        }
        Branch(z, Branch(w, a, b), Branch(u, c, d))
    }

    def rotateRight(): AVLTree = {
        val Branch(w, lChild, c) = this
        val Branch(u, a, b) = lChild match {
            case b: Branch => b
            case Empty => throw UnexpectedException("invalid rotateLeft call")
        }
        Branch(u, a, Branch(w, b, c))
    }

    def rotateLeftRight(): AVLTree = {
        val Branch(w, lChild, d) = this
        val Branch(u, a, rGrandchild) = lChild match {
            case b: Branch => b
            case Empty => throw UnexpectedException("invalid rotateRightLeft call")
        }
        val Branch(z, b, c) = rGrandchild match {
            case b: Branch => b
            case Empty => throw UnexpectedException("invalid rotateRightLeft call")
        }
        Branch(z, Branch(u, a, b), Branch(w, c, d))
    }
}