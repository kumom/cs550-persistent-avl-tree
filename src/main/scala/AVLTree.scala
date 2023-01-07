import stainless.collection._
import stainless.proof._
import stainless.lang._
import stainless.annotation._

import AVLTree._

object AVLTreeSpecs {
        def isBalanced(t: Tree) : Boolean = {
            t match {
                case Empty => true
                case n: Node =>
                    -1 <= n.balanceFactor && n.balanceFactor <= 1 &&
                    isBalanced(n.l) && isBalanced(n.r)
            }
        }

        def isValidUnbalanced(t: Tree) : Boolean = {
            t match {
                case Empty => true
                case n: Node =>
                    -2 <= n.balanceFactor && n.balanceFactor <= 2 &&
                    isBalanced(n.l) && isBalanced(n.r)
            }
        }

        def isBST(t: Tree) : Boolean = StrictlyOrderedList.isInorder(t.toList)

        def isAVL(t: Tree) : Boolean = isBalanced(t) && isBST(t)

        def contains(t:Tree, x: BigInt) : Boolean = {
            require(isBST(t))
            assert(t.subTreesAreBST)

            t match {
                case Empty => false
                case Node(l, v, r) => { 
                    assert(StrictlyOrderedList.contains(l.toList, v, r.toList, x))
                    if x == v then 
                        true
                    else if x > v then 
                        contains(r, x)
                    else 
                        contains(l, x)
                }
            }
        }.ensuring(old(t).content == t.content && isBST(t) && _ == t.toList.contains(x))
}

object AVLTree {
    sealed abstract class Tree {
        lazy val size : BigInt = (this match {
            case Empty => BigInt(0)
            case Node(l, v, r) => l.size + BigInt(1) + r.size
        }).ensuring(_ == toList.length)

        lazy val height : BigInt = (this match {
            case Empty => BigInt(0)
            case Node(l, v, r) => 
                val lh = l.height
                val rh = r.height
                val h = BigInt(1) + (if lh > rh then lh else rh)
                assert(h == lh + 1 || h == rh + 1)
                h
        }).ensuring(_ >= 0)

        def content: Set[BigInt] = this match {
            case Empty => Set.empty
            case Node(l, v, r) => l.content ++ Set(v) ++ r.content
        }

        // inorder traversel of the tree
        def toList: List[BigInt] = (this match {
            case Empty => List.empty[BigInt]
            case Node(l, v, r) => l.toList ++ (v :: r.toList)
        }).ensuring(_.content == content)

        def balanceFactor: BigInt = (this match {
            case Empty => 0
            case Node(l, v, r) => r.height - l.height
        })

        def isRightHeavy : Boolean = balanceFactor >= 1
        def isLeftHeavy : Boolean = -1 >= balanceFactor

        def insert(x: BigInt) : Node = {
            require(AVLTreeSpecs.isAVL(this))
            assert(subTreesAreAVL)

            this match {
                case Empty => 
                    balance(Node(Empty, x, Empty)).asInstanceOf[Node]
                case Node(l, v, r) => 
                    assert(StrictlyOrderedList.insertLemma(l.toList, v, r.toList, x))
                    if v == x then 
                        this.asInstanceOf[Node]
                    else if v < x then
                        balance(Node(l, v, balance(r.insert(x)))).asInstanceOf[Node]
                    else
                        balance(Node(balance(l.insert(x)), v, r)).asInstanceOf[Node]
            }
        }.ensuring(res => res.toList == StrictlyOrderedList.inorderInsert(toList, x) && 
                        (res.height == height || res.height == height + 1) && 
                        AVLTreeSpecs.contains(res, x) && 
                        AVLTreeSpecs.isAVL(res))

        def remove(x: BigInt) : Tree = {
            require(AVLTreeSpecs.isAVL(this))
            assert(subTreesAreAVL)
            
            this match {
                case Empty => 
                    Empty
                case Node(l, v, r) => 
                    assert(StrictlyOrderedList.deleteFirstLemma(l.toList, v, r.toList, x))
                    if x > v then
                        balance(Node(l, v, balance(r.remove(x))))
                    else if x < v then
                        balance(Node(balance(l.remove(x)), v, r))
                    else 
                        if r == Empty then
                            balance(l)
                        else
                            val (min, rr) = (r.asInstanceOf[Node]).removeMin()
                            balance(Node(l, min, rr))
            }
        }.ensuring(res => res.toList == StrictlyOrderedList.deleteFirst(toList, x) &&
                        (res.height == height || res.height == height - 1) && 
                        !AVLTreeSpecs.contains(res, x) &&
                        AVLTreeSpecs.isAVL(res))

        // Lemmas
        def subTreesAreBST : Boolean = {
            require(AVLTreeSpecs.isBST(this))

            this match {
                case Empty => true
                case Node(l, v, r) => 
                    StrictlyOrderedList.inorderSpread(l.toList, r.toList) &&
                    StrictlyOrderedList.inorderSpread(l.toList, v, r.toList) &&
                    StrictlyOrderedList.isInorder(l.toList :+ v) &&
                    StrictlyOrderedList.isInorder(v :: r.toList) &&
                    AVLTreeSpecs.isBST(r) && AVLTreeSpecs.isBST(l) &&
                    r.subTreesAreBST && l.subTreesAreBST
            }
        }.holds

        def subTreesAreAVL : Boolean = {
            require(AVLTreeSpecs.isAVL(this))

            this match {
                case Empty => true
                case Node(l, v, r) => 
                    subTreesAreBST &&
                    AVLTreeSpecs.isAVL(r) && AVLTreeSpecs.isAVL(l) &&
                    r.subTreesAreAVL && l.subTreesAreAVL
            }
        }.holds
    }

    case object Empty extends Tree 

    case class Node (l: Tree, v: BigInt, r: Tree) extends Tree {
        def removeMin() : (BigInt, Tree) = {
            require(AVLTreeSpecs.isAVL(this))
            assert(subTreesAreAVL)

            l match {
                case Empty => 
                    (v, r)
                case l: Node => 
                    val (min, ll) = l.removeMin()
                    (min, balance(Node(ll, v, r)))
            }

        }.ensuring(res => 
                   res._1 == toList.head &&
                   res._2.toList == toList.tail &&
                   StrictlyOrderedList.isInorder(res._1 :: res._2.toList) &&
                   (res._2.height == height || res._2.height == height - 1) && 
                   AVLTreeSpecs.isAVL(res._2))
    }

    private def concatAssoc(@induct l1: List[BigInt], l2: List[BigInt], l3: List[BigInt]) : Boolean = {
        (l1 ++ l2) ++ l3 == l1 ++ (l2 ++ l3)
    }.holds

    private def rotateLeft(n: Node) : Node = {
        require(n.isRightHeavy)

        n match {
            case Node(l, v, r) => {
                r match {
                    case Node(ll, vv, rr) => 
                        assert(concatAssoc(l.toList, v :: ll.toList, vv :: rr.toList))
                        val res = Node(Node(l, v, ll), vv, rr)

                        // the assertions below can be commented out
                        if n.balanceFactor == -2 then
                            if r.balanceFactor == 0 then
                                assert(res.balanceFactor == 1)
                            else if r.balanceFactor == -1 then
                                assert(res.balanceFactor == 0)
                            else if r.balanceFactor == 1 then
                                assert(res.balanceFactor == 2)

                        if n.balanceFactor == 1 then
                            if r.balanceFactor == 0 then
                                assert(res.balanceFactor == -1)

                        res
                }
            }
        }
    }.ensuring(res => n.toList == res.toList && 
                    (res.height == n.height || res.height == n.height - 1))

    private def rotateRight(n: Node) : Node = {
        require(n.isLeftHeavy)

        n match {
            case Node(l, v, r) => {
                l match {
                    case Node(ll, vv, rr) =>  
                        assert(concatAssoc(ll.toList, vv :: rr.toList, v :: r.toList))
                        val res = Node(ll, vv, Node(rr, v, r))

                        // the assertions below can be commented out
                        if n.balanceFactor == -2 then
                            if l.balanceFactor == 0 then
                                assert(res.balanceFactor == 1)
                            else if l.balanceFactor == -1 then
                                assert(res.balanceFactor == 0)
                            else if l.balanceFactor == 1 then
                                assert(res.balanceFactor == 2)

                        if n.balanceFactor == -1 then
                            if l.balanceFactor == 0 then
                                assert(res.balanceFactor == 1)

                        res
                }
            }
        }
    }.ensuring(res => n.toList == res.toList && 
                    (res.height == n.height || res.height == n.height - 1))

    private def balance(n: Tree) : Tree = {
        require(AVLTreeSpecs.isValidUnbalanced(n))

        n match {
            case Empty => Empty
            case n: Node =>
                if n.balanceFactor == 2 then
                    assert(n.r.height == n.l.height + 2)
                    if n.r.balanceFactor == -1 then
                        rotateLeft(Node(n.l, n.v, rotateRight(n.r.asInstanceOf[Node])))
                    else
                        assert(n.r.balanceFactor == 0 || n.r.balanceFactor == 1)
                        rotateLeft(n)
                else if n.balanceFactor == -2 then
                    assert(n.r.height + 2 == n.l.height)
                    if n.l.balanceFactor == 1 then
                        rotateRight(Node(rotateLeft(n.l.asInstanceOf[Node]), n.v, n.r))
                    else
                        assert(n.l.balanceFactor == 0 || n.l.balanceFactor == -1)
                        rotateRight(n)
                else 
                    n
        }
    }.ensuring(res => n.toList == res.toList &&
                    (res.height == n.height || res.height == n.height - 1) && 
                    AVLTreeSpecs.isBalanced(res))
}

/* Copyright 2009-2021 EPFL, Lausanne */
/* Written by Clément Burgelin */
/* https://github.com/epfl-lara/bolts/blob/master/data-structures/trees/redblack/StrictlyOrderedList.scala */

object StrictlyOrderedList {
    def isInorder(l: List[BigInt]): Boolean = l match {
        case Cons(h1, Cons(h2, _)) if(h1 >= h2) => false
        case Cons(_, t) => isInorder(t)
        case _ => true
    }

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
        isInorder(res)
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

    // // Unused helpers/lemmas below
    // def concatLast(@induct left: List[BigInt], right: List[BigInt]): Boolean = {
    //     right.nonEmpty ==> ((left ++ right).last == right.last)
    // }.holds

    // def addLast(left: List[BigInt], elem: BigInt): Boolean = {
    //     (left :+ elem) == (left ++ List(elem))
    // }.holds

    // def concatElem(@induct left: List[BigInt], elem: BigInt, right: List[BigInt]): Boolean = {
    //     (left ++ (elem :: right)) == ((left :+ elem) ++ right)
    // }.holds

    // def inorderSpread(@induct xs: List[BigInt], y: BigInt): Boolean = (
    //     isInorder(xs :+ y) == (
    //         isInorder(xs) &&
    //         (xs.isEmpty || xs.last < y)
    //     )
    // ).holds

    // def inorderSpread(x: BigInt, @induct xs: List[BigInt], y: BigInt, ys: List[BigInt]): Boolean = (
    //     isInorder((x :: xs) ++ (y :: ys)) == (
    //         x < y &&
    //         isInorder(x :: xs) &&
    //         isInorder(xs :+ y) &&
    //         isInorder(y :: ys)
    //     ) && inorderSpread(x :: xs, y, ys)
    // ).holds

    // def insertSmallerLemma(@induct xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
    //     require(isInorder(xs ++ (y :: ys)) && e < y)
    //     inorderInsert(xs ++ (y :: ys), e) == (inorderInsert(xs, e) ++ (y :: ys))
    // }.holds

    // def insertEqualLemma(xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
    //     require(isInorder(xs ++ (y :: ys)) && y == e)
    //     check(insertBiggerLemma(xs, y, ys, e))
    //     inorderInsert(xs ++ (y :: ys), e) == (xs ++ (y :: ys))
    // }.holds

    // def insertBiggerLemma(@induct xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
    //     require(isInorder(xs ++ (y :: ys)) && y <= e)
    //     inorderInsert(xs ++ (y :: ys), e) == (xs ++ inorderInsert(y :: ys, e))
    // }.holds

    // def deleteSmallerLemma(@induct xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
    //     require(isInorder(xs ++ (y :: ys)) && e < y)
    //     check(smaller(y, ys, e))
    //     deleteFirst(xs ++ (y :: ys), e) == (deleteFirst(xs, e) ++ (y :: ys))
    // }.holds

    // def deleteEqualLemma(xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
    //     require(isInorder(xs ++ (y :: ys)) && y == e)
    //     check(deleteBiggerLemma(xs, y, ys, e))
    //     deleteFirst(xs ++ (y :: ys), e) == (xs ++ ys)
    // }.holds

    // def deleteBiggerLemma(@induct xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
    //     require(isInorder(xs ++ (y :: ys)) && y <= e)
    //     check(bigger(xs, y, e))
    //     deleteFirst(xs ++ (y :: ys), e) == (xs ++ deleteFirst(y :: ys, e))
    // }.holds

    // def containsLemma(xs: List[BigInt], y: BigInt, ys: List[BigInt], e: BigInt): Boolean = {
    //     require(isInorder(xs ++ (y :: ys)))
    //     require(y != e)

    //     val l = xs ++ (y :: ys)

    //     if(e < y) {
    //         smaller(xs, y, ys, e) && (l.contains(e) == xs.contains(e))
    //     } else {
    //         bigger(xs, y, ys, e) && (l.contains(e) == (y :: ys).contains(e))
    //     }
    // }
}