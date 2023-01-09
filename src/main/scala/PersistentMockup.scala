import stainless.collection._
import stainless.proof._
import stainless.lang._
import stainless.annotation._

import AVLTree._
import PersistentAVLTreeSpecs._

object PersistentAVLTree {
    final case class PersistentTree (var roots: List[Tree], var time: BigInt) {
        def valid : Boolean = time == roots.length - 1 && time >= 0 && roots(0) == Empty && roots.forall(isAVL(_))
        
        def root : Tree = {
            require(valid)
            roots(time)
        }.ensuring(isAVL(_))

        def insert(x: BigInt) : Unit = {
            require(valid)
            val newRoot = root.insert(x)
            roots = roots ++ List(newRoot)
            time = time + 1
        }.ensuring(_ => roots.length == old(this).roots.length + 1 && time == old(this).time + 1 && valid)

        def remove(x: BigInt) : Unit = {
            require(valid)
            val newRoot = root.remove(x)
            roots = roots ++ List(newRoot)
            time = time + 1
        }.ensuring(_ => roots.length == old(this).roots.length + 1 && time == old(this).time + 1 && valid)

        def contains(x: BigInt, t: BigInt) : Boolean = {
            require(t >= 0)
            require(valid)
            if t <= time then
                val r = roots(t)
                r.contains(x)
            else
                root.contains(x)
        }.ensuring(res => old(this).roots == roots && (t <= time ==> res == roots(t).contains(x)) && (t > time ==> res == root.contains(x)))
    }
}