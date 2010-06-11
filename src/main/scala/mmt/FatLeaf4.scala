package mmt

import annotation.tailrec

// FatLeaf4

object FatLeaf4 {

  def LeafMin = 8
  def LeafMax = 2 * LeafMin 

  abstract class Node[A,B](var parent: Branch[A,B])

  class Branch[@specialized A,B](par0: Branch[A,B],
                                 var height: Int,
                                 var key: A,
                                 var value: B,
                                 var left: Node[A,B],
                                 var right: Node[A,B]) extends Node[A,B](par0) {
    def this(right0: Node[A,B]) = this(null, -1, null.asInstanceOf[A], null.asInstanceOf[B], null, right0)
  }

  class Leaf[@specialized A,B](par0: Branch[A,B],
                               var size: Int,
                               var keys: Array[A],
                               var values: Array[B]) extends Node[A,B](par0) {
    def this(par0: Branch[A,B], size0: Int)(implicit am: ClassManifest[A], bm: ClassManifest[B]) =
        this(par0, size0, new Array[A](LeafMax), new Array[B](LeafMax))
  }

  def newEmptyRootHolder[@specialized A,B](implicit am: ClassManifest[A], bm: ClassManifest[B]) = {
    val h = new Branch[A,B](null)
    h.right = new Leaf[A,B](h, 0)
    h
  }

  class MutableTree[@specialized A,B](rootHolder: Branch[A,B], var _size: Int)(
          implicit cmp: Ordering[A], am: ClassManifest[A], bm: ClassManifest[B]) {

    def this()(implicit cmp: Ordering[A], am: ClassManifest[A], bm: ClassManifest[B]) =
        this(newEmptyRootHolder[A,B], 0)

    //////// bulk

    def isEmpty = _size == 0
    def size = _size

    override def clone() = {
      markShared(rootHolder.right)
      new MutableTree(new Branch[A,B](rootHolder.right), _size)
    }

    //////// reads

    def contains(k: A): Boolean = contains(rootHolder.right, k)

    @tailrec final def contains(n: Node[A,B], k: A): Boolean = n match {
      case b: Branch[A,B] => {
        val c = cmp.compare(k, b.key)
        c >= 0 || contains(if (c < 0) b.left else b.right, k)
      }
      case t: Leaf[A,B] => keySearch(t, k) >= 0
    }

    def get(k: A): Option[B] = get(rootHolder.right, k)

    @tailrec final def get(n: Node[A,B], k: A): Option[B] = n match {
      case b: Branch[A,B] => {
        val c = cmp.compare(k, b.key)
        if (c == 0) Some(b.value) else get(if (c < 0) b.left else b.right, k)
      }
      case t: Leaf[A,B] => {
        val i = keySearch(t, k)
        if (i >= 0) Some(t.values(i)) else None
      }
    }

    def keySearch(t: Leaf[A,B], k: A): Int = {
      var b = 0
      var e = t.size
      while (b < e) {
        val mid = (b + e) >>> 1
        val c = cmp.compare(k, t.keys(mid))
        if (c < 0) {
          e = mid
        } else if (c > 0) {
          b = mid + 1
        } else {
          return mid
        }
      }
      return ~b
    }

    //////// put

    def put(k: A, v: B): Option[B] = put(unsharedRight(rootHolder), k, v)

    @tailrec final def put(n: Node[A,B], k: A, v: B): Option[B] = n match {
      case b: Branch[A,B] => {
        val c = cmp.compare(k, b.key)
        if (c == 0) {
          // update
          val z = b.value
          b.value = v
          Some(z)
        } else {
          put(if (c < 0) unsharedLeft(b) else unsharedRight(b), k, v)
        }
      }
      case t: Leaf[A,B] => {
        val i = keySearch(t, k)
        if (i >= 0) {
          val z = t.values(i)
          t.values(i) = v
          Some(z)
        } else {
          insert(t, ~i, k, v)
          _size += 1
          None
        }
      }
    }

    def insert(t: Leaf[A,B], i: Int, k: A, v: B) {
      // make space
      val num = t.size
      System.arraycopy(t.keys, i, t.keys, i + 1, num - i)
      System.arraycopy(t.values, i, t.values, i + 1, num - i)
      t.size = num + 1

      // copy the values
      t.keys(i) = k
      t.values(i) = v

      // split if necessary
      if (num + 1 == LeafMax) split(t)
    }

    def split(tL: Leaf[A,B]) {
      val leftSize = LeafMax / 2
      val rightSize = LeafMax - 1 - leftSize

      // existing terminal becomes left leaf, create new branch
      val b = new Branch[A,B](tL.parent, 2, tL.keys(leftSize), tL.values(leftSize), tL, null)
      val tR = new Leaf[A,B](b, rightSize)
      b.right = tR

      // copy to right
      System.arraycopy(tL.keys, leftSize + 1, tR.keys, 0, rightSize)
      System.arraycopy(tL.values, leftSize + 1, tR.values, 0, rightSize)

      // fix up left
      tL.parent = b
      tL.size = leftSize
      clear(tL, leftSize, 1 + rightSize)

      // link into parent
      if (b.parent.left eq tL) b.parent.left = b else b.parent.right = b
      repair(b.parent)
    }

    def clear(t: Leaf[A,B], pos: Int, len: Int) {
      clear(t.keys, pos, len)
      clear(t.values, pos, len)
    }

    def clear[@specialized C](a: Array[C], pos: Int, len: Int) {
      var i = pos
      while (i < pos + len) { a(i) = null.asInstanceOf[C] ; i += 1 }
    }

    //////// remove

    def remove(k: A): Option[B] = remove(unsharedRight(rootHolder), k)

    @tailrec final def remove(n: Node[A,B], k: A): Option[B] = n match {
      case b: Branch[A,B] => {
        val c = cmp.compare(k, b.key)
        if (c == 0) {
          val z = b.value
          removeMax(b, unsharedLeft(b))
          _size -= 1
          Some(z)
        } else {
          remove(if (c < 0) unsharedLeft(b) else unsharedRight(b), k)
        }
      }
      case t: Leaf[A,B] => {
        val i = keySearch(t, k)
        if (i >= 0) {
          val z = t.values(i)
          removeFromLeaf(t, i)
          _size -= 1
          Some(z)
        } else {
          None
        }
      }
    }

    @tailrec final def removeMax(target: Branch[A,B], n: Node[A,B]): Unit = n match {
      case b: Branch[A,B] => {
        removeMax(target, unsharedRight(b))
      }
      case t: Leaf[A,B] => {
        // steal one
        val i = t.size - 1
        target.key = t.keys(i)
        target.value = t.values(i)
        removeMaxFromLeaf(t)
      }
    }

    def removeMaxFromLeaf(t: Leaf[A,B]) {
      val num = t.size - 1
      t.size = num
      clear(t, num, 1)
      if (num < LeafMin) refill(t)
    }

    def removeFromLeaf(t: Leaf[A,B], i: Int) {
      // slide down
      val num = t.size - 1
      System.arraycopy(t.keys, i + 1, t.keys, i, num - i)
      System.arraycopy(t.values, i + 1, t.values, i, num - i)
      t.size = num

      clear(t, num, 1)

      // join or steal if necessary
      if (num < LeafMin) refill(t)
    }

    def refill(t: Leaf[A,B]): Unit = t.parent.height match {
      case -1 => {} // root holder has height -1, root can't be refilled
      case 2 => {
        if (t.parent.left eq t)
          refillAsLeft(t)
        else
          refillAsRight(t)
      }
      case 3 => {
        // refill is easier if our sibling is a leaf
        if (t.parent.left eq t) {
          rotateLeft(t.parent)
          refillAsLeft(t)
        } else {
          rotateRight(t.parent)
          refillAsRight(t)
        }
      }
    }

    def refillAsLeft(tL: Leaf[A,B]) {
      val b = tL.parent
      val tR = unsharedRight(b).asInstanceOf[Leaf[A,B]]
      if (tR.size == LeafMin)
        merge(b, tL, tR)
      else {
        tL.keys(LeafMin - 1) = b.key
        tL.values(LeafMin - 1) = b.value
        tL.size = LeafMin
        b.key = tR.keys(0)
        b.value = tR.values(0)
        removeFromLeaf(tR, 0)
      }
    }
  
    def refillAsRight(tR: Leaf[A,B]) {
      val b = tR.parent
      val tL = unsharedLeft(b).asInstanceOf[Leaf[A,B]]
      if (tL.size == LeafMin)
        merge(b, tL, tR)
      else {
        insert(tR, 0, b.key, b.value)
        b.key = tL.keys(tL.size - 1)
        b.value = tL.values(tL.size - 1)
        removeMaxFromLeaf(tL)
      }
    }

    def merge(b: Branch[A,B], tL: Leaf[A,B], tR: Leaf[A,B]) {
      assert(1 + tL.size + tR.size == LeafMax)
      val leftSize = tL.size
      tL.keys(leftSize) = b.key
      tL.values(leftSize) = b.value
      System.arraycopy(tR.keys, 0, tL.keys, leftSize + 1, LeafMax - (leftSize + 1))
      tL.size = LeafMax
      tL.parent = b.parent

      if (b.parent.left eq b) b.parent.left = tL else b.parent.right = tL
      repair(b.parent)
    }

    //////// sharing machinery

    def unsharedLeft(b: Branch[A,B]): Node[A,B] = {
      if (b.left.parent == null)
        b.left = unshare(b.left, b)
      b.left
    }

    def unsharedRight(b: Branch[A,B]): Node[A,B] = {
      if (b.right.parent == null)
        b.right = unshare(b.right, b)
      b.right
    }

    def unshare(n: Node[A,B], p: Branch[A,B]): Node[A,B] = n match {
      case b: Branch[A,B] => {
        markShared(b.left)
        markShared(b.right)
        new Branch[A,B](p, b.height, b.key, b.value, b.left, b.right)
      }
      case t: Leaf[A,B] => {
        new Leaf[A,B](p, t.size, t.keys.clone(), t.values.clone())
      }
    }

    def markShared(n: Node[A,B]) { n.parent = null }


    //////// AVL rebalancing

    def height(n: Node[A,B]) = n match {
      case b: Branch[A,B] => b.height
      case _ => 1
    }

    def balance(n: Node[A,B]) = n match {
      case b: Branch[A,B] => height(b.left) - height(b.right)
      case _ => 0
    }
    
    def repair(b: Branch[A,B]) {
      val h0 = b.height

      // rootHolder
      if (h0 < 0) return

      val hL = height(b.left)
      val hR = height(b.right)
      val bal = hL - hR
      if (bal > 1) {
        // Left is too large, rotate right.  If left.right is larger than
        // left.left then rotating right will lead to a -2 balance, so
        // first we have to rotateLeft on left.
        replaceInParent(b, h0, if (balance(b.left) < 0) rotateRightOverLeft(b) else rotateRight(b))
      } else if (bal < -1) {
        replaceInParent(b, h0, if (balance(b.right) > 0) rotateLeftOverRight(b) else rotateLeft(b))
      } else {
        // no rotations needed, just update height
        val h = 1 + math.max(hL, hR)
        if (h != h0) {
          b.height = h
          repair(b.parent)
        }
      }
    }

    def replaceInParent(n0: Node[A,B], h0: Int, n: Branch[A,B]) {
      if (n.parent.right eq n0) n.parent.right = n else n.parent.left = n

      if (n.height != h0) repair(n.parent)
    }

    def rotateRight(b: Branch[A,B]): Branch[A,B] = {
      val nL = unsharedLeft(b).asInstanceOf[Branch[A,B]]
      nL.parent = b.parent

      b.left = nL.right
      if (b.left.parent != null)
        b.left.parent = b

      nL.right = b
      b.parent = nL

      b.height = 1 + math.max(height(b.left), height(b.right))
      nL.height = 1 + math.max(height(nL.left), b.height)

      nL
    }

    def rotateRightOverLeft(b: Branch[A,B]): Branch[A,B] = {
      b.left = rotateLeft(unsharedLeft(b).asInstanceOf[Branch[A,B]])
      rotateRight(b)
    }

    def rotateLeft(b: Branch[A,B]): Branch[A,B] = {
      val nR = unsharedRight(b).asInstanceOf[Branch[A,B]]
      nR.parent = b.parent

      b.right = nR.left
      if (b.right.parent != null)
        b.right.parent = b

      nR.left = b
      b.parent = nR

      b.height = 1 + math.max(height(b.right), height(b.left))
      nR.height = 1 + math.max(height(nR.right), b.height)

      nR
    }

    def rotateLeftOverRight(b: Branch[A,B]): Branch[A,B] = {
      b.right = rotateRight(unsharedRight(b).asInstanceOf[Branch[A,B]])
      rotateLeft(b)
    }
  }
}