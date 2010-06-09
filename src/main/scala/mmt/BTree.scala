package mmt

import annotation.tailrec

// BTree

object BTree {
  def MaxKeys = 15
  def MinKeysForPair = 13

  final class Node[A,B](val generation: Long, // TODO: replace with Int + rollover logic
                        var numKeys: Int,     // TODO: replace with Short
                        var kvShared: Boolean,
                        var keysAndValues: Array[AnyRef],
                        var children: Array[Node[A,B]]) {

    //////// access to keys and values

    def keys(i: Int) = keysAndValues(2*i).asInstanceOf[A]
    def values(i: Int) = keysAndValues(2*i+1).asInstanceOf[B]

    def setKey(i: Int, k: A) { unsharedKeysAndValues()(2*i) = k.asInstanceOf[AnyRef] }
    def setValue(i: Int, v: B) { unsharedKeysAndValues()(2*i+1) = v.asInstanceOf[AnyRef] }

    def unsharedKeysAndValues(): Array[AnyRef] = {
      if (kvShared) {
        keysAndValues = keysAndValues.clone()
        kvShared = false
      }
      keysAndValues
    }

    def keySearch(k: A)(implicit cmp: Ordering[A]): Int = keySearch(k, 0, numKeys - 1)

    /** On entry, k > key(min-1) && k < key(max+1) */
    @tailrec def keySearch(k: A, min: Int, max: Int)(implicit cmp: Ordering[A]): Int = {
      if (min > max) {
        // min == max + 1, so k > key(min-1) && k < key(min).  Insert at min
        -(min + 1)
      } else {
        val mid = (min + max) >>> 1
        val c = cmp.compare(k, keys(mid))
        if (c < 0)
          keySearch(k, min, mid - 1)
        else if (c > 0)
          keySearch(k, mid + 1, max)
        else
          mid
      }
    }

    //////// read

    @tailrec def contains(k: A)(implicit cmp: Ordering[A]): Boolean = {
      val i = keySearch(k)
      i >= 0 || (children != null && children(-(i+1)).contains(k))
    }

    @tailrec def get(k: A)(implicit cmp: Ordering[A]): Option[B] = {
      val i = keySearch(k)
      if (i >= 0)
        Some(values(i))
      else if (children == null)
        None
      else
        children(-(i+1)).get(k)
    }

    //////// sharing machinery

    def copy(gen: Long) = {
      kvShared = true
      new Node[A,B](gen, numKeys, true, keysAndValues, if (children == null) null else children.clone())      
    }

    def unsharedChild(i: Int): Node[A,B] = {
      val c = children(i)
      if (c.generation == generation) {
        c
      } else {
        val repl = c.copy(generation)
        children(i) = repl
        repl
      }      
    }

    def splitChild(i: Int) {
      val lhs = children(i)
      assert(lhs.numKeys == MaxKeys && lhs.generation == generation)

      val leftN = MaxKeys / 2
      val rightN = MaxKeys - 1 - leftN
      // the other key goes into this node

      // create the new child
      val rhs = new Node[A,B](generation, rightN, false, new Array[AnyRef](2 * MaxKeys), null)

      // fix up this node
      insertEntry(i, lhs.keys(leftN), lhs.values(leftN), rhs)

      // copy the values to the rhs and reduce the size of lhs
      System.arraycopy(lhs.keysAndValues, 2 * (leftN + 1), rhs.keysAndValues, 0, 2 * rightN)
      clear(lhs.keysAndValues, 2 * leftN, 2 * (rightN + 1))
      if (lhs.children != null) {
        rhs.children = new Array[Node[A,B]](MaxKeys + 1)
        System.arraycopy(lhs.children, leftN + 1, rhs.children, 0, rightN + 1)
        clear(lhs.children, leftN + 1, rightN + 1)
      }
    }

    def insertEntry(i: Int, k: A, v: B, ch: Node[A,B]) {
      System.arraycopy(children, i + 1, children, i + 2, numKeys - i)
      children(i + 1) = ch
      insertEntry(i, k, v)
    }

    def insertEntry(i: Int, k: A, v: B) {
      System.arraycopy(keysAndValues, 2 * i, keysAndValues, 2 * (i + 1), 2 * (numKeys - i))
      setKey(i, k)
      setValue(i, v)
      numKeys += 1
    }

    def clear[T <: AnyRef](a: Array[T], pos: Int, len: Int) {
      var i = 0
      while (i < len) { a(pos + i) = null.asInstanceOf[T] ; i += 1 }
    }

    //////// write

    def put(k: A, v: B)(implicit cmp: Ordering[A]): Option[B] = {
      val i = keySearch(k)
      if (i >= 0) {
        // update
        val z = values(i)
        setValue(i, v)
        Some(z)
      } else if (children == null) {
        // insert here
        insertEntry(-(i + 1), k, v)
        None
      } else {
        // insert in child
        val c = unsharedChild(-(i+1))
        val z = c.put(k, v)
        if (c.numKeys == MaxKeys)
          splitChild(-(i+1))
        z
      }
    }

    def remove(k: A, v: B)(implicit cmp: Ordering[A]): Option[B] = {
      val i = keySearch(k)
      if (i >= 0) {
        // hit
        if (children == null) leafRemove(i) else branchRemove(i)
      } else if (children == null) {
        // miss
        None
      } else {
        val ii = -(i+1)
        val z = unsharedChild(ii).remove(k, v)
        checkJoin(ii)
        z
      }
    }

    def branchRemove(i: Int): Option[B] = {
      val z = Some(values(i))
      unsharedChild(i).removeMax(this, i)
      checkJoin(i)
      z
    }

    def removeMax(target: Node[A,B], targetI: Int) {
      if (children == null) {
        target.setKey(targetI, keys(numKeys - 1))
        target.setValue(targetI, values(numKeys - 1))
        setKey(numKeys - 1, null.asInstanceOf[A])
        setValue(numKeys - 1, null.asInstanceOf[B])
        numKeys -= 1
      } else {
        unsharedChild(numKeys).removeMax(target, targetI)
        checkJoin(numKeys)
      }
    }

    def leafRemove(i: Int): Option[B] = {
      val z = Some(values(i))
      val kv = unsharedKeysAndValues
      System.arraycopy(kv, 2 * (i + 1), kv, 2 * i, 2 * (numKeys - i - 1))
      kv(2 * numKeys - 2) = null
      kv(2 * numKeys - 1) = null
      numKeys -= 1
      z
    }

    def checkJoin(i: Int) {
      if (i == 0) {
        checkJoin(i + 1)
      } else if (children(i - 1).numKeys + children(i).numKeys < MinKeysForPair)
        joinChildren(i - 1)
    }

    def joinChildren(i: Int) {
      // TODO
    }
  }
}