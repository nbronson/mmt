package mmt

import annotation.tailrec

// TTree1

object TTree1 {
  private def Unshared = 0 : Byte
  private def SharedKeys = 1 : Byte
  private def SharedAll = 2 : Byte

  private val NotFound = new Object

  private def InitialKeyCapacity = 4
  private def MaxKeyCapacity = 32

  sealed class Node[A,B](var state: Byte,
                         var height: Byte,
                         var numKeys: Short,
                         var left: Node[A,B],
                         var right: Node[A,B],
                         var keysAndValues: Array[Any]) {

    def key(i: Int) = keysAndValues(2 * i).asInstanceOf[A]
    def value(i: Int) = keysAndValues(2 * i + 1).asInstanceOf[B]

    @tailrec def find(k: A)(implicit cmp: Ordering[A]): Any = {
      var min = 0
      var max = numKeys - 1

      // go right?
      if (right != null) {
        val c = cmp.compare(k, key(max))
        if (c > 0)
          return right.find(k)
        if (c == 0)
          return value(max)
        max -= 1
      }

      // go left?
      if (left != null) {
        val c = cmp.compare(k, key(min))
        if (c < 0)
          return left.find(k)
        if (c == 0)
          return value(min)
        min += 1
      }

      // search remaining keys
      val i = keySearch(k, min, max)

      return if (i < 0) NotFound else value(i)
    }

    /** On entry, k > key(min-1) && k < key(max+1) */
    @tailrec def keySearch(k: A, min: Int, max: Int)(implicit cmp: Ordering[A]): Int = {
      if (min > max) {
        // min == max + 1, so k > key(min-1) && k < key(min).  Insert at min
        -(min + 1)
      } else {
        val mid = (min + max) >>> 1
        val c = cmp.compare(k, key(mid))
        if (c < 0)
          keySearch(k, min, mid - 1)
        else if (c > 0)
          keySearch(k, mid + 1, max)
        else
          mid
      }
    }

    def unshare: Node[A,B] = {
      if (state != SharedAll)
        this
      else {
        // push down the mark
        if (left != null) left.markShared()
        if (right != null) right.markShared()

        // leave keysAndValues shared for now
        return new Node(SharedKeys, height, numKeys, left, right, keysAndValues)
      }
    }

    def markShared() {
      if (state != SharedAll) state = SharedAll
    }


    /** Returns the previous value, or NotFound. */
    @tailrec def update(k: A, v: B)(implicit cmp: Ordering[A]): Any = {
      var min = 0
      var max = numKeys - 1

      // go right?
      if (right != null) {
        val c = cmp.compare(k, key(max))
        if (c > 0) {
          if (right.state == SharedAll) right = right.unshare
          return right.update(k, v)
        }
        if (c == 0)
          return update(k, v, i)
        max -= 1
      }

      // go left?
      if (left != null) {
        val c = cmp.compare(k, key(min))
        if (c < 0) {
          if (left.state == SharedAll) left = left.unshare
          return left.update(k, v)
        }
        if (c == 0)
          return update(k, v, i)
        min += 1
      }

      // search remaining keys
      val i = keySearch(k, min, max)

      return if (i < 0) NotFound else update(k, v, i)
    }

    def update(k: A, v: B, i: Int): Any = {
      unshareKeys()
      val prev = value(i)
      keysAndValues(2 * i + 1) = v
      prev
    }

    def unshareKeys() {
      if (state == SharedKeys) {
        keysAndValues = keysAndValues.clone()
        state = Unshared
      }
    }

    def insert(k: A, v: B)(implicit cmp: Ordering[A]): Node[A,B] = {
      var min = 0
      var max = numKeys - 1

      // go right?
      if (right != null) {
        val c = cmp.compare(k, key(max))
        if (c > 0) {
          val n = right.unshare.insert(k, v)
          if (n ne right) right = n // avoid M and E states for nodes near the root
          return rotateLeftIfNeeded()
        }
        assert(c != 0) // this is insert, not put
        max -= 1
      }

      // go left?
      if (left != null) {
        val c = cmp.compare(k, key(min))
        if (c < 0) {
          val n = left.unshare.insert(k, v)
          if (n ne left) left = n
          return rotateRightIfNeeded()
        }
        assert(c != 0)
        min += 1
      }

      // search remaining keys, failing if found
      val i = -(keySearch(k, min, max) + 1)
      assert(i >= 0 && i < numKeys)

      // this will push down the largest key if necessary, and clone if necessary
      val fixLater = prepareForInsert()

      // slide down
      Array.copy(keysAndValues, 2 * i, keysAndValues, 2 * i + 2, 2 * (numKeys - i))
      keysAndValues(2 * i) = k
      keysAndValues(2 * i + 1) = v
      numKeys += 1

      return if (fixLater) rotateLeftIfNeeded() else this 
    }
  }

  abstract class Tree[A,B](implicit cmp: Ordering[A]) {
    import TTree1._

    protected var _root: Node[A,B] =
        new Node(Unshared, 1, 0, null, null, new Array[Any](2 * InitialKeyCapacity))
    protected var _size = 0

    def isEmpty: Boolean = (_size == 0)
    def size: Int = _size

    def contains(key: A): Boolean = NotFound != _root.find(key)

    def get(key: A): Option[B] = _root.find(key) match {
      case NotFound => None
      case x => Some(x.asInstanceOf[B])
    }

    def apply(key: A): B = _root.find(key) match {
      case NotFound => defaultValue(key)
      case x => x.asInstanceOf[B]
    }

    def defaultValue(key: A): B = throw new IllegalArgumentException
  }

  class MutableTree[A,B](implicit cmp: Ordering[A]) extends Tree {
    def clone: MutableTree[A,B] = {
      _root.state = SharedAll
      new MutableTree(_root, _size)
    }

    def put(key: A, value: B): Option[B] = _root.update(key, value) match {
      case NotFound => {
        _root = _root.insert(key, value)
        _size += 1
        None
      }
      case x => Some(x.asInstanceOf[B])
    }
  }
}