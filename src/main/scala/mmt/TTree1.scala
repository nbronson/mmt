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

  private def initKV(k: Any, v: Any) = {
    val kv = new Array[Any](2 * InitialKeyCapacity)
    kv(0) = k
    kv(1) = v
    kv
  }

  sealed class Node[A,B](var state: Byte,
                         height0: Int,
                         numKeys0: Int,
                         var left: Node[A,B],
                         var right: Node[A,B],
                         var keysAndValues: Array[Any]) {
    var _height = height0.asInstanceOf[Short]
    var _numKeys = numKeys0.asInstanceOf[Short]

    def height = _height : Int
    def height_=(v: Int) { _height = v.asInstanceOf[Short] }
    def numKeys = _numKeys : Int
    def numKeys_=(v: Int) { _numKeys = v.asInstanceOf[Short] }

    def this(k: A, v: B) = this(Unshared, 1, 1, null, null, initKV(k, v))

    def key(i: Int) = keysAndValues(2 * i).asInstanceOf[A]
    def value(i: Int) = keysAndValues(2 * i + 1).asInstanceOf[B]

    // TODO: @tailrec
    def find(k: A)(implicit cmp: Ordering[A]): Any = {
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
    @tailrec final def keySearch(k: A, min: Int, max: Int)(implicit cmp: Ordering[A]): Int = {
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
        return new Node[A,B](SharedKeys, height, numKeys, left, right, keysAndValues)
      }
    }

    def markShared() {
      if (state != SharedAll) state = SharedAll
    }


    /** Returns the previous value, or NotFound. */
    // TODO: @tailrec
    def update(k: A, v: B)(implicit cmp: Ordering[A]): Any = {
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
          return update(k, v, max)
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
          return update(k, v, min)
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
          return fixHeightAndRebalance()
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
          return fixHeightAndRebalance()
        }
        assert(c != 0)
        min += 1
      }

      // search remaining keys, failing if found
      val i = -(keySearch(k, min, max) + 1)
      assert(i > 0 || (i == 0 && left == null))
      assert(i < numKeys || (i == numKeys && right == null))

      return insert(k, v, i)
    }

    def insert(k: A, v: B, i: Int): Node[A,B] = {
      if (i == MaxKeyCapacity) {
        // new right node needed
        assert(right == null)
        right = new Node(k, v)
        return fixHeightAndRebalance()
      }

      // TODO: clean up code

      // this will push down the largest key if necessary, and clone if necessary
      val fixLater = prepareForInsert()

      Array.copy(keysAndValues, 2 * i, keysAndValues, 2 * i + 2, 2 * (numKeys - i))
      keysAndValues(2 * i) = k
      keysAndValues(2 * i + 1) = v
      numKeys += 1

      return if (fixLater) fixHeightAndRebalance() else this
    }

    def prepareForInsert(): Boolean = {
      if (numKeys * 2 < keysAndValues.length) {
        // no resize or push-down needed
        unshareKeys()
        false
      } else if (numKeys < MaxKeyCapacity) {
        // resize is sufficient, unshare and resize at the same time
        val kv = new Array[Any](numKeys * 4)
        Array.copy(keysAndValues, 0, kv, 0, numKeys * 2)
        keysAndValues = kv
        state = Unshared

        // no push-down, so no rebalancing needed later
        false
      } else {
        // this node is full, move its maximum entry to the right
        unshareKeys()
        val k = key(numKeys - 1)
        val v = value(numKeys - 1)
        right = if (right == null) new Node(k, v) else right.unshare.pushMin(k, v)
        numKeys -= 1

        // caller must recompute height and check balance
        true
      }
    }

    def pushMin(k: A, v: B): Node[A,B] = {
      if (left == null && numKeys < MaxKeyCapacity) {
        // this is the left-most descendant of the right child of the pushing
        // node, and has space for us
        return insert(k, v, 0)
      } else {
        left = if (left == null) new Node(k, v) else left.unshare.pushMin(k, v)
        return fixHeightAndRebalance()
      }
    }

    def fixHeightAndRebalance(): Node[A,B] = {
      val hL = height(left)
      val hR = height(right)
      val bal = hL - hR
      if (bal > 1) {
        // Left is too large, rotate right.  If left.right is larger than
        // left.left then rotating right will lead to a -2 balance, so
        // first we have to rotateLeft on left.
        if (left.balance < 0)
          rotateRightOverLeft()
        else
          rotateRight()
      } else if (bal < -1) {
        if (right.balance > 0)
          rotateLeftOverRight()
        else
          rotateLeft()
      } else {
        // no rotations needed, just update height
        val h = 1 + math.max(hL, hR)
        if (h != height) height = h
        this
      }
    }

    def height(node: Node[_,_]): Int = if (node == null) 0 else node.height

    def balance = height(left) - height(right)

    def rotateRight(): Node[A,B] = {
      val nL = left.unshare
      this.left = nL.right
      nL.right = this
      this.height = 1 + math.max(height(left), height(right))
      nL.height = 1 + math.max(height(nL.left), this.height)
      nL
    }

    def rotateRightOverLeft(): Node[A,B] = {
      this.left = this.left.unshare.rotateLeft()
      rotateRight()
    }

    def rotateLeft(): Node[A,B] = {
      val nR = right.unshare
      this.right = nR.left
      nR.left = this
      this.height = 1 + math.max(height(right), height(left))
      nR.height = 1 + math.max(height(nR.right), this.height)
      nR
    }

    def rotateLeftOverRight(): Node[A,B] = {
      this.right = this.right.unshare.rotateRight()
      rotateLeft()
    }

    @tailrec final def minKey: A = if (left != null) left.minKey else key(0)

    @tailrec final def maxKey: A = if (right != null) right.maxKey else key(numKeys - 1)

    def computeSize: Int = {
      numKeys + (if (left != null) left.computeSize else 0) + (if (right != null) right.computeSize else 0)
    }

    def validate(implicit cmp: Ordering[A]) {
      if (numKeys == 0) {
        // special case for root
        assert(height == 1 && left == null && right == null)
      } else {
        assert(height == 1 + math.max(height(left), height(right)))
        assert(math.abs(height(left) - height(right)) <= 1)
        assert(numKeys > 0 && numKeys <= MaxKeyCapacity)
        for (i <- 0 until numKeys - 1) assert(cmp.compare(key(i), key(i + 1)) < 0)
        for (i <- numKeys until keysAndValues.length / 2) assert(key(i) == null)
        if (left != null) {
          assert(cmp.compare(left.maxKey, key(0)) < 0)
          left.validate
        }
        if (right != null) {
          assert(cmp.compare(key(numKeys - 1), right.minKey) < 0)
          right.validate
        }
      }
    }
  }

  abstract class Tree[A,B](implicit cmp: Ordering[A]) {

    protected var _root = new Node[A,B](Unshared, 1, 0, null, null, new Array[Any](2 * InitialKeyCapacity))
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

    def elements: Iterator[(A,B)] = new Iterator[(A,B)] {
      private val stack = new Array[Node[A,B]](_root.height)
      private var depth = 0
      private var index = -1
      private var avail: (A,B) = null
      pushMin(_root)
      advance()

      @tailrec private def pushMin(node: Node[A,B]) {
        if (node != null) {
          stack(depth) = node
          depth += 1
          pushMin(node.left)
        }
      }

      // TODO: fix
      private def advance() {
        if (depth > 0) {
          val n = stack(depth - 1)
          if (index + 1 < n.numKeys) {
            // there is another entry in this node
            index += 1
          } else {
            index = 0
            depth -= 1
            if (n.right != null) {
              pushMin(n.right)
            } else {
              stack(depth) = null
            }
          }
        }
        if (depth > 0) {
          val n = stack(depth - 1)
          avail = (n.key(index), n.value(index))
        } else {
          avail = null
        }
      }

      def hasNext = (avail != null)
      
      def next = {
        val z = avail
        if (z == null) throw new IllegalStateException
        advance()
        z
      }
    }

    def validate {
      assert(_size == _root.computeSize)
      if (_size >= 2) {
        for (entries <- elements.toSeq.sliding(2)) {
          assert(cmp.compare(entries(0)._1, entries(1)._1) < 0)
        }
      }
      assert(_size == elements.toSeq.size)
      _root.validate
    }
  }

  class MutableTree[A,B](implicit cmp: Ordering[A]) extends Tree[A,B] {
    override def clone: MutableTree[A,B] = {
      _root.state = SharedAll
      //new MutableTree(_root, _size)
      throw new Error
    }

    def update(key: A, value: B) {
      if (NotFound == _root.update(key, value)) {
        _root = _root.insert(key, value)
        _size += 1
      }
      validate
    }

    def put(key: A, value: B): Option[B] = _root.update(key, value) match {
      case NotFound => {
        _root = _root.insert(key, value)
        _size += 1
        validate
        None
      }
      case x => {
        validate
        Some(x.asInstanceOf[B])
      }
    }
  }
}