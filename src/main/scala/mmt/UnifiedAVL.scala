package mmt

import annotation.tailrec

// UnifiedAVL

private object UnifiedAVLNotFound

object UnifiedAVL {
  
  import mmt.{UnifiedAVLNotFound => NotFound}

  final class Node[A,B](height0: Int,
                        var left: Node[A,B],
                        var right: Node[A,B],
                        var key: A,
                        var value: B) {

    def this(k: A, v: B) = this(1, null, null, k, v)

    private var _height = height0.asInstanceOf[Byte]
    def height = _height : Int
    def height_=(v: Int) { _height = v.asInstanceOf[Byte] }

    var shared = false

    @tailrec def find(k: A)(implicit cmp: Ordering[A]): Node[A,B] = {
      val c = cmp.compare(k, key)
      if (c < 0) {
        if (left == null) null else left.find(k)
      } else if (c > 0) {
        if (right == null) null else right.find(k)
      } else {
        this
      }
    }

    def unsharedLeft: Node[A,B] = {
      if (left != null && left.shared)
        left = left.unshare
      left
    }

    def unsharedRight: Node[A,B] = {
      if (right != null && right.shared)
        right = right.unshare
      right
    }

    def unshare: Node[A,B] = {
      if (!shared) {
        this
      } else {
        // push down the mark
        if (left != null) left.markShared()
        if (right != null) right.markShared()

        return new Node(height, left, right, key, value)
      }
    }

    def markShared() {
      if (!shared)
        shared = true
    }

    /** Returns the previous value, or NotFound. */
    def put(k: A, v: B)(implicit cmp: Ordering[A]): AnyRef = {
      assert(!shared)

      val c = cmp.compare(k, key)
      if (c < 0) {
        if (left == null) {
          left = new Node(k, v)
          NotFound
        } else {
          val z = unsharedLeft.put(k, v)
          if (z eq NotFound) fixLeft()
          z
        }
      } else if (c > 0) {
        if (right == null) {
          right = new Node(k, v)
          NotFound
        } else {
          val z = unsharedRight.put(k, v)
          if (z eq NotFound) fixRight()
          z
        }
      } else {
        val z = value
        value = v
        z.asInstanceOf[AnyRef]
      }
    }

    def fixLeft() {
      val n = left.fix()
      if (n ne left)
        left = n
    }

    def fixRight() {
      val n = right.fix()
      if (n ne right)
        right = n
    }

    def fix(): Node[A,B] = {
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

    @tailrec def minKey: A = if (left != null) left.minKey else key

    @tailrec def maxKey: A = if (right != null) right.maxKey else key

    def computeSize: Int = {
      1 + (if (left != null) left.computeSize else 0) + (if (right != null) right.computeSize else 0)
    }

    def validate(implicit cmp: Ordering[A]) {
      assert(height == 1 + math.max(height(left), height(right)))
      assert(math.abs(height(left) - height(right)) <= 1)
      if (left != null) {
        assert(cmp.compare(left.maxKey, key) < 0)
        left.validate
      }
      if (right != null) {
        assert(cmp.compare(key, right.minKey) < 0)
        right.validate
      }
    }
  }

  abstract class Tree[A,B](implicit cmp: Ordering[A]) {

    protected var _root: Node[A,B] = null
    protected var _size = 0

    def isEmpty: Boolean = (_size == 0)
    def size: Int = _size

    def contains(key: A): Boolean = _root != null && _root.find(key) != null

    def get(key: A): Option[B] = {
      if (_root == null) {
        None
      } else {
        _root.find(key) match {
          case null => None
          case n => Some(n.value)
        }
      }
    }

    def apply(key: A): B = {
      (if (_root == null) null else _root.find(key)) match {
        case null => default(key)
        case n => n.value
      }
    }

    def default(key: A): B = throw new IllegalArgumentException

    def elements: Iterator[(A,B)] = new Iterator[(A,B)] {
      private val stack = new Array[Node[A,B]](_root.height)
      private var depth = 0
      pushMin(_root)

      @tailrec private def pushMin(node: Node[A,B]) {
        if (node != null) {
          stack(depth) = node
          depth += 1
          pushMin(node.left)
        }
      }

      private def advance() {
        depth -= 1
        pushMin(stack(depth).right)
      }

      def hasNext = depth > 0

      def next = {
        if (depth == 0) throw new NoSuchElementException
        val n = stack(depth - 1)
        val z = (n.key, n.value)
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
//    override def clone: MutableTree[A,B] = {
//      _root.state = SharedAll
//      //new MutableTree(_root, _size)
//      throw new Error
//    }

    private def createRoot(k: A, v: B): AnyRef = {
      _root = new Node(k, v)
      NotFound
    }

    def update(key: A, value: B) {
      if (_root == null) {
        _root = new Node(key, value)
        _size = 1
      } else if (_root.put(key, value) eq NotFound) {
        _root = _root.fix()
        _size += 1
      }
//      validate
    }

    def put(key: A, value: B): Option[B] = {
      if (_root == null) {
        _root = new Node(key, value)
        _size = 1
        None
      } else {
        val z = _root.put(key, value)
        if (z eq NotFound) {
          _root = _root.fix()
          _size += 1
//          validate
          None
        } else {
//          validate
          Some(z.asInstanceOf[B])
        }
      }
    }
  }

  def main1(args: Array[String]) {
    val rand = new scala.util.Random
    for (pass <- 0 until 50) test(rand)
  }

  def test(rand: scala.util.Random) {
    val a = testMyTree(rand)
    val b = 0 // testJavaTree(rand)
    println("MyTree: " + a + " nanos/op,  java.util.TreeMap: " + b + " nanos/op")
  }

  def testMyTree(rand: scala.util.Random): Int = {
    val t0 = System.currentTimeMillis
    val m = new MutableTree[Int,String]
    var i = 1000000
    while (i > 0) {
      val key = rand.nextInt(10000)
      val pct = rand.nextInt(100)
      if (pct < 80) {
        m.contains(key)
      } else {
        m(key) = "abc"
      }
      i -= 1
      if (i == 100000)
        m.contains(0)
    }
    (System.currentTimeMillis - t0).intValue
  }

  def testJavaTree(rand: scala.util.Random): Int = {
    val t0 = System.currentTimeMillis
    val m = new java.util.TreeMap[Int,String](implicitly[Ordering[Int]])
    var i = 1000000
    while (i > 0) {
      val key = rand.nextInt(10000)
      val pct = rand.nextInt(100)
      if (pct < 80) {
        m.containsKey(key)
      } else {
        m.put(key, "abc")
      }
      i -= 1
    }
    (System.currentTimeMillis - t0).intValue
  }
}