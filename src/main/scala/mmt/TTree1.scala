package mmt

import annotation.tailrec

// TTree1

private object TTree1NotFound extends TTree1.SearchResult
private object TTree1FixRequired extends TTree1.SearchResult

object TTree1 {
  trait SearchResult

  import mmt.{TTree1NotFound => NotFound}
  import mmt.{TTree1FixRequired => FixRequired}

  private def Unshared = 0 : Byte
  private def SharedKeys = 1 : Byte
  private def SharedAll = 2 : Byte

  private def Capacity = 15

  private def initKV[A,B](k: A, v: B) = {
    val kv = new Array[AnyRef](2 * Capacity)
    kv(0) = k.asInstanceOf[AnyRef]
    kv(1) = v.asInstanceOf[AnyRef]
    kv
  }

  final class Node[A,B](var _state: Byte,
                        height0: Int,
                        numKeys0: Int,
                        var left: Node[A,B],
                        var right: Node[A,B],
                        var keysAndValues: Array[AnyRef]) {
    // TODO: remove
    def state = Unshared
    def state_=(s: Byte) {}

    var _height = height0.asInstanceOf[Short]
    var _numKeys = numKeys0.asInstanceOf[Short]

    def height = _height : Int
    def height_=(v: Int) { _height = v.asInstanceOf[Short] }
    def numKeys = _numKeys : Int
    def numKeys_=(v: Int) { _numKeys = v.asInstanceOf[Short] }

    def this(k: A, v: B) = this(Unshared, 1, 1, null, null, initKV(k, v))

    def key(i: Int) = keysAndValues(2 * i).asInstanceOf[A]
    def value(i: Int) = keysAndValues(2 * i + 1).asInstanceOf[B]

    @tailrec def nodeFor(k: A)(implicit cmp: Ordering[A]): Node[A,B] = {
      if (right != null && cmp.compare(k, key(numKeys - 1)) > 0) {
        right.nodeFor(k)
      } else if (left != null && cmp.compare(k, key(0)) < 0) {
        left.nodeFor(k)
      } else {
        this
      }
    }

    def keySearch(k: A)(implicit cmp: Ordering[A]): Int = keySearch(k, 0, numKeys - 1)

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

    def unsharedLeft(): Node[A,B] = {
      if (left != null && left.state == SharedAll)
        left = left.unshare()
      left
    }

    def unsharedRight(): Node[A,B] = {
      if (right != null && right.state == SharedAll)
        right = right.unshare()
      right
    }

    def unshare(): Node[A,B] = {
      if (state != SharedAll)
        this
      else {
        // push down the mark
        if (left != null)
          left.markShared()
        if (right != null)
          right.markShared()

        // leave keysAndValues shared for now
        return new Node[A,B](SharedKeys, height, numKeys, left, right, keysAndValues)
      }
    }

    def markShared() {
      if (state != SharedAll)
        state = SharedAll
    }


    /** Returns the previous value, or NotFound. */
    def put(k: A, v: B)(implicit cmp: Ordering[A]): AnyRef = {
      if (right != null && cmp.compare(k, key(numKeys - 1)) > 0) {
        val z = unsharedRight().put(k, v)
        if (z eq FixRequired) fixRight() else z
      } else if (left != null && cmp.compare(k, key(0)) < 0) {
        val z = unsharedLeft().put(k, v)
        if (z eq FixRequired) fixLeft() else z
      } else {
        putHere(k, v)
      }
    }

    def putHere(k: A, v: B)(implicit cmp: Ordering[A]): AnyRef = {
      val i = keySearch(k)
      if (i >= 0)
        return update(k, v, i).asInstanceOf[AnyRef]
      else
        return insert(k, v, -(i + 1))
    }

//    def put(k: A, v: B)(implicit cmp: Ordering[A]): AnyRef = {
//      var min = 0
//      var max = numKeys - 1
//
//      // go right?
//      if (right != null) {
//        val c = cmp.compare(k, key(max))
//        if (c > 0) {
//          val z = unsharedRight().put(k, v)
//          return if (z eq FixRequired) fixRight() else z
//        }
//        if (c == 0)
//          return update(k, v, max).asInstanceOf[AnyRef]
//        max -= 1
//      }
//
//      // go left?
//      if (left != null) {
//        val c = cmp.compare(k, key(min))
//        if (c < 0) {
//          val z = unsharedLeft().put(k, v)
//          return if (z eq FixRequired) fixLeft() else z
//        }
//        if (c == 0)
//          return update(k, v, min).asInstanceOf[AnyRef]
//        min += 1
//      }
//
//      val i = keySearch(k, min, max)
//      if (i >= 0)
//        return update(k, v, i).asInstanceOf[AnyRef]
//      else
//        return insert(k, v, -(i + 1))
//    }

    def update(k: A, v: B, i: Int): B = {
      unshareKV()
      val z = value(i)
      keysAndValues(2 * i + 1) = v.asInstanceOf[AnyRef]
      z
    }

    def unshareKV() {
      if (state == SharedKeys) {
        val kv = new Array[AnyRef](2 * Capacity)
        System.arraycopy(keysAndValues, 0, kv, 0, 2 * Capacity)
        keysAndValues = kv
        state = Unshared
      }
    }

    def insert(k: A, v: B, i: Int): SearchResult = {
      if (i == Capacity) {
        // new right node needed
        assert(right == null)
        right = new Node(k, v)

        FixRequired
      } else {
        // this will push down the largest key if necessary
        unshareKV()
        val z = if (numKeys == Capacity) makeSpace() else NotFound

        System.arraycopy(keysAndValues, 2 * i, keysAndValues, 2 * i + 2, 2 * (numKeys - i))
        keysAndValues(2 * i) = k.asInstanceOf[AnyRef]
        keysAndValues(2 * i + 1) = v.asInstanceOf[AnyRef]
        numKeys += 1

        z
      }
    }

    def makeSpace(): SearchResult = {
      val k = key(Capacity - 1)
      val v = value(Capacity - 1)
      numKeys = Capacity - 1

      if (right == null) {
        right = new Node(k, v)
        FixRequired
      } else {
        if (unsharedRight().insertMin(k, v) eq FixRequired)
          fixRight()
        else
          NotFound
      }
    }

    def insertMin(k: A, v: B): SearchResult = {
      if (left == null && numKeys < Capacity) {
        // this is the left-most descendant of the right child of the pushing
        // node, and has space for us
        insert(k, v, 0)
        NotFound
      } else if (left == null) {
        left = new Node(k, v)
        FixRequired
      } else {
        if (unsharedLeft().insertMin(k, v) eq FixRequired)
          fixLeft()
        else
          NotFound
      }
    }

    def fixLeft(): SearchResult = {
      val prevHeight = left.height
      val newLeft = left.fixHeightAndRebalance()
      if (newLeft ne left)
        left = newLeft
      if (prevHeight != newLeft.height)
        FixRequired
      else
        NotFound
    }

    def fixRight(): SearchResult = {
      val prevHeight = right.height
      val newRight = right.fixHeightAndRebalance()
      if (newRight ne right)
        right = newRight
      if (prevHeight != newRight.height)
        FixRequired
      else
        NotFound
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

      // TODO: fix this conditional to handle removes
      if (nL.numKeys < Capacity) {
        assert(this.left == null && this.numKeys == Capacity)

        nL.unshareKV()
        val n = Capacity - nL.numKeys
        System.arraycopy(keysAndValues, 0, nL.keysAndValues, 2 * nL.numKeys, 2 * n)
        nL.numKeys = Capacity

        unshareKV()
        System.arraycopy(keysAndValues, 2 * n, keysAndValues, 0, 2 * (Capacity - n))
        var i = 2 * (Capacity - n)
        while (i < 2 * Capacity) {
          keysAndValues(i) = null
          i += 1
        }
        numKeys = Capacity - n
      }

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

      // TODO: fix this conditional
      if (nR.numKeys < Capacity) {
        assert(this.right == null && this.numKeys == Capacity)

        nR.unshareKV()
        val n = Capacity - nR.numKeys
        System.arraycopy(nR.keysAndValues, 0, nR.keysAndValues, 2 * n, 2 * (Capacity - n))
        System.arraycopy(keysAndValues, 2 * (Capacity - n), nR.keysAndValues, 0, 2 * n)
        nR.numKeys = Capacity

        unshareKV()
        var i = 2 * (Capacity - n)
        while (i < 2 * Capacity) {
          keysAndValues(i) = null
          i += 1
        }
        numKeys = Capacity - n
      }

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

    def validate()(implicit cmp: Ordering[A]) {
      if (numKeys == 0) {
        // special case for root
        assert(height == 1 && left == null && right == null)
      } else {
        assert(height == 1 + math.max(height(left), height(right)))
        assert(math.abs(height(left) - height(right)) <= 1)
        assert(numKeys > 0 && numKeys <= Capacity)
        for (i <- 0 until numKeys - 1) assert(cmp.compare(key(i), key(i + 1)) < 0)
        for (i <- numKeys until keysAndValues.length / 2) assert(key(i) == null)
        if (left != null) {
          assert(cmp.compare(left.maxKey, key(0)) < 0)
          left.validate()
        }
        if (right != null) {
          assert(cmp.compare(key(numKeys - 1), right.minKey) < 0)
          right.validate()
        }
        assert((left == null && right == null) || numKeys == Capacity)
      }
    }
  }

  abstract class Tree[A,B](implicit cmp: Ordering[A]) {

    protected var _root = new Node[A,B](Unshared, 1, 0, null, null, new Array[AnyRef](2 * Capacity))
    protected var _size = 0

    def isEmpty: Boolean = (_size == 0)
    def size: Int = _size

    def contains(key: A): Boolean = {
      _root.nodeFor(key).keySearch(key) >= 0
    }

    def get(key: A): Option[B] = {
      val n = _root.nodeFor(key)
      val i = n.keySearch(key)
      if (i < 0) None else Some(n.value(i))
    }

    def apply(key: A): B = {
      val n = _root.nodeFor(key)
      val i = n.keySearch(key)
      if (i < 0) default(key) else n.value(i)
    }

    def default(key: A): B = throw new IllegalArgumentException

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
          avail = (n.key(index), n.value(index).asInstanceOf[B])
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

    def validate() {
      assert(_size == _root.computeSize)
      if (_size >= 2) {
        for (entries <- elements.toSeq.sliding(2)) {
          assert(cmp.compare(entries(0)._1, entries(1)._1) < 0)
        }
      }
      assert(_size == elements.toSeq.size)
      _root.validate()
    }

    def dumpBFs() {
      val m = new scala.collection.mutable.HashMap[Int,Int] { override def default(k: Int) = 0 }
      def visit(n: Node[A,B]) {
        if (n != null) {
          m(n.numKeys) += 1
          visit(n.left)
          visit(n.right)
        }
      }
      visit(_root)
      for (i <- 0 to Capacity) {
        println(m(i) + " nodes with " + i + " keys")
      }
    }
  }

  class MutableTree[A,B](implicit cmp: Ordering[A]) extends Tree[A,B] {
    override def clone: MutableTree[A,B] = {
      _root.state = SharedAll
      //new MutableTree(_root, _size)
      throw new Error
    }

    def update(key: A, value: B) {
      val z = _root.put(key, value)
      if (z eq FixRequired) {
        _root = _root.fixHeightAndRebalance()
        _size += 1
      } else if (z eq NotFound) {
        _size += 1
      }
    }

    def put(key: A, value: B): Option[B] = {
      val z = _root.put(key, value)
      if (z eq FixRequired) {
        _root = _root.fixHeightAndRebalance()
        _size += 1
        None
      } else if (z eq NotFound) {
        _size += 1
        None
      } else {
        Some(z.asInstanceOf[B])
      }
    }
  }

  var cmpCount = 0

//  implicit val myOrder = new Ordering[Int] {
//    def compare(x: Int, y: Int): Int = {
//      cmpCount += 1
//      if (x < y) -1 else if (x == y) 0 else 1
//    }
//  }

  def main(args: Array[String]) {
    val rand = new scala.util.Random(0)
    for (pass <- 0 until 0) testInt(rand)
    println("------------- adding short")
    for (pass <- 0 until 10) {
      testInt(rand)
      testShort(rand)
    }
    println("------------- adding long")
    for (pass <- 0 until 10) {
      testInt(rand)
      testShort(rand)
      testLong(rand)
    }
  }

  def Range = 1<<21
  def GetPct = 0

  def testInt(rand: scala.util.Random) = {
    test[Int]("Int", rand, () => rand.nextInt(Range))
  }

  def testShort(rand: scala.util.Random) = {
    test[Short]("Short", rand, () => rand.nextInt(Range).asInstanceOf[Short])
  }

  def testLong(rand: scala.util.Random) = {
    test[Long]("Long", rand, () => rand.nextInt(Range).asInstanceOf[Long])
  }

  def test[A](name: String, rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A]) {
    cmpCount = 0
    val a = testTTree(rand, keyGen)
    val ac = cmpCount
    cmpCount = 0
    val b = testJavaTree(rand, keyGen)
    val bc = cmpCount
    println(name + ": TTree: " + a + " nanos/op,  java.util.TreeMap: " + b + " nanos/op")
    if (ac > 0) println("  TTree: " + ac + " compares,  java.util.TreeMap: " + bc + " compares")
  }

  def testTTree[A](rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A]): Int = {
    val m = new MutableTree[A,String]
    var best = Long.MaxValue
    for (group <- 1 until 10000) {
      var i = 1000
      val t0 = System.nanoTime
      while (i > 0) {
        val key = keyGen()
        val pct = rand.nextInt(100)
        if (pct < GetPct) {
          m.contains(key)
        } else {
          m(key) = "abc"
        }
        i -= 1
      }
      val elapsed = System.nanoTime - t0
      best = best min elapsed
    }
    (best / 1000).asInstanceOf[Int]
  }

  def testJavaTree[A](rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A]): Int = {
    val m = new java.util.TreeMap[A,String](cmp)
    var best = Long.MaxValue
    for (group <- 1 until 10000) {
      var i = 1000
      val t0 = System.nanoTime
      while (i > 0) {
        val key = keyGen()
        val pct = rand.nextInt(100)
        if (pct < GetPct) {
          m.containsKey(key)
        } else {
          m.put(key, "abc")
        }
        i -= 1
      }
      val elapsed = System.nanoTime - t0
      best = best min elapsed
    }
    (best / 1000).asInstanceOf[Int]
  }
}