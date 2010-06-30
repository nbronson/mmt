package mmt.experimental

import annotation.tailrec

// TTree2

object TTree2 {
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

  final class Node[A,B](var state: Byte,
                        height0: Int,
                        numKeys0: Int,
                        var parent: Node[A,B],
                        var left: Node[A,B],
                        var right: Node[A,B],
                        var keysAndValues: Array[AnyRef]) {

    def this(p: Node[A,B], k: A, v: B) = this(Unshared, 1, 1, p, null, null, initKV(k, v))

    //def state = Unshared
    //def state_=(s: Byte) {}

    var _height = height0.asInstanceOf[Byte]
    var _numKeys = numKeys0.asInstanceOf[Short]

    def height = _height : Int
    def height_=(v: Int) { _height = v.asInstanceOf[Byte] }
    def numKeys = _numKeys : Int
    def numKeys_=(v: Int) { _numKeys = v.asInstanceOf[Short] }

    def key(i: Int) = keysAndValues(2 * i).asInstanceOf[A]
    def value(i: Int) = keysAndValues(2 * i + 1).asInstanceOf[B]

    @tailrec def nodeForGet(k: A)(implicit cmp: Ordering[A]): Node[A,B] = {
      if (right != null && cmp.compare(k, key(numKeys - 1)) > 0) {
        right.nodeForGet(k)
      } else if (left != null && cmp.compare(k, key(0)) < 0) {
        left.nodeForGet(k)
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
        left = left.unshare(this)
      left
    }

    def unsharedRight(): Node[A,B] = {
      if (right != null && right.state == SharedAll)
        right = right.unshare(this)
      right
    }

    def unshare(p: Node[A,B]): Node[A,B] = {
      if (state != SharedAll)
        this
      else {
        // push down the mark
        if (left != null)
          left.markShared()
        if (right != null)
          right.markShared()

        // leave keysAndValues shared for now
        return new Node[A,B](SharedKeys, height, numKeys, p, left, right, keysAndValues)
      }
    }

    def markShared() {
      if (state != SharedAll) {
        state = SharedAll
        parent = null
      }
    }

    @tailrec def nodeForPut(k: A)(implicit cmp: Ordering[A]): Node[A,B] = {
      if (right != null && cmp.compare(k, key(numKeys - 1)) > 0) {
        unsharedRight().nodeForPut(k)
      } else if (left != null && cmp.compare(k, key(0)) < 0) {
        unsharedLeft().nodeForPut(k)
      } else {
        this
      }
    }

    def putHere(k: A, v: B)(implicit cmp: Ordering[A]): Option[B] = {
      val i = keySearch(k)
      if (i >= 0) {
        Some(update(k, v, i))
      } else {
        insert(k, v, -(i + 1))
        None
      }
    }

    def storeHere(k: A, v: B)(implicit cmp: Ordering[A]): Boolean = {
      val i = keySearch(k)
      if (i >= 0) {
        update(k, v, i)
        false
      } else {
        insert(k, v, -(i + 1))
        true
      }
    }

    def update(k: A, v: B, i: Int): B = {
      unshareKV()
      val z = value(i)
      keysAndValues(2 * i + 1) = v.asInstanceOf[AnyRef]
      z
    }

    def unshareKV() {
      if (state == SharedKeys) {
        //val kv = new Array[AnyRef](2 * Capacity)
        //System.arraycopy(keysAndValues, 0, kv, 0, 2 * Capacity)
        //keysAndValues = kv
        keysAndValues = keysAndValues.clone()
        state = Unshared
      }
    }

    def insert(k: A, v: B, i: Int) {
      if (i == Capacity) {
        // new right node needed
        assert(right == null)
        right = new Node(this, k, v)
        fix()
      } else {
        // this will push down the largest key if necessary
        unshareKV()
        if (numKeys == Capacity) {
          val k0 = key(Capacity - 1)
          val v0 = value(Capacity - 1)
          numKeys = Capacity - 1

          insertHere(k, v, i)

          if (right == null) {
            right = new Node(this, k0, v0)
            fix()
          } else {
            unsharedRight().insertMin(k0, v0)
          }
        } else {
          insertHere(k, v, i)
        }
      }
    }

    def insertHere(k: A, v: B, i: Int) {
      System.arraycopy(keysAndValues, 2 * i, keysAndValues, 2 * i + 2, 2 * (numKeys - i))
      keysAndValues(2 * i) = k.asInstanceOf[AnyRef]
      keysAndValues(2 * i + 1) = v.asInstanceOf[AnyRef]
      numKeys += 1
    }

    def insertMin(k: A, v: B) {
      if (left == null && numKeys < Capacity) {
        // this is the left-most descendant of the right child of the pushing
        // node, and has space for us
        insert(k, v, 0)
      } else if (left == null) {
        left = new Node(this, k, v)
        fix()
      } else {
        unsharedLeft().insertMin(k, v)
      }
    }

    def fix() {
      val h0 = height

      // rootHolder
      if (h0 < 0) return

      val hL = height(left)
      val hR = height(right)
      val bal = hL - hR
      if (bal > 1) {
        // Left is too large, rotate right.  If left.right is larger than
        // left.left then rotating right will lead to a -2 balance, so
        // first we have to rotateLeft on left.
        replaceInParent(h0, if (left.balance < 0) rotateRightOverLeft() else rotateRight())
      } else if (bal < -1) {
        replaceInParent(h0, if (right.balance > 0) rotateLeftOverRight() else rotateLeft())
      } else {
        // no rotations needed, just update height
        val h = 1 + math.max(hL, hR)
        if (h != height) {
          height = h
          parent.fix()
        }
      }
    }

    def replaceInParent(oldHeight: Int, repl: Node[A,B]) {
      if (this eq repl.parent.right) {
        repl.parent.right = repl
      } else {
        repl.parent.left = repl
      }
      if (repl.height != oldHeight) {
        repl.parent.fix()
      }
    }

    def height(node: Node[_,_]): Int = if (node == null) 0 else node.height

    def balance = height(left) - height(right)

    def rotateRight(): Node[A,B] = {
      val nL = left.unshare(this)
      nL.parent = parent

      left = nL.right
      if (left != null && left.parent != null)
        left.parent = this

      nL.right = this
      parent = nL

      height = 1 + math.max(height(left), height(right))
      nL.height = 1 + math.max(height(nL.left), height)

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
      left = left.unshare(this).rotateLeft()
      rotateRight()
    }

    def rotateLeft(): Node[A,B] = {
      val nR = right.unshare(this)
      nR.parent = parent

      right = nR.left
      if (right != null && right.parent != null)
        right.parent = this

      nR.left = this
      parent = nR

      height = 1 + math.max(height(right), height(left))
      nR.height = 1 + math.max(height(nR.right), height)

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
      right = right.unshare(this).rotateRight()
      rotateLeft()
    }

    @tailrec def minKey: A = if (left != null) left.minKey else key(0)

    @tailrec def maxKey: A = if (right != null) right.maxKey else key(numKeys - 1)

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

    private val rootHolder = {
      val h = new Node[A,B](Unshared, -1, 0, null, null, null, null)
      h.right = new Node[A,B](Unshared, 1, 0, h, null, null, new Array[AnyRef](2 * Capacity))
      h
    }

    protected def root = rootHolder.right
    protected var _size = 0

    def isEmpty: Boolean = (_size == 0)
    def size: Int = _size

    def contains(key: A): Boolean = {
      root.nodeForGet(key).keySearch(key) >= 0
    }

    def get(key: A): Option[B] = {
      val n = root.nodeForGet(key)
      val i = n.keySearch(key)
      if (i < 0) None else Some(n.value(i))
    }

    def apply(key: A): B = {
      val n = root.nodeForGet(key)
      val i = n.keySearch(key)
      if (i < 0) default(key) else n.value(i)
    }

    def default(key: A): B = throw new IllegalArgumentException

    def elements: Iterator[(A,B)] = new Iterator[(A,B)] {
      private val stack = new Array[Node[A,B]](root.height)
      private var depth = 0
      private var index = -1
      private var avail: (A,B) = null
      pushMin(root)
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
      assert(_size == root.computeSize)
      if (_size >= 2) {
        for (entries <- elements.toSeq.sliding(2)) {
          assert(cmp.compare(entries(0)._1, entries(1)._1) < 0)
        }
      }
      assert(_size == elements.toSeq.size)
      root.validate()
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
      visit(root)
      for (i <- 0 to Capacity) {
        println(m(i) + " nodes with " + i + " keys")
      }
    }
  }

  class MutableTree[A,B](implicit cmp: Ordering[A]) extends Tree[A,B] {
    def update(key: A, value: B) {
      if (root.nodeForPut(key).storeHere(key, value))
        _size += 1
    }

    def put(key: A, value: B): Option[B] = {
      val z = root.nodeForPut(key).putHere(key, value)
      if (z.isEmpty)
        _size += 1
      z
    }
  }

  var cmpCount = 0

//  implicit val myOrder = new Ordering[Int] {
//    def compare(x: Int, y: Int): Int = {
//      cmpCount += 1
//      if (x < y) -1 else if (x == y) 0 else 1
//    }
//  }

  def main0(args: Array[String]) {
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
    println(name + ": TTree2: " + a + " nanos/op,  java.util.TreeMap: " + b + " nanos/op")
    if (ac > 0) println("  TTree2: " + ac + " compares,  java.util.TreeMap: " + bc + " compares")
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