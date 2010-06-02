package mmt

import annotation.tailrec

// FatLeaf

private object FatLeafNotFound

object FatLeaf {
  import mmt.{FatLeafNotFound => NotFound}

  private def Capacity = 15
  private def MinExtras = 6

  private def initKV[A,B](k: A, v: B) = {
    val kv = new Array[AnyRef](2 * Capacity)
    kv(0) = k.asInstanceOf[AnyRef]
    kv(1) = v.asInstanceOf[AnyRef]
    kv
  }

  final class Node[A,B] (var _height: Byte,
                         var _extraSize: Byte,
                         var key: A, // unused in leaf nodes
                         var value: B, // unused in leaf nodes
                         var parent: Node[A,B],
                         var left: Node[A,B],
                         var right: Node[A,B],
                         var extras: Array[AnyRef]) {

    def this(h: Int, k: A, v: B, p: Node[A,B], left0: Node[A,B], right0: Node[A,B]) =
      this(h.asInstanceOf[Byte], 0: Byte, k, v, p, left0, right0, null)

    def this(es: Int, p: Node[A,B], extras0: Array[AnyRef]) =
      this(1: Byte, es.asInstanceOf[Byte], null.asInstanceOf[A], null.asInstanceOf[B], p, null, null, extras0)

    def this(es: Int, p: Node[A,B]) = this(es, p, new Array[AnyRef](2 * Capacity))


    def height: Int = _height
    def height_=(v: Int) { _height = v.asInstanceOf[Byte] }

    def isLeaf = left == null // _extraSize != (0: Byte)

    def extraSize: Int = _extraSize & 255
    def extraSize_=(s: Int) { _extraSize = s.asInstanceOf[Byte] }

    def keys(i: Int): A = extras(2 * i).asInstanceOf[A]
    def setKey(i: Int, k: A) { extras(2 * i) = k.asInstanceOf[AnyRef] }

    def values(i: Int): B = extras(2 * i + 1).asInstanceOf[B]
    def setValue(i: Int, v: B) { extras(2 * i + 1) = v.asInstanceOf[AnyRef] }

    def shared = parent eq null

    //////// reads

    @tailrec def nodeForRead(k: A)(implicit cmp: Ordering[A]): Node[A,B] = {
      if (isLeaf) {
        this
      } else {
        val c = cmp.compare(k, key)
        if (c < 0) {
          left.nodeForRead(k)
        } else if (c > 0) {
          right.nodeForRead(k)
        } else {
          // exact match
          this
        }
      }
    }

    def keySearch(k: A)(implicit cmp: Ordering[A]): Int = keySearch(k, 0, extraSize - 1)

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

    //////// navigation on MUTABLE trees

    @tailrec def unsharedLeftmost(): Node[A,B] = {
      if (isLeaf) this else unsharedLeft().unsharedLeftmost()
    }

    @tailrec def unsharedRightmost(): Node[A,B] = {
      if (isLeaf) this else unsharedRight().unsharedRightmost()
    }

    // TODO: do we need this?
    def unsharedPred(): Node[A,B] = {
      if (isLeaf) parentPred else unsharedLeft().unsharedRightmost()
    }

    @tailrec def parentPred: Node[A,B] = {
      if (parent == null)
        null
      else if (this eq parent.right)
        parent
      else
        parent.parentPred
    }

    def unsharedSucc(): Node[A,B] = {
      if (isLeaf) parentSucc else unsharedRight().unsharedLeftmost()
    }

    @tailrec def parentSucc: Node[A,B] = {
      if (parent == null)
        null
      else if (this eq parent.left)
        parent
      else
        parent.parentSucc
    }
    
    /** On exit, left.state will be either SharedExtra or Unshared. */
    def unsharedLeft(): Node[A,B] = {
      if (left.shared)
        left = left.unshare(this)
      left
    }

    def unsharedRight(): Node[A,B] = {
      if (right.shared)
        right = right.unshare(this)
      right
    }

    def unshare(p: Node[A,B]): Node[A,B] = {
      if (!shared) {
        this
      } else if (isLeaf) {
        // clone the keys and values array as well
        new Node[A,B](1: Byte, _extraSize, key, value, p, null, null, extras.clone())
      } else {
        // push down the mark first
        left.markShared()
        right.markShared()
        new Node[A,B](_height, 0: Byte, key, value, p, left, right, null)
      }
    }

    def markShared() {
      if (!shared)
        parent = null
    }

    //////// writes

    @tailrec def nodeForWrite(k: A)(implicit cmp: Ordering[A]): Node[A,B] = {
      if (isLeaf) {
        this
      } else {
        val c = cmp.compare(k, key)
        if (c < 0)
          unsharedLeft().nodeForWrite(k)
        else if (c > 0)
          unsharedRight().nodeForWrite(k)
        else
          this
      }
    }

    def putHere(k: A, v: B)(implicit cmp: Ordering[A]): AnyRef = {
      if (isLeaf)
        leafPut(k, v)
      else
        internalUpdate(v)
    }

    def internalUpdate(v: B): AnyRef = {
      val z = value
      value = v
      z.asInstanceOf[AnyRef]
    }

    def leafPut(k: A, v: B)(implicit cmp: Ordering[A]): AnyRef = {
      val i = keySearch(k)
      if (i >= 0) {
        // this is an update
        val z = values(i)
        setValue(i, v)
        z.asInstanceOf[AnyRef]
      } else if (extraSize < Capacity) {
        // insert, space available
        easyInsert(k, v, -(i + 1))
        NotFound
      } else {
        splittingInsert(k, v, -(i + 1))
        NotFound
      }
    }

    def easyInsert(k: A, v: B, i: Int) {
      val n = extraSize - i
      System.arraycopy(extras, 2 * i, extras, 2 * (i + 1), 2 * n)
      setKey(i, k)
      setValue(i, v)
      extraSize += 1
    }

    def splittingInsert(k: A, v: B, i: Int) {
      //assert(extraSize == Capacity && height == 1)

      // we've got Capacity + 1 entries to distribute.  1 goes in this.
      val leftSize = (Capacity + 1) / 2
      val rightSize = Capacity + 1 - 1 - leftSize
      val newLeft = new Node(leftSize, this, extras)
      val newRight = new Node(Capacity - leftSize, this)

      // at this point, extras eq left.extras

      if (i < leftSize) {
        // right-most elements go to the right
        System.arraycopy(extras, 2 * (Capacity - rightSize), newRight.extras, 0, 2 * rightSize)

        // k goes in left, element at leftSize - 1 would become the element at
        // leftSize if we had an intermediate copy to a single flat array of
        // size Capacity + 1
        key = keys(leftSize - 1)
        value = values(leftSize - 1)

        // insert k and v
        System.arraycopy(extras, 2 * i, extras, 2 * (i + 1), 2 * (leftSize - 1 - i))
        setKey(i, k)
        setValue(i, v)
      } else if (i > leftSize) {
        // k goes in right, element at leftSize becomes the pivot
        val ii = i - (leftSize + 1)
        System.arraycopy(extras, 2 * (leftSize + 1), newRight.extras, 0, 2 * ii)
        newRight.setKey(ii, k)
        newRight.setValue(ii, v)
        System.arraycopy(extras, 2 * i, newRight.extras, 2 * (ii + 1), 2 * (rightSize - 1 - ii))

        key = keys(leftSize)
        value = values(leftSize)

        // left.extras only needs a clear
      } else {
        // k and v become the new pivot
        System.arraycopy(extras, 2 * leftSize, newRight.extras, 0, 2 * rightSize)
        key = k
        value = v
      }

      // clear the right half of the reused array
      var j = 2 * leftSize
      while (j < 2 * Capacity) {
        extras(j) = null
        j += 1
      }

      // link the nodes properly
      height = 2
      extraSize = 0
      left = newLeft
      right = newRight

      // we've grown, so we might need to rebalance the parent
      parent.fixHeightAndRebalance()
    }

    def removeHere(k: A)(implicit cmp: Ordering[A]): AnyRef = {
      if (isLeaf)
        leafRemove(k)
      else
        internalRemove()
    }

    def internalRemove(): AnyRef = {
      val z = value

      // It's easier to steal from the end of our predecessor than from the
      // beginning of our successor.  This is an internal node, so its
      // predecessor is a leaf.
      val pred = unsharedLeft().unsharedRightmost()
      assert(pred.isLeaf)

      // steal one entry from the predecessor
      val i = pred.extraSize - 1
      key = pred.keys(i)
      value = pred.values(i)
      pred.trimExtras(i, 1)

      if (pred.extraSize < MinExtras)
        pred.refill()

      z.asInstanceOf[AnyRef]
    }

    def openExtras(pos: Int, len: Int) {
      val n = extraSize
      System.arraycopy(extras, 2 * pos, extras, 2 * (pos + len), 2 * (n + len))
      extraSize = n + len
    }

    def trimExtras(pos: Int, len: Int) {
      assert(pos >= 0 && len >= 0 && pos + len <= extraSize)
      val n = extraSize
      System.arraycopy(extras, 2 * (pos + len), extras, 2 * pos, 2 * (n - (pos + len)))
      var j = 2 * (n - len)
      while (j < 2 * n) {
        extras(j) = null
        j += 1
      }
      extraSize = n - len
    }

    def leafRemove(k: A)(implicit cmp: Ordering[A]): AnyRef = {
      val i = keySearch(k)
      if (i < 0) {
        NotFound
      } else {
        val z = values(i)
        trimExtras(i, 1)
        if (extraSize < MinExtras)
          refill()
        z.asInstanceOf[AnyRef]
      }
    }

    def refill() {
      // can't refill if this is the root
      parent.height match {
        case 2 => parent.pack2()
        case 3 => parent.pack3()
        case _ => // parent.height == -1 means we are the root, can't refill
      }
    }

    def pack2() {
      assert(left.isLeaf && right.isLeaf)

      val n = left.extraSize + 1 + right.extraSize
      if (n <= Capacity)
        merge2(n)
      else if (left.extraSize < right.extraSize)
        shuffleLeft2()
      else
        shuffleRight2()
    }

    def merge2(newSize: Int) {
      // We can merge the three nodes into one.  We'll use left's extra array
      extras = if (left.shared) left.extras.clone() else left.extras
      setKey(left.extraSize, key)
      setValue(left.extraSize, value)
      System.arraycopy(right.extras, 0, extras, 2 * (left.extraSize + 1), 2 * right.extraSize)

      // turn this into a leaf
      height = 1
      extraSize = newSize
      left = null
      right = null

      // rebalancing may be required
      parent.fixHeightAndRebalance()
    }

    def shuffleLeft2() {
      val n = (right.extraSize - MinExtras + 1) / 2

      // deal with left
      left.setKey(left.extraSize, key)
      left.setValue(left.extraSize, value)
      System.arraycopy(right.extras, 0, left.extras, 2 * (left.extraSize + 1), 2 * (n - 1))
      left.extraSize += n

      // fix this
      key = right.keys(n - 1)
      value = right.values(n - 1)

      // trim from right
      right.trimExtras(0, n)

      assert(left.extraSize >= MinExtras)
      assert(right.extraSize >= MinExtras)
    }

    def shuffleRight2() {
      val n = (left.extraSize - MinExtras + 1) / 2

      // deal with right
      right.openExtras(0, n)
      right.setKey(n - 1, key)
      right.setValue(n - 1, value)
      System.arraycopy(left.extras, 2 * (left.extraSize - n + 1), right.extras, 0, 2 * (n - 1))

      // fix this
      key = left.keys(left.extraSize - n)
      value = left.values(left.extraSize - n)

      // trim from left
      left.trimExtras(left.extraSize - n, n)

      assert(left.extraSize >= MinExtras)
      assert(right.extraSize >= MinExtras)
    }

    def computeSize: Int = {
      if (isLeaf)
        extraSize
      else
        1 + left.computeSize + right.computeSize
    }

    def flattenInto(kv: Array[AnyRef], i: Int): Int = {
      if (isLeaf) {
        System.arraycopy(extras, 0, kv, i, 2 * extraSize)
        i + 2 * extraSize
      } else {
        val i1 = left.flattenInto(kv, i)
        kv(i1) = key.asInstanceOf[AnyRef]
        kv(i1 + 1) = value.asInstanceOf[AnyRef]
        right.flattenInto(kv, i1 + 2)
      }
    }

    def pack3() {
      val n = computeSize
      val kv = new Array[AnyRef](2 * n)
      flattenInto(kv, 0)
      if (n <= 2 * Capacity + 1) {
        unpack2(kv, n)
        parent.fixHeightAndRebalance()
      } else {
        // we need three leaves again
        val rightSize = (n - 2) / 3
        val leftSize = n - rightSize - 1

        left.unpack2(kv, leftSize)

        key = kv(2 * leftSize).asInstanceOf[A]
        value = kv(2 * leftSize + 1).asInstanceOf[B]

        right = new Node(rightSize, this)
        System.arraycopy(kv, 2 * (n - rightSize), right.extras, 0, 2 * rightSize)
      }
    }

    def unpack2(kv: Array[AnyRef], n: Int) {
      // we can fit into a branch and two leaves
      val leftSize = n / 2

      left = new Node[A,B](leftSize, this)
      assert(2 * leftSize <= 2 * Capacity)
      assert(2 * leftSize <= kv.length)
      System.arraycopy(kv, 0, left.extras, 0, 2 * leftSize)

      key = kv(2 * leftSize).asInstanceOf[A]
      value = kv(2 * leftSize + 1).asInstanceOf[B]

      right = new Node[A,B](n - leftSize - 1, this)
      System.arraycopy(kv, 2 * (leftSize + 1), right.extras, 0, 2 * (n - leftSize - 1))

      height = 2
    }

    //////// rebalancing

    def fixHeightAndRebalance() {
      val h0 = height

      // rootHolder
      if (h0 < 0) return

      val hL = left.height
      val hR = right.height
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
          parent.fixHeightAndRebalance()
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
        repl.parent.fixHeightAndRebalance()
      }
    }

    def balance = left.height - right.height

    def rotateRight(): Node[A,B] = {
      val nL = left.unshare(this)
      nL.parent = parent

      left = nL.right
      if (!left.shared)
        left.parent = this

      nL.right = this
      parent = nL

      height = 1 + math.max(left.height, right.height)
      nL.height = 1 + math.max(nL.left.height, height)

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
      if (!right.shared)
        right.parent = this

      nR.left = this
      parent = nR

      height = 1 + math.max(right.height, left.height)
      nR.height = 1 + math.max(nR.right.height, height)

      nR
    }

    def rotateLeftOverRight(): Node[A,B] = {
      right = right.unshare(this).rotateRight()
      rotateLeft()
    }

    @tailrec def minKey: A = if (!isLeaf) left.minKey else keys(0)

    @tailrec def maxKey: A = if (!isLeaf) right.maxKey else keys(extraSize - 1)

    def validate()(implicit cmp: Ordering[A]) {
      if (height < 0) {
        // rootHolder
        assert(left == null && right != null)
      } else if (isLeaf) {
        assert(extraSize >= MinExtras || parent.height < 0)
        assert(extraSize <= Capacity)
        assert(right == null)
      } else {
        assert(left != null && (left.parent eq this))
        assert(right != null && (right.parent eq this))
        assert(extraSize == 0)
        assert(height == 1 + math.max(left.height, right.height))
        assert(math.abs(left.height - right.height) <= 1)
        left.validate()
        right.validate()
      }
    }
  }

  abstract class Tree[A,B](implicit cmp: Ordering[A]) {

    protected val rootHolder = {
      val h = new Node[A,B](-1: Byte, 0: Byte, null.asInstanceOf[A], null.asInstanceOf[B], null, null, null, null)
      h.right = new Node[A,B](1: Byte, 0: Byte, null.asInstanceOf[A], null.asInstanceOf[B], h, null, null, new Array[AnyRef](2 * Capacity))
      h
    }

    protected def root = rootHolder.right
    protected var _size = 0

    def isEmpty: Boolean = (_size == 0)
    def size: Int = _size

    def contains(key: A): Boolean = {
      val n = root.nodeForRead(key)
      !n.isLeaf || n.keySearch(key) >= 0
    }

    def get(key: A): Option[B] = {
      val n = root.nodeForRead(key)
      if (!n.isLeaf) {
        Some(n.value)
      } else {
        val i = n.keySearch(key)
        if (i >= 0)
          Some(n.values(i))
        else
          None
      }
    }

    def apply(key: A): B = {
      val n = root.nodeForRead(key)
      if (n.extraSize == 0) {
        n.value
      } else {
        val i = n.keySearch(key)
        if (i >= 0)
          n.values(i)
        else
          default(key)
      }
    }

    def default(key: A): B = throw new IllegalArgumentException

    def elements: Iterator[(A,B)] = new Iterator[(A,B)] {
      // TODO: rewrite using a stack to support iteration without unsharing
      
      private var current: Node[A,B] = if (root.isLeaf && root.extraSize == 0) null else root.unsharedLeftmost()
      private var index = 0

      def hasNext = (current != null)
      
      def next = {
        if (current == null)
          throw new IllegalStateException
        if (current.height == 1) {
          val z = (current.keys(index), current.values(index))
          if (index + 1 >= current.extraSize) {
            index = 0
            current = current.unsharedSucc()
          } else {
            index += 1
          }
          z
        } else {
          val z = (current.key, current.value)
          current = current.unsharedSucc()
          z
        }
      }
    }

    def validate() {
      if (_size == 0) {
        assert(root.isLeaf && root.extraSize == 0)
      } else {
        assert(_size == root.computeSize)
        root.validate()
      }
      if (_size >= 2) {
        for (entries <- elements.toSeq.sliding(2)) {
          assert(cmp.compare(entries(0)._1, entries(1)._1) < 0)
        }
      }
      val s = elements.toSeq
      val ss = s.size
      assert(_size == ss)
    }
  }

  class MutableTree[A,B](implicit cmp: Ordering[A]) extends Tree[A,B] {

    def update(key: A, value: B) {
      putImpl(key, value)
      //validate()
    }

    def put(key: A, value: B): Option[B] = {
      val z = putImpl(key, value)
      if (z eq NotFound) None else Some(z.asInstanceOf[B])
    }

    private def putImpl(key: A, value: B): AnyRef = {
      val z = root.nodeForWrite(key).putHere(key, value)
      if (z eq NotFound)
        _size += 1
      z
    }

    def -=(key: A) {
      removeImpl(key)
      //validate()
    }

    def remove(key: A): Option[B] = {
      val z = removeImpl(key)
      if (z eq NotFound) None else Some(z.asInstanceOf[B])
    }

    private def removeImpl(key: A): AnyRef = {
      val z = root.nodeForWrite(key).removeHere(key)
      if (z ne NotFound)
        _size -= 1
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

  def Range = 10000000
  def GetPct = 0

  def testInt(rand: scala.util.Random) = {
    test[Int]("  Int", rand, () => rand.nextInt(Range))
  }

  def testShort(rand: scala.util.Random) = {
    test[Short]("Short", rand, () => rand.nextInt(Range).asInstanceOf[Short])
  }

  def testLong(rand: scala.util.Random) = {
    test[Long](" Long", rand, () => rand.nextInt(Range).asInstanceOf[Long])
  }

  def test[A](name: String, rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A]) {
    cmpCount = 0
    val (abest,aavg) = testTTree(rand, keyGen)
    val ac = cmpCount
    //println("!!")
    cmpCount = 0
    val (bbest,bavg) = testJavaTree(rand, keyGen)
    val bc = cmpCount
    println(name + ": FatLeaf: " + abest + " nanos/op (" + aavg + " avg),  " +
            "java.util.TreeMap: " + bbest + " nanos/op (" + bavg + " avg)")
    if (ac > 0) println("  FatLeaf: " + ac + " compares,  java.util.TreeMap: " + bc + " compares")
  }

  def testTTree[A](rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A]): (Long,Long) = {
    val tt0 = System.currentTimeMillis
    val m = new MutableTree[A,String]
    var best = Long.MaxValue
    for (group <- 1 until 10000) {
      var i = 1000
      val t0 = System.nanoTime
      var matching = 0
      while (i > 0) {
        val key = keyGen()
        val pct = rand.nextInt(200)
        if (pct < 2 * GetPct) {
          if (m.contains(key)) matching += 1
        } else if ((pct & 1) == 0) {
          m(key) = "abc"
        } else {
          m -= key
        }
        i -= 1
      }
      if (matching < 0) println("unlikely")
      val elapsed = System.nanoTime - t0
      best = best min elapsed
    }
    val total = System.currentTimeMillis - tt0
    (best / 1000, total / 10)
  }

  def testJavaTree[A](rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A]): (Long,Long) = {
    val tt0 = System.currentTimeMillis
    val m = new java.util.TreeMap[A,String](cmp)
    var best = Long.MaxValue
    for (group <- 1 until 10000) {
      var i = 1000
      val t0 = System.nanoTime
      var matching = 0
      while (i > 0) {
        val key = keyGen()
        val pct = rand.nextInt(200)
        if (pct < 2 * GetPct) {
          if (m.containsKey(key)) matching += 1
        } else if ((pct & 1) == 0) {
          m.put(key, "abc")
        } else {
          m.remove(key)
        }
        i -= 1
      }
      if (matching < 0) println("unlikely")
      val elapsed = System.nanoTime - t0
      best = best min elapsed
    }
    val total = System.currentTimeMillis - tt0
    (best / 1000, total / 10)
  }
}