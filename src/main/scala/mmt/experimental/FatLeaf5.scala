package mmt.experimental

import annotation.tailrec

// FatLeaf5

object FatLeaf5 {

  trait MyCmp[@specialized A] { def compare(k1: A, k2: A): Int }
  object MyCmpByte extends MyCmp[Byte] { def compare(k1: Byte, k2: Byte) = if (k1 < k2) -1 else if (k1 > k2) 1 else 0 }
  object MyCmpShort extends MyCmp[Short] { def compare(k1: Short, k2: Short) = if (k1 < k2) -1 else if (k1 > k2) 1 else 0 }
  object MyCmpChar extends MyCmp[Char] { def compare(k1: Char, k2: Char) = if (k1 < k2) -1 else if (k1 > k2) 1 else 0 }
  object MyCmpInt extends MyCmp[Int] { def compare(k1: Int, k2: Int) = if (k1 < k2) -1 else if (k1 > k2) 1 else 0 }
  object MyCmpFloat extends MyCmp[Float] { def compare(k1: Float, k2: Float) = if (k1 < k2) -1 else if (k1 > k2) 1 else 0 }
  object MyCmpLong extends MyCmp[Long] { def compare(k1: Long, k2: Long) = if (k1 < k2) -1 else if (k1 > k2) 1 else 0 }
  object MyCmpDouble extends MyCmp[Double] { def compare(k1: Double, k2: Double) = if (k1 < k2) -1 else if (k1 > k2) 1 else 0 }
  class MyCmpGeneric[@specialized A](cmp: Ordering[A]) extends MyCmp[A] { def compare(k1: A, k2: A) = cmp.compare(k1, k2) }

  implicit def specCmp[@specialized A](implicit cmp: Ordering[A]): MyCmp[A] = {
    (cmp.asInstanceOf[AnyRef] match {
      case Ordering.Byte => MyCmpByte
      case Ordering.Short => MyCmpShort
      case Ordering.Char => MyCmpChar
      case Ordering.Int => MyCmpInt
      case Ordering.Float => MyCmpFloat
      case Ordering.Long => MyCmpLong
      case Ordering.Double => MyCmpDouble
      case _ => new MyCmpGeneric(cmp)
    }).asInstanceOf[MyCmp[A]]
  }

  ////////

  def LeafMin = 15
  def LeafMax = 2 * LeafMin + 1

  class Node[@specialized A,B](var parent: Node[A,B],
                               var height: Int,
                               var key: A,
                               var value: B,
                               var left: Node[A,B],
                               var right: Node[A,B],
                               var size: Int,
                               var keys: Array[A],
                               var values: Array[B]) {
    def isLeaf = left == null
  }

  def newEmptyRootHolder[@specialized A,B](implicit am: ClassManifest[A], bm: ClassManifest[B]) = {
    val h = new Node[A,B](null, -1, null.asInstanceOf[A], null.asInstanceOf[B], null, null, 0, null, null)
    h.right = new Node[A,B](h, 1, null.asInstanceOf[A], null.asInstanceOf[B], null, null,
                            0, new Array[A](LeafMax), new Array[B](LeafMax))
    h
  }

  def newTree[@specialized A,B](implicit cmp: Ordering[A], am: ClassManifest[A], bm: ClassManifest[B]): MutableTree[A,B] = {
    (am.newArray(0).asInstanceOf[AnyRef] match {
      case _: Array[Unit] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Unit]]
        new MutableTree[Unit,B](newEmptyRootHolder[Unit,B], 0)
      }
      case _: Array[Boolean] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Boolean]]
        new MutableTree[Boolean,B](newEmptyRootHolder[Boolean,B], 0)
      }
      case _: Array[Byte] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Byte]]
        new MutableTree[Byte,B](newEmptyRootHolder[Byte,B], 0)
      }
      case _: Array[Short] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Short]]
        new MutableTree[Short,B](newEmptyRootHolder[Short,B], 0)
      }
      case _: Array[Char] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Char]]
        new MutableTree[Char,B](newEmptyRootHolder[Char,B], 0)
      }
      case _: Array[Int] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Int]]
        new MutableTree[Int,B](newEmptyRootHolder[Int,B], 0)
      }
      case _: Array[Float] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Float]]
        new MutableTree[Float,B](newEmptyRootHolder[Float,B], 0)
      }
      case _: Array[Long] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Long]]
        new MutableTree[Long,B](newEmptyRootHolder[Long,B], 0)
      }
      case _: Array[Double] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Double]]
        new MutableTree[Double,B](newEmptyRootHolder[Double,B], 0)
      }
      case _: Array[AnyRef] => new MutableTree[A,B](newEmptyRootHolder[A,B], 0)
    }).asInstanceOf[MutableTree[A,B]]
  }

  class MutableTree[@specialized A,B](val rootHolder: Node[A,B], var _size: Int)(
          implicit cmp: MyCmp[A], am: ClassManifest[A], bm: ClassManifest[B]) {

//    {
//      println("hello?")
//      // We'd like to fill in the rootHolder during construction (and let it be a
//      // val), but that seems to cause specialization of the root Branch to not
//      // occur.  Actually we don't care much about the Branch, but the Leaf it
//      // contains should be specialized.
//      if (rootHolder == null) {
//        rootHolder = new Branch[A,B](null)
//        rootHolder.right = new Leaf[A,B](rootHolder, 0)
//      }
//    }

//    def this()(implicit cmp: Ordering[A], am: ClassManifest[A], bm: ClassManifest[B]) =
//        this(newEmptyRootHolder[A,B], 0)

    def newLeaf(p: Node[A,B], size: Int, kk: Array[A], vv: Array[B]): Node[A,B] =
        new Node[A,B](p, 1, null.asInstanceOf[A], null.asInstanceOf[B], null, null, size, kk, vv)
    def newLeaf(p: Node[A,B], size: Int): Node[A,B] =
        newLeaf(p, size, new Array[A](LeafMax), new Array[B](LeafMax))
    def newBranch(p: Node[A,B], h: Int, k: A, v: B, left: Node[A,B], right: Node[A,B]) =
        new Node[A,B](p, h, k, v, left, right, 0, null, null)

    //////// bulk

    def isEmpty = _size == 0
    def size = _size

    override def clone() = {
      markShared(rootHolder.right)
      new MutableTree(newBranch(null, -1, null.asInstanceOf[A], null.asInstanceOf[B], null, rootHolder.right), _size)
    }

    //////// reads

    def contains(k: A): Boolean = {
      var n = rootHolder.right
      (while (true) {
        if (n.isLeaf) {
          return keySearch(n, k) >= 0
        } else {
          val c = cmp.compare(k, n.key)
          if (c == 0)
            return true
          n = if (c < 0) n.left else n.right
        }
      }).asInstanceOf[Nothing]
    }

    def get(k: A): Option[B] = {
      var n = rootHolder.right
      (while (true) {
        if (n.isLeaf) {
          val i = keySearch(n, k)
          return if (i >= 0) Some(n.values(i)) else None
        } else {
          val c = cmp.compare(k, n.key)
          if (c == 0)
            return Some(n.value)
          n = if (c < 0) n.left else n.right
        }
      }).asInstanceOf[Nothing]
    }

    def keySearch(n: Node[A,B], k: A): Int = {
      var b = 0
      var e = n.size
      while (b < e) {
        val mid = (b + e) >>> 1
        val c = cmp.compare(k, n.keys(mid))
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

    def put(k: A, v: B): Option[B] = {
      var n = unsharedRight(rootHolder)
      (while (true) {
        if (n.isLeaf) {
          val i = keySearch(n, k)
          if (i >= 0) {
            val z = n.values(i)
            n.values(i) = v
            return Some(z)
          } else {
            insert(n, ~i, k, v)
            _size += 1
            return None
          }
        } else {
          val c = cmp.compare(k, n.key)
          if (c == 0) {
            // update
            val z = n.value
            n.value = v
            return Some(z)
          } else {
            n = if (c < 0) unsharedLeft(n) else unsharedRight(n)
          }
        }
      }).asInstanceOf[Nothing]
    }

    def update(k: A, v: B) {
      put(k, v)
      //validate()
    }

    def insert(n: Node[A,B], i: Int, k: A, v: B) {
      // make space
      val num = n.size
      System.arraycopy(n.keys, i, n.keys, i + 1, num - i)
      System.arraycopy(n.values, i, n.values, i + 1, num - i)
      n.size = num + 1

      // copy the values
      n.keys(i) = k
      n.values(i) = v

      // split if necessary
      if (num + 1 == LeafMax) split(n)
    }

    def split(tL: Node[A,B]) {
      val leftSize = LeafMax / 2
      val rightSize = LeafMax - 1 - leftSize

      // existing terminal becomes left leaf, create new branch
      val b = newBranch(tL.parent, 2, tL.keys(leftSize), tL.values(leftSize), tL, null)
      val tR = newLeaf(b, rightSize)
      b.right = tR

      // copy to right
      System.arraycopy(tL.keys, leftSize + 1, tR.keys, 0, rightSize)
      System.arraycopy(tL.values, leftSize + 1, tR.values, 0, rightSize)

      // fix up left
      tL.parent = b
      tL.size = leftSize
      clear(tL, leftSize, 1 + rightSize)

      // link into parent
      replaceAndRepair(tL, b)
    }

    def clear(t: Node[A,B], pos: Int, len: Int) {
      clear(t.keys, pos, len)
      clear(t.values, pos, len)
    }

    def clear[@specialized C](a: Array[C], pos: Int, len: Int) {
      var i = pos
      while (i < pos + len) { a(i) = null.asInstanceOf[C] ; i += 1 }
    }

    //////// remove

    def remove(k: A): Option[B] = {
      var n = unsharedRight(rootHolder)
      (while (true) {
        if (n.isLeaf) {
          val i = keySearch(n, k)
          if (i >= 0) {
            val z = n.values(i)
            removeFromLeaf(n, i)
            _size -= 1
            return Some(z)
          } else {
            return None
          }
        } else {
          val c = cmp.compare(k, n.key)
          if (c == 0) {
            val z = n.value
            removeMax(n, unsharedLeft(n))
            _size -= 1
            return Some(z)
          } else {
            n = if (c < 0) unsharedLeft(n) else unsharedRight(n)
          }
        }
      }).asInstanceOf[Nothing]
    }

    def -=(k: A) {
      remove(k)
      //validate()
    }

    @tailrec private def removeMax(target: Node[A,B], n: Node[A,B]) {
      if (n.isLeaf) {
        // steal one
        val i = n.size - 1
        target.key = n.keys(i)
        target.value = n.values(i)
        removeMaxFromLeaf(n)
      } else {
        removeMax(target, unsharedRight(n))
      }
    }

    def removeMaxFromLeaf(n: Node[A,B]) {
      val num = n.size - 1
      n.size = num
      clear(n, num, 1)
      if (num < LeafMin) refill(n)
    }

    def removeFromLeaf(n: Node[A,B], i: Int) {
      // slide down
      val num = n.size - 1
      System.arraycopy(n.keys, i + 1, n.keys, i, num - i)
      System.arraycopy(n.values, i + 1, n.values, i, num - i)
      n.size = num

      clear(n, num, 1)

      // join or steal if necessary
      if (num < LeafMin) refill(n)
    }

    def refill(n: Node[A,B]): Unit = n.parent.height match {
      case -1 => {} // root holder has height -1, root can't be refilled
      case 2 => {
        if (n.parent.left eq n)
          refillAsLeft(n)
        else
          refillAsRight(n)
      }
      case 3 => {
        // refill is easier if our sibling is a leaf
        val p = n.parent
        if (p.left eq n) {
          replace(p, rotateLeft(p))
          refillAsLeft(n)
        } else {
          replace(p, rotateRight(p))
          refillAsRight(n)
        }
      }
    }

    def refillAsLeft(tL: Node[A,B]) {
      assert(tL.size == LeafMin - 1)
      val b = tL.parent
      val tR = unsharedRight(b)
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
  
    def refillAsRight(tR: Node[A,B]) {
      assert(tR.size == LeafMin - 1)
      val b = tR.parent
      val tL = unsharedLeft(b)
      if (tL.size == LeafMin)
        merge(b, tL, tR)
      else {
        insert(tR, 0, b.key, b.value)
        b.key = tL.keys(tL.size - 1)
        b.value = tL.values(tL.size - 1)
        removeMaxFromLeaf(tL)
      }
    }

    def merge(b: Node[A,B], tL: Node[A,B], tR: Node[A,B]) {
      assert(1 + tL.size + tR.size == LeafMax - 1)
      val leftSize = tL.size
      tL.keys(leftSize) = b.key
      tL.values(leftSize) = b.value
      System.arraycopy(tR.keys, 0, tL.keys, leftSize + 1, LeafMax - 1 - (leftSize + 1))
      tL.size = LeafMax - 1
      tL.parent = b.parent

      replaceAndRepair(b, tL)
    }

    //////// sharing machinery

    def unsharedLeft(b: Node[A,B]): Node[A,B] = {
      if (b.left.parent == null)
        b.left = unshare(b.left, b)
      b.left
    }

    def unsharedRight(b: Node[A,B]): Node[A,B] = {
      if (b.right.parent == null)
        b.right = unshare(b.right, b)
      b.right
    }

    def unshare(n: Node[A,B], p: Node[A,B]): Node[A,B] = {
      if (n.isLeaf) {
        newLeaf(p, n.size, n.keys.clone(), n.values.clone())
      } else {
        markShared(n.left)
        markShared(n.right)
        newBranch(p, n.height, n.key, n.value, n.left, n.right)
      }
    }

    def markShared(n: Node[A,B]) { n.parent = null }


    //////// AVL rebalancing

    def height(n: Node[A,B]) = n.height

    def balance(n: Node[A,B]) = if (n.isLeaf) 0 else n.left.height - n.right.height
    
    def repair(b: Node[A,B]) {
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
        replaceAndMaybeRepair(b, h0, if (balance(b.left) < 0) rotateRightOverLeft(b) else rotateRight(b))
      } else if (bal < -1) {
        replaceAndMaybeRepair(b, h0, if (balance(b.right) > 0) rotateLeftOverRight(b) else rotateLeft(b))
      } else {
        // no rotations needed, just update height
        val h = 1 + math.max(hL, hR)
        if (h != h0) {
          b.height = h
          repair(b.parent)
        }
      }
    }

    def replaceAndMaybeRepair(n0: Node[A,B], h0: Int, n: Node[A,B]) {
      replace(n0, n)
      if (n.height != h0) repair(n.parent)
    }

    def replaceAndRepair(n0: Node[A,B], n: Node[A,B]) {
      replace(n0, n)
      repair(n.parent)
    }

    def replace(n0: Node[A,B], n: Node[A,B]) {
      val p = n.parent
      if (p.left eq n0) p.left = n else p.right = n
    }

    def rotateRight(b: Node[A,B]): Node[A,B] = {
      val nL = unsharedLeft(b)
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

    def rotateRightOverLeft(b: Node[A,B]): Node[A,B] = {
      b.left = rotateLeft(unsharedLeft(b))
      rotateRight(b)
    }

    def rotateLeft(b: Node[A,B]): Node[A,B] = {
      val nR = unsharedRight(b)
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

    def rotateLeftOverRight(b: Node[A,B]): Node[A,B] = {
      b.right = rotateRight(unsharedRight(b))
      rotateLeft(b)
    }

    //////// enumeration

    def foreach(block: ((A,B)) => Unit) { foreach(rootHolder.right, block) }

    def foreach(n: Node[A,B], block: ((A,B)) => Unit) {
      if (n.isLeaf) {
        var i = 0
        while (i < n.size) { block((n.keys(i), n.values(i))) ; i += 1 }
      } else {
        foreach(n.left, block)
        block((n.key, n.value))
        foreach(n.right, block)
      }
    }

    def elements: Iterator[(A,B)] = new Iterator[(A,B)] {
      private val stack = new Array[Node[A,B]](height(rootHolder.right))
      private var depth = 0
      private var index = 0

      if (_size > 0) pushMin(rootHolder.right)

      @tailrec final def pushMin(n: Node[A,B]) {
        stack(depth) = n
        depth += 1
        if (!n.isLeaf)
          pushMin(n.left)
      }

      private def advance() {
        val n = stack(depth - 1)
        if (n.isLeaf) {
          if (index + 1 < n.size) {
            // more entries in this node
            index += 1
          } else {
            index = 0
            // no children, so just pop
            depth -= 1
            stack(depth) = null
          }
        } else {
          // pop current node
          depth -= 1
          pushMin(n.right)
        }
      }

      def hasNext = depth > 0

      def next = {
        if (depth == 0) throw new IllegalStateException
        val n = stack(depth - 1)
        val z = if (n.isLeaf) (n.keys(index), n.values(index)) else (n.key, n.value)
        advance()
        z
      }
    }

    //////// validation

    def validate() {
      val root = rootHolder.right
      if (_size == 0) {
        assert(root.isLeaf && root.size == 0)
      } else {
        validate(rootHolder)
        assert(_size == computeSize(root))
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

    def computeSize(n: Node[A,B]): Int =
        if (n.isLeaf) n.size else computeSize(n.left) + 1 + computeSize(n.right)

    def validate(n: Node[A,B]) {
      if (n.height < 0) {
        // rootHolder
        assert(n.left == null && n.right != null)
        validate(n.right)
      } else if (n.height == 1) {
        assert(n.isLeaf)
        assert(n.size >= LeafMin || n.parent.height < 0)
        assert(n.size < LeafMax)
      } else {
        assert(!n.isLeaf)
        assert(n.left != null && (n.left.parent eq n))
        assert(n.right != null && (n.right.parent eq n))
        assert(n.height == 1 + math.max(height(n.left), height(n.right)))
        assert(math.abs(balance(n)) <= 1)
        validate(n.left)
        validate(n.right)
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
    val rands = Array.tabulate(6) { _ => new scala.util.Random(0) }
    for (pass <- 0 until 0) {
      testInt(rands(0))
    }
    println("------------- adding short")
    for (pass <- 0 until 0) {
      testInt(rands(1))
      testShort(rands(2))
    }
    println("------------- adding custom")
    for (pass <- 0 until 10) {
      testInt(rands(3))
      testShort(rands(4))
      testCustom(rands(5))
    }
  }

  def Range = 1000
  def InitialGetPct = 50
  def GetPct = 50 // 70 //95
  def IterPct = 1.0 / Range

  def testInt(rand: scala.util.Random) = {
    test[Int]("  Int", rand, () => rand.nextInt(Range))
  }

  def testShort(rand: scala.util.Random) = {
    test[Short]("Short", rand, () => rand.nextInt(Range).asInstanceOf[Short])
  }

  case class Custom(v: Int)

  implicit object CustomCmp extends Ordering[Custom] {
    def compare(x: Custom, y: Custom): Int = {
      if (x.v < y.v) -1 else if (x.v == y.v) 0 else 1
    }
  }

  def testCustom(rand: scala.util.Random) = {
    test[Custom](" Custom", rand, () => Custom(rand.nextInt(Range)))
  }

  def test[@specialized A](name: String, rand: scala.util.Random, keyGen: () => A)(
          implicit cmp: Ordering[A], am: ClassManifest[A]) {
    cmpCount = 0
    val (abest,aavg) = testFatLeaf4(rand, keyGen)
    val ac = cmpCount
    //println("!!")
    cmpCount = 0
    val (bbest,bavg) = testFatLeaf5(rand, keyGen)
    val bc = cmpCount
    cmpCount = 0
    val (cbest,cavg) = testJavaTree(rand, keyGen)
    val cc = cmpCount
    println(name + ": FatLeaf4: " + abest + " nanos/op (" + aavg + " avg),  " +
            name + ": FatLeaf5: " + bbest + " nanos/op (" + bavg + " avg),  " +
            "java.util.TreeMap: " + cbest + " nanos/op (" + cavg + " avg)")
    if (ac > 0)
      println("  FatLeaf4: " + ac + " compares,  FatLeaf5: " + bc +
              " compares,  java.util.TreeMap: " + cc + " compares")
  }

  def testFatLeaf5[@specialized A](rand: scala.util.Random, keyGen: () => A)(
          implicit cmp: Ordering[A], am: ClassManifest[A]): (Long,Long) = {
    val tt0 = System.currentTimeMillis
    val m = FatLeaf5.newTree[A,String]
    var best = Long.MaxValue
    for (group <- 1 until 10000) {
      val gp = if (group < 1000) InitialGetPct else GetPct
      var i = 1000
      val t0 = System.nanoTime
      var matching = 0
      while (i > 0) {
        val key = keyGen()
        val pct = rand.nextDouble() * 100
        if (pct < gp) {
          if (m.contains(key)) matching += 1
        } else if (pct < gp + IterPct) {
          // iterate
          var n = 0
          //for (e <- m.elements) n += 1
          for (e <- m) n += 1
          assert(n == m.size)
        } else if (pct < 50 + (gp + IterPct) / 2) {
          m(key) = "abc"
        } else {
          m -= key
        }
        i -= 1
      }
      if (matching < 0) println("unlikely")
      val elapsed = System.nanoTime - t0
      if (group >= 1000) best = best min elapsed
    }
    val total = System.currentTimeMillis - tt0
    (best / 1000, total / 10)
  }

  def testFatLeaf4[@specialized A](rand: scala.util.Random, keyGen: () => A)(
          implicit cmp: Ordering[A], am: ClassManifest[A]): (Long,Long) = {
    val tt0 = System.currentTimeMillis
    val m = FatLeaf4.newTree[A,String]
    var best = Long.MaxValue
    for (group <- 1 until 10000) {
      val gp = if (group < 1000) InitialGetPct else GetPct
      var i = 1000
      val t0 = System.nanoTime
      var matching = 0
      while (i > 0) {
        val key = keyGen()
        val pct = rand.nextDouble() * 100
        if (pct < gp) {
          if (m.contains(key)) matching += 1
        } else if (pct < gp + IterPct) {
          // iterate
          var n = 0
          //for (e <- m.elements) n += 1
          for (e <- m) n += 1
          assert(n == m.size)
        } else if (pct < 50 + (gp + IterPct) / 2) {
          m(key) = "abc"
        } else {
          m -= key
        }
        i -= 1
      }
      if (matching < 0) println("unlikely")
      val elapsed = System.nanoTime - t0
      if (group >= 1000) best = best min elapsed
    }
    val total = System.currentTimeMillis - tt0
    (best / 1000, total / 10)
  }

  def testJavaTree[@specialized A](rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A]): (Long,Long) = {
    val tt0 = System.currentTimeMillis
    val m = new java.util.TreeMap[A,String](cmp)
    var best = Long.MaxValue
    for (group <- 1 until 10000) {
      val gp = if (group < 1000) InitialGetPct else GetPct
      var i = 1000
      val t0 = System.nanoTime
      var matching = 0
      while (i > 0) {
        val key = keyGen()
        val pct = rand.nextDouble() * 100
        if (pct < gp) {
          if (m.containsKey(key)) matching += 1
        } else if (pct < gp + IterPct) {
          // iterate
          var n = 0
          val iter = m.entrySet.iterator
          while (iter.hasNext) {
            iter.next()
            n += 1
          }
          assert(n == m.size)
        } else if (pct < 50 + (gp + IterPct) / 2) {
          m.put(key, "abc")
        } else {
          m.remove(key)
        }
        i -= 1
      }
      if (matching < 0) println("unlikely")
      val elapsed = System.nanoTime - t0
      if (group >= 1000) best = best min elapsed
    }
    val total = System.currentTimeMillis - tt0
    (best / 1000, total / 10)
  }
}