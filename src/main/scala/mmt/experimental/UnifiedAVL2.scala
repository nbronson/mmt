package mmt.experimental

import annotation.tailrec

// UnifiedAVL2

object UnifiedAVL2 {

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

  class Node[@specialized A,B](var parent: Node[A,B],
                               var height: Int,
                               var key: A,
                               var value: B,
                               var left: Node[A,B],
                               var right: Node[A,B]) {
    def this(right0: Node[A,B]) = this(null, -1, null.asInstanceOf[A], null.asInstanceOf[B], null, right0)
    def this(p: Node[A,B], k: A, v: B) = this(p, 1, k, v, null, null)
  }

  def newTree[@specialized A,B](implicit cmp: Ordering[A], am: ClassManifest[A]): MutableTree[A,B] = {
    (am.newArray(0).asInstanceOf[AnyRef] match {
      case _: Array[Unit] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Unit]]
        new MutableTree[Unit,B](new Node[Unit,B](null), 0)
      }
      case _: Array[Boolean] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Boolean]]
        new MutableTree[Boolean,B](new Node[Boolean,B](null), 0)
      }
      case _: Array[Byte] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Byte]]
        new MutableTree[Byte,B](new Node[Byte,B](null), 0)
      }
      case _: Array[Short] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Short]]
        new MutableTree[Short,B](new Node[Short,B](null), 0)
      }
      case _: Array[Char] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Char]]
        new MutableTree[Char,B](new Node[Char,B](null), 0)
      }
      case _: Array[Int] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Int]]
        new MutableTree[Int,B](new Node[Int,B](null), 0)
      }
      case _: Array[Float] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Float]]
        new MutableTree[Float,B](new Node[Float,B](null), 0)
      }
      case _: Array[Long] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Long]]
        new MutableTree[Long,B](new Node[Long,B](null), 0)
      }
      case _: Array[Double] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Double]]
        new MutableTree[Double,B](new Node[Double,B](null), 0)
      }
      case _: Array[AnyRef] => new MutableTree[A,B](new Node[A,B](null), 0)
    }).asInstanceOf[MutableTree[A,B]]
  }

  class MutableTree[@specialized A,B](val rootHolder: Node[A,B], var _size: Int)(implicit cmp: MyCmp[A]) {

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

    //////// bulk

    def isEmpty = _size == 0
    def size = _size

    override def clone() = {
      markShared(rootHolder.right)
      new MutableTree(new Node[A,B](rootHolder.right), _size)
    }

    //////// reads

    def contains(k: A): Boolean = {
      var n = rootHolder.right
      while (n != null) {
        val c = cmp.compare(k, n.key)
        if (c == 0)
          return true
        n = if (c < 0) n.left else n.right
      }
      return false
    }

    def get(k: A): Option[B] = {
      var n = rootHolder.right
      while (n != null) {
        val c = cmp.compare(k, n.key)
        if (c == 0)
          return Some(n.value)
        n = if (c < 0) n.left else n.right
      }
      return None
    }

    //////// put

    def put(k: A, v: B): Option[B] = {
      var n = rootHolder
      var c = 1
      while (c != 0) {
        val next = if (c > 0) unsharedRight(n) else unsharedLeft(n)
        if (next == null) {
          val fresh = new Node[A,B](n, k, v)
          if (c > 0) n.right = fresh else n.left = fresh
          if (n.height != 2) repair(n)
          _size += 1
          return None
        }
        n = next
        c = cmp.compare(k, n.key)
      }
      // hit
      val z = n.value
      n.value = v
      return Some(z)
    }

    def update(k: A, v: B) {
      put(k, v)
      //validate()
    }

    //////// remove

    def remove(k: A): Option[B] = {
      var n = rootHolder
      var c = 1
      while (c != 0) {
        val next = if (c > 0) unsharedRight(n) else unsharedLeft(n)
        if (next == null) {
          // miss
          return None
        }
        n = next
        c = cmp.compare(k, n.key)
      }
      // hit
      val z = n.value
      removeNode(n)
      _size -= 1
      return Some(z)
    }

    def removeNode(n: Node[A,B]) {
      if (n.left == null) {
        replaceInParent(n, n.right)
      } else if (n.right == null) {
        replaceInParent(n, n.left)
      } else {
        val s = unsharedSucc(n)
        n.key = s.key
        n.value = s.value
        replaceInParent(s, s.right)
      }
    }

    def unsharedSucc(n: Node[A,B]) = {
      var succ = unsharedRight(n)
      while (succ.left != null)
        succ = unsharedLeft(succ)
      succ
    }

    def replaceInParent(n: Node[A,B], repl: Node[A,B]) {
      if (n.parent.left eq n)
        n.parent.left = repl
      else
        n.parent.right = repl
      if (repl != null && repl.parent != null)
        repl.parent = n.parent
      repair(n.parent)
    }

    def -=(k: A) {
      remove(k)
      //validate()
    }

    //////// sharing machinery

    def unsharedLeft(n: Node[A,B]): Node[A,B] = {
      if (n.left != null && n.left.parent == null)
        n.left = unshare(n.left, n)
      n.left
    }

    def unsharedRight(n: Node[A,B]): Node[A,B] = {
      if (n.right != null && n.right.parent == null)
        n.right = unshare(n.right, n)
      n.right
    }

    def unshare(n: Node[A,B], p: Node[A,B]): Node[A,B] = {
      markShared(n.left)
      markShared(n.right)
      new Node[A,B](p, n.height, n.key, n.value, n.left, n.right)
    }

    def markShared(n: Node[A,B]) {
      if (n != null)
        n.parent = null 
    }


    //////// AVL rebalancing

    def height(n: Node[A,B]) = if (n == null) 0 else n.height

    def balance(n: Node[A,B]) = height(n.left) - height(n.right)

    def repair(n: Node[A,B]) {
      val h0 = n.height

      // rootHolder
      if (h0 < 0) return

      val hL = height(n.left)
      val hR = height(n.right)
      val bal = hL - hR
      if (bal > 1) {
        // Left is too large, rotate right.  If left.right is larger than
        // left.left then rotating right will lead to a -2 balance, so
        // first we have to rotateLeft on left.
        replaceAndMaybeRepair(n, h0, if (balance(n.left) < 0) rotateRightOverLeft(n) else rotateRight(n))
      } else if (bal < -1) {
        replaceAndMaybeRepair(n, h0, if (balance(n.right) > 0) rotateLeftOverRight(n) else rotateLeft(n))
      } else {
        // no rotations needed, just update height
        val h = 1 + math.max(hL, hR)
        if (h != h0) {
          n.height = h
          repair(n.parent)
        }
      }
    }

    def replaceAndMaybeRepair(n0: Node[A,B], h0: Int, n: Node[A,B]) {
      replace(n0, n)
      if (n.height != h0) repair(n.parent)
    }

    def replace(n0: Node[A,B], n: Node[A,B]) {
      val p = n.parent
      if (p.left eq n0) p.left = n else p.right = n
    }

    def rotateRight(b: Node[A,B]): Node[A,B] = {
      val nL = unsharedLeft(b)
      nL.parent = b.parent

      b.left = nL.right
      if (b.left != null && b.left.parent != null)
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
      if (b.right != null && b.right.parent != null)
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
      if (n != null) {
        foreach(n.left, block)
        block((n.key, n.value))
        foreach(n.right, block)
      }
    }

    def elements: Iterator[(A,B)] = new Iterator[(A,B)] {
      private val stack = new Array[Node[A,B]](height(rootHolder.right))
      private var depth = 0

      pushMin(rootHolder.right)

      @tailrec final def pushMin(n: Node[A,B]) {
        if (n != null) {
          stack(depth) = n
          depth += 1
          pushMin(n.left)
        }
      }

      def hasNext = depth > 0

      def next = {
        if (depth == 0) throw new IllegalStateException
        depth -= 1
        val n = stack(depth)
        stack(depth) = null
        pushMin(n.right)
        (n.key, n.value)
      }
    }

    //////// validation

    def validate() {
      assert(rootHolder.height == -1)
      assert(rootHolder.left == null)
      validate(rootHolder.right)
      assert(_size == computeSize(rootHolder.right))
      if (_size >= 2) {
        for (entries <- elements.toSeq.sliding(2)) {
          assert(cmp.compare(entries(0)._1, entries(1)._1) < 0)
        }
      }
      val s = elements.toSeq
      val ss = s.size
      assert(_size == ss)
    }

    def computeSize(n: Node[A,B]): Int = {
      if (n == null) 0 else computeSize(n.left) + 1 + computeSize(n.right)
    }

    def validate(n: Node[A,B]) {
      if (n != null) {
        assert(n.left == null || (n.left.parent eq n))
        assert(n.right == null || (n.right.parent eq n))
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

  def Range = 100
  def InitialGetPct = 50
  def GetPct = 30 // 70 //95
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
    val (bbest,bavg) = testUnifiedAVL2(rand, keyGen)
    val bc = cmpCount
    cmpCount = 0
    val (cbest,cavg) = testJavaTree(rand, keyGen)
    val cc = cmpCount
    println(name + ": FatLeaf4: " + abest + " nanos/op (" + aavg + " avg),  " +
            name + ": UnifiedAVL2: " + bbest + " nanos/op (" + bavg + " avg),  " +
            "java.util.TreeMap: " + cbest + " nanos/op (" + cavg + " avg)")
    if (ac > 0)
      println("  FatLeaf4: " + ac + " compares,  UnifiedAVL2: " + bc +
              " compares,  java.util.TreeMap: " + cc + " compares")
  }

  def testUnifiedAVL2[@specialized A](rand: scala.util.Random, keyGen: () => A)(
          implicit cmp: Ordering[A], am: ClassManifest[A]): (Long,Long) = {
    val tt0 = System.currentTimeMillis
    val m = UnifiedAVL2.newTree[A,String]
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