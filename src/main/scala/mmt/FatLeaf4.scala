package mmt

import annotation.tailrec

// FatLeaf4

object FatLeaf4 {

  def LeafMin = 8
  def LeafMax = 2 * LeafMin + 1

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
                               var _size: Int,
                               var keys: Array[A],
                               var values: Array[B]) extends Node[A,B](par0) {
    def this(par0: Branch[A,B], size0: Int)(implicit am: ClassManifest[A], bm: ClassManifest[B]) =
        this(par0, size0, new Array[A](LeafMax), new Array[B](LeafMax))

    def size = _size
    def size_=(v: Int) { assert(v >= LeafMin - 1 || parent.height < 0) ; _size = v }
  }

  def newEmptyRootHolder[@specialized A,B](implicit am: ClassManifest[A], bm: ClassManifest[B]) = {
    val h = new Branch[A,B](null)
    h.right = new Leaf[A,B](h, 0)
    h
  }

  def newTree[@specialized A,B](implicit cmp: Ordering[A], am: ClassManifest[A], bm: ClassManifest[B]): MutableTree[A,B] = {
    (am.newArray(0).asInstanceOf[AnyRef] match {
      case _: Array[Unit] =>    new MutableTree[Unit,B](newEmptyRootHolder[Unit,B], 0)
      case _: Array[Boolean] => new MutableTree[Boolean,B](newEmptyRootHolder[Boolean,B], 0)
      case _: Array[Byte] =>    new MutableTree[Byte,B](newEmptyRootHolder[Byte,B], 0)
      case _: Array[Short] =>   new MutableTree[Short,B](newEmptyRootHolder[Short,B], 0)
      case _: Array[Char] =>    new MutableTree[Char,B](newEmptyRootHolder[Char,B], 0)
      case _: Array[Int] =>     new MutableTree[Int,B](newEmptyRootHolder[Int,B], 0)
      case _: Array[Float] =>   new MutableTree[Float,B](newEmptyRootHolder[Float,B], 0)
      case _: Array[Long] =>    new MutableTree[Long,B](newEmptyRootHolder[Long,B], 0)
      case _: Array[Double] =>  new MutableTree[Double,B](newEmptyRootHolder[Double,B], 0)
      case _: Array[AnyRef] =>  new MutableTree[A,B](newEmptyRootHolder[A,B], 0)
    }).asInstanceOf[MutableTree[A,B]]
  }

  class MutableTree[@specialized A,B](val rootHolder: Branch[A,B], var _size: Int)(
          implicit cmp: Ordering[A], am: ClassManifest[A], bm: ClassManifest[B]) {

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
      new MutableTree(new Branch[A,B](rootHolder.right), _size)
    }

    //////// reads

    def contains(k: A): Boolean = {
      var n = rootHolder.right
      (while (true) {
        n match {
          case b: Branch[A,B] => {
            val c = cmp.compare(k, b.key)
            if (c == 0)
              return true
            n = if (c < 0) b.left else b.right
          }
          case t: Leaf[A,B] => {
            return keySearch(t, k) >= 0
          }
        }
      }).asInstanceOf[Nothing]
    }

    def get(k: A): Option[B] = {
      var n = rootHolder.right
      (while (true) {
        n match {
          case b: Branch[A,B] => {
            val c = cmp.compare(k, b.key)
            if (c == 0)
              return Some(b.value)
            n = if (c < 0) b.left else b.right
          }
          case t: Leaf[A,B] => {
            val i = keySearch(t, k)
            return if (i >= 0) Some(t.values(i)) else None
          }
        }
      }).asInstanceOf[Nothing]
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

    def put(k: A, v: B): Option[B] = {
      var n = unsharedRight(rootHolder)
      (while (true) {
        n match {
          case b: Branch[A,B] => {
            val c = cmp.compare(k, b.key)
            if (c == 0) {
              // update
              val z = b.value
              b.value = v
              return Some(z)
            } else {
              n = if (c < 0) unsharedLeft(b) else unsharedRight(b)
            }
          }
          case t: Leaf[A,B] => {
            val i = keySearch(t, k)
            if (i >= 0) {
              val z = t.values(i)
              t.values(i) = v
              return Some(z)
            } else {
              insert(t, ~i, k, v)
              _size += 1
              return None
            }
          }
        }
      }).asInstanceOf[Nothing]
    }

    def update(k: A, v: B) {
      put(k, v)
      // validate()
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
      replaceAndRepair(tL, b)
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

    def remove(k: A): Option[B] = {
      var n = unsharedRight(rootHolder)
      (while (true) {
        n match {
          case b: Branch[A,B] => {
            val c = cmp.compare(k, b.key)
            if (c == 0) {
              val z = b.value
              removeMax(b, unsharedLeft(b))
              _size -= 1
              return Some(z)
            } else {
              n = if (c < 0) unsharedLeft(b) else unsharedRight(b)
            }
          }
          case t: Leaf[A,B] => {
            val i = keySearch(t, k)
            if (i >= 0) {
              val z = t.values(i)
              removeFromLeaf(t, i)
              _size -= 1
              return Some(z)
            } else {
              return None
            }
          }
        }
      }).asInstanceOf[Nothing]
    }

    def -=(k: A) {
      remove(k)
      //validate()
    }

    @tailrec private def removeMax(target: Branch[A,B], n: Node[A,B]): Unit = n match {
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
        val p = t.parent
        if (p.left eq t) {
          replace(p, rotateLeft(p))
          refillAsLeft(t)
        } else {
          replace(p, rotateRight(p))
          refillAsRight(t)
        }
      }
    }

    def refillAsLeft(tL: Leaf[A,B]) {
      assert(tL.size == LeafMin - 1)
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
      assert(tR.size == LeafMin - 1)
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

    def replaceAndMaybeRepair(n0: Node[A,B], h0: Int, n: Branch[A,B]) {
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

    //////// enumeration

    def foreach(block: ((A,B)) => Unit) { foreach(rootHolder.right, block) }

    def foreach(n: Node[A,B], block: ((A,B)) => Unit): Unit = n match {
      case b: Branch[A,B] => {
        foreach(b.left, block)
        block((b.key, b.value))
        foreach(b.right, block)
      }
      case t: Leaf[A,B] => {
        var i = 0
        while (i < t.size) { block((t.keys(i), t.values(i))) ; i += 1 }
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
        n match {
          case b: Branch[A,B] => pushMin(b.left)
          case _ => {}
        }
      }

      private def advance(): Unit = stack(depth - 1) match {
        case b: Branch[A,B] => {
          // pop current node
          depth -= 1
          pushMin(b.right)
        }
        case t: Leaf[A,B] => {
          if (index + 1 < t.size) {
            // more entries in this node
            index += 1
          } else {
            index = 0
            // no children, so just pop
            depth -= 1
            stack(depth) = null
          }
        }
      }

      def hasNext = depth > 0

      def next = {
        if (depth == 0) throw new IllegalStateException
        val z = stack(depth - 1) match {
          case b: Branch[A,B] => (b.key, b.value)
          case t: Leaf[A,B] => (t.keys(index), t.values(index))
        }
        advance()
        z
      }
    }

    //////// validation

    def validate() {
      val root = rootHolder.right
      if (_size == 0) {
        assert(root.isInstanceOf[Leaf[_,_]] && root.asInstanceOf[Leaf[_,_]].size == 0)
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

    def computeSize(n: Node[A,B]): Int = n match {
      case b: Branch[A,B] => computeSize(b.left) + 1 + computeSize(b.right)
      case t: Leaf[A,B] => t.size
    }

    def validate(n: Node[A,B]): Unit = n match {
      case b: Branch[A,B] if b.height < 0 => {
        // rootHolder
        assert(b.left == null && b.right != null)
        validate(b.right)
      }
      case b: Branch[A,B] => {
        assert(b.left != null && (b.left.parent eq b))
        assert(b.right != null && (b.right.parent eq b))
        assert(b.height == 1 + math.max(height(b.left), height(b.right)))
        assert(math.abs(balance(b)) <= 1)
        validate(b.left)
        validate(b.right)
      }
      case t: Leaf[A,B] => {
        assert(t.size >= LeafMin || t.parent.height < 0)
        assert(t.size < LeafMax)
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

  def Range = 10000
  def InitialGetPct = 50
  def GetPct = 70 // 70 //95
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

  def test[A](name: String, rand: scala.util.Random, keyGen: () => A)(
          implicit cmp: Ordering[A], am: ClassManifest[A]) {
    cmpCount = 0
    val (abest,aavg) = testFatLeaf(rand, keyGen)
    val ac = cmpCount
    //println("!!")
    cmpCount = 0
    val (bbest,bavg) = testFatLeaf4(rand, keyGen)
    val bc = cmpCount
    cmpCount = 0
    val (cbest,cavg) = testJavaTree(rand, keyGen)
    val cc = cmpCount
    println(name + ": FatLeaf: " + abest + " nanos/op (" + aavg + " avg),  " +
            name + ": FatLeaf4: " + bbest + " nanos/op (" + bavg + " avg),  " +
            "java.util.TreeMap: " + cbest + " nanos/op (" + cavg + " avg)")
    if (ac > 0)
      println("  FatLeaf: " + ac + " compares,  FatLeaf4: " + bc +
              " compares,  java.util.TreeMap: " + cc + " compares")
  }

  def testFatLeaf4[A](rand: scala.util.Random, keyGen: () => A)(
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

  def testFatLeaf[A](rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A]): (Long,Long) = {
    val tt0 = System.currentTimeMillis
    val m = new FatLeaf.MutableTree[A,String]
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

  def testJavaTree[A](rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A]): (Long,Long) = {
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