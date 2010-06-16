package mmt

import annotation.tailrec
import java.util.NoSuchElementException

// BTree2

object BTree2NotFound

object BTree2 {
  trait MyCmp[@specialized A] {
    def compare(k1: A, k2: A): Int

    def keySearch(keys: Array[A], numKeys: Int, k: A): Int = {
      var b = 0
      var e = numKeys
      while (b < e) {
        val mid = (b + e) >>> 1
        val c = compare(k, keys(mid))
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

//    def treeContains[B](root: Node[A,B], k: A): Boolean = {
//      var n = root
//      (while (true) {
//        val i = keySearch(n.keys, n.numKeys, k)
//        if (i >= 0) return true
//        if (n.children == null) return false
//        n = n.children(~i)
//      }).asInstanceOf[Nothing]
//    }
  }

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

  import mmt.{BTree2NotFound => NotFound}

  // try 1 for testing
  def MinKeys = 15
  def MaxKeys = 2 * MinKeys + 1

  class Node[@specialized A,B](var generation: Long, // TODO: replace with Int + rollover logic
                               var numKeys: Int,     // TODO: replace with Short
                               var keysShared: Boolean,
                               var valuesShared: Boolean,
                               var keys: Array[A],
                               var values: Array[B],
                               var children: Array[Node[A,B]]) {

    //////// read

    def contains(k: A)(implicit cmp: MyCmp[A]): Boolean = {
      var n = this
      (while (true) {
        val i = cmp.keySearch(n.keys, n.numKeys, k)
        if (i >= 0) return true
        if (n.children == null) return false
        n = n.children(~i)
      }).asInstanceOf[Nothing]
    }

    def get(k: A)(implicit cmp: MyCmp[A]): Option[B] = {
      var n = this
      (while (true) {
        val i = cmp.keySearch(n.keys, n.numKeys, k)
        if (i >= 0) return Some(values(i))
        if (n.children == null) return None
        n = n.children(~i)
      }).asInstanceOf[Nothing]
    }

    //////// sharing machinery

    def unsharedKeys = {
      if (keysShared) {
        keys = keys.clone()
        keysShared = false
      }
      keys
    }

    def unsharedValues = {
      if (valuesShared) {
        values = values.clone()
        valuesShared = false
      }
      values
    }

    def copy(gen: Long) = {
      keysShared = true
      valuesShared = true
      new Node[A,B](gen, numKeys, true, true, keys, values, if (children == null) null else children.clone())
    }

    def copyForClone() = {
      // original and copy use the same _new_ generation, so all of the shared
      // nodes are now frozen
      generation += 1
      copy(generation)
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

    //////// update and insert

    def put(k: A, v: B)(implicit cmp: MyCmp[A]): AnyRef = {
      var n = this
      var b = 0
      var e = numKeys
      (while (true) {
        if (b < e) {
          // keep binary searching in this node
          val mid = (b + e) >>> 1
          val c = cmp.compare(k, n.keys(mid))
          if (c < 0) {
            e = mid
          } else if (c > 0) {
            b = mid + 1
          } else {
            // hit, update
            val z = n.values(mid)
            n.unsharedValues(mid) = v
            return z.asInstanceOf[AnyRef]
          }
        } else if (n.children == null) {
          // this is a leaf, insert here
          n.insertEntry(b, k, v)
          return NotFound
        } else {
          // not found in this node, move down
          val ch = n.unsharedChild(b)
          if (ch.numKeys == MaxKeys) {
            // Split the child first.  We then need to decide whether to go to
            // the left or the right of the resulting split, or possibly stay at
            // this node (because one key moves to this level during the split).
            n.splitChild(k, b)
            e = b + 1
          } else {
            // just move down
            n = ch
            b = 0
            e = n.numKeys
          }
        }
      }).asInstanceOf[Nothing]
    }

    def splitChild(dummy: A, i: Int) {
      val lhs = children(i)
      assert(lhs.numKeys == MaxKeys && lhs.generation == generation)

      val leftN = MaxKeys / 2
      val rightN = MaxKeys - 1 - leftN
      // the other key goes into this node

      val kk = lhs.unsharedKeys
      val vv = lhs.unsharedValues
      
      // Create the new child.  We create the new arrays using clone() so that
      // they get the right type without needing a ClassManifest here.  We'll
      // create the child array later if necessary.
      val rhs = new Node[A,B](generation, rightN, false, false, kk.clone(), vv.clone(), null)

      // fix up this node
      insertEntry(i, kk(leftN), vv(leftN), rhs)

      // copy the values to the rhs, then clear out the empty portions
      // TODO: is it faster to copy from rhs.keys?
      System.arraycopy(kk, leftN + 1, rhs.keys, 0, rightN)
      System.arraycopy(vv, leftN + 1, rhs.values, 0, rightN)
      clear(kk, leftN, rightN + 1)
      clear(vv, leftN, rightN + 1)
      clear(rhs.keys, rightN, MaxKeys - rightN)
      clear(rhs.values, rightN, MaxKeys - rightN)

      // fix up the children if this is not a leaf
      if (lhs.children != null) {
        rhs.children = new Array[Node[A,B]](MaxKeys + 1)
        System.arraycopy(lhs.children, leftN + 1, rhs.children, 0, rightN + 1)
        clear(lhs.children, leftN + 1, rightN + 1)
      }
      lhs.numKeys = leftN
    }

    def insertEntry(i: Int, k: A, v: B, ch: Node[A,B]) {
      assert(ch.generation == generation)
      System.arraycopy(children, i + 1, children, i + 2, numKeys - i)
      children(i + 1) = ch
      insertEntry(i, k, v)
    }

    def insertEntry(i: Int, k: A, v: B) {
      val kk = unsharedKeys
      val vv = unsharedValues
      System.arraycopy(kk, i, kk, i + 1, numKeys - i)
      System.arraycopy(vv, i, vv, i + 1, numKeys - i)
      kk(i) = k
      vv(i) = v
      numKeys += 1
    }

    @inline def clear[T](a: Array[T], pos: Int, len: Int) {
      var i = 0
      while (i < len) { a(pos + i) = null.asInstanceOf[T] ; i += 1 }
    }

    //////// removal

    def remove(k: A)(implicit cmp: MyCmp[A]): AnyRef = {
      // Pre-splitting during put is not too hard, but we can't pre-join.  This
      // means that put is tail recursive, but not remove.
      val i = cmp.keySearch(keys, numKeys, k)
      if (i >= 0) {
        // hit
        val z = values(i)
        if (children == null)
          leafRemove(k, i)
        else
          branchRemove(k, i)
        z.asInstanceOf[AnyRef]
      } else if (children == null) {
        // miss
        NotFound
      } else {
        // recurse
        val z = unsharedChild(~i).remove(k)
        if (z ne NotFound) checkJoin(k, ~i)
        z
      }
    }

    def branchRemove(dummy: A, i: Int) {
      unsharedChild(i).removeMax(dummy, this, i)
      checkJoin(dummy, i)
    }

    def removeMax(dummy: A, target: Node[A,B], targetI: Int) {
      if (children == null) {
        target.unsharedKeys(targetI) = keys(numKeys - 1)
        target.unsharedValues(targetI) = values(numKeys - 1)
        leafTrimMax(dummy)
      } else {
        unsharedChild(numKeys).removeMax(dummy, target, targetI)
        checkJoin(dummy, numKeys)
      }
    }

    def leafRemove(dummy: A, i: Int) {
      val kk = unsharedKeys
      val vv = unsharedValues
      System.arraycopy(kk, i + 1, kk, i, numKeys - i - 1)
      System.arraycopy(vv, i + 1, vv, i, numKeys - i - 1)
      leafTrimMax(dummy)
    }

    def leafTrimMax(dummy: A) {
      unsharedKeys(numKeys - 1) = null.asInstanceOf[A]
      unsharedValues(numKeys - 1) = null.asInstanceOf[B]
      numKeys -= 1
    }

    def checkJoin(dummy: A, i: Int) {
      if (children(i).numKeys < MinKeys && numKeys > 0)
        refillChild(dummy, i)
    }

    def refillChild(dummy: A, i: Int) {
      // we either need to steal an entry, or merge with a sibling
      if (i > 0) {
        // possible merge or steal with left sibling
        if (children(i - 1).numKeys == MinKeys)
          joinChildren(dummy, i - 1)
        else
          shuffleRight(dummy, i - 1)
      } else {
        // consider only right sibling
        if (children(i + 1).numKeys == MinKeys)
          joinChildren(dummy, i)
        else
          shuffleLeft(dummy, i)
      }
    }

    def joinChildren(dummy: A, i: Int) {
      val lhs = unsharedChild(i)
      val rhs = children(i + 1)
      assert(lhs.numKeys + 1 + rhs.numKeys <= MaxKeys)

      // merge the children into lhs
      lhs.unsharedKeys(lhs.numKeys) = keys(i)
      lhs.unsharedValues(lhs.numKeys) = values(i)
      System.arraycopy(rhs.keys, 0, lhs.keys, lhs.numKeys + 1, rhs.numKeys)
      System.arraycopy(rhs.values, 0, lhs.values, lhs.numKeys + 1, rhs.numKeys)
      if (lhs.children != null)
        System.arraycopy(rhs.children, 0, lhs.children, lhs.numKeys + 1, rhs.numKeys + 1)
      lhs.numKeys += 1 + rhs.numKeys

      // splice out rhs
      val kk = unsharedKeys
      val vv = unsharedValues
      System.arraycopy(kk, i + 1, kk, i, numKeys - i - 1)
      System.arraycopy(vv, i + 1, vv, i, numKeys - i - 1)
      System.arraycopy(children, i + 2, children, i + 1, numKeys - i - 1)
      trimMax(dummy)
    }

    def trimMax(dummy: A) {
      if (children != null)
        children(numKeys) = null
      leafTrimMax(dummy)
    }

    // moves one entry from leftI+1 to leftI
    def shuffleLeft(dummy: A, leftI: Int) {
      val lhs = unsharedChild(leftI)
      val rhs = unsharedChild(leftI + 1)

      // append onto lhs
      if (lhs.children != null)
        lhs.insertEntry(lhs.numKeys, keys(leftI), values(leftI), rhs.children(0))
      else
        lhs.insertEntry(lhs.numKeys, keys(leftI), values(leftI))

      // adjust splitting entry
      unsharedKeys(leftI) = rhs.keys(0)
      unsharedValues(leftI) = rhs.values(0)

      // remove from rhs
      if (rhs.children != null) {
        System.arraycopy(rhs.children, 1, rhs.children, 0, rhs.numKeys + 1)
        rhs.children(rhs.numKeys) = null
      }
      rhs.leafRemove(dummy, 0)
    }

    // moves one entry from leftI to leftI+1
    def shuffleRight(dummy: A, leftI: Int) {
      val lhs = unsharedChild(leftI)
      val rhs = unsharedChild(leftI + 1)

      // insert into rhs
      if (lhs.children != null)
        rhs.insertEntry(0, keys(leftI), values(leftI), lhs.children(lhs.numKeys))
      else
        rhs.insertEntry(0, keys(leftI), values(leftI))

      // adjust splitting entry
      unsharedKeys(leftI) = lhs.keys(lhs.numKeys - 1)
      unsharedValues(leftI) = lhs.values(lhs.numKeys - 1)

      // trim lhs
      lhs.trimMax(dummy)
    }

    def visit(v: ((A,B)) => Unit) {
      var i = 0
      while (i < numKeys) {
        if (children != null) children(i).visit(v)
        v((keys(i), values(i)))
        i += 1
      }
      if (children != null) children(i).visit(v)
    }

    def validate(isRoot: Boolean, nullKey: A, nullValue: B): Int = {
      assert(numKeys >= MinKeys || isRoot)
      assert(numKeys >= 1 || (isRoot && children == null))
      assert(numKeys <= MaxKeys)
      for (i <- numKeys until MaxKeys) {
        assert(keys(i) == nullKey)
        assert(values(i) == nullValue)
      }
      if (children != null) {
        val h = children(0).validate(false, nullKey, nullValue)
        for (i <- 1 to numKeys) {
          val h2 = children(i).validate(false, nullKey, nullValue)
          assert(h == h2)
        }
        for (i <- numKeys + 1 to MaxKeys)
          assert(children(i) == null)
        return h + 1
      } else {
        return 1
      }
    }
  }

  def newEmptyRoot[@specialized A,B](gen: Long)(implicit am: ClassManifest[A], bm: ClassManifest[B]) =
      new Node[A,B](gen, 0, false, false, new Array[A](MaxKeys), new Array[B](MaxKeys), null)

  def newTree[@specialized A,B](implicit cmp: Ordering[A], am: ClassManifest[A], bm: ClassManifest[B]): MutableTree[A,B] = {
    (am.newArray(0).asInstanceOf[AnyRef] match {
      case _: Array[Unit] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Unit]]
        new MutableTree[Unit,B](newEmptyRoot[Unit,B](0L), 0)
      }
      case _: Array[Boolean] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Boolean]]
        new MutableTree[Boolean,B](newEmptyRoot[Boolean,B](0L), 0)
      }
      case _: Array[Byte] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Byte]]
        new MutableTree[Byte,B](newEmptyRoot[Byte,B](0L), 0)
      }
      case _: Array[Short] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Short]]
        new MutableTree[Short,B](newEmptyRoot[Short,B](0L), 0)
      }
      case _: Array[Char] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Char]]
        new MutableTree[Char,B](newEmptyRoot[Char,B](0L), 0)
      }
      case _: Array[Int] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Int]]
        new MutableTree[Int,B](newEmptyRoot[Int,B](0L), 0)
      }
      case _: Array[Float] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Float]]
        new MutableTree[Float,B](newEmptyRoot[Float,B](0L), 0)
      }
      case _: Array[Long] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Long]]
        new MutableTree[Long,B](newEmptyRoot[Long,B](0L), 0)
      }
      case _: Array[Double] => {
        implicit val cmp0 = cmp.asInstanceOf[Ordering[Double]]
        new MutableTree[Double,B](newEmptyRoot[Double,B](0L), 0)
      }
      case _: Array[AnyRef] => new MutableTree[A,B](newEmptyRoot[A,B](0L), 0)
    }).asInstanceOf[MutableTree[A,B]]
  }

  class MutableTree[@specialized A,B](var root: BTree2.Node[A,B], var _size: Int)(
          implicit cmp: MyCmp[A], am: ClassManifest[A], bm: ClassManifest[B]) {
    
    def isEmpty = _size == 0
    def size = _size

    def contains(k: A): Boolean = root.contains(k)
    //def contains(k: A): Boolean = cmp.treeContains(root, k)

    def get(k: A): Option[B] = root.get(k)

    def foreach(block: ((A,B)) => Unit) { root.visit(block) }

    def elements: Iterator[(A,B)] = new Iterator[(A,B)] {
      private val nodeStack = new Array[Node[A,B]](32) // TODO: compute a tighter bound
      private val posStack = new Array[Int](32)
      private var depth = 0
      if (root.numKeys != 0) pushMin(root)

      @tailrec private def pushMin(node: Node[A,B]) {
        nodeStack(depth) = node
        posStack(depth) = 0
        depth += 1
        if (node.children != null)
          pushMin(node.children(0))
      }

      private def advance() {
        if (depth > 0) {
          val n = nodeStack(depth - 1)
          val p = posStack(depth - 1)
          if (p + 1 >= n.numKeys) {
            // no more keys for this node, visit the right-most child and then
            // be done with it
            depth -= 1
            if (n.children != null)
              pushMin(n.children(p + 1))
            else
              nodeStack(depth) = null
          } else {
            // just advance to the next key here, but first visit the child
            // between the last key and the next
            posStack(depth - 1) = p + 1
            if (n.children != null)
              pushMin(n.children(p + 1))
          }
        }
      }

      def hasNext = depth > 0

      def next = {
        if (!hasNext) throw new NoSuchElementException
        val n = nodeStack(depth - 1)
        val p = posStack(depth - 1)
        val z = (n.keys(p), n.values(p))
        advance()
        z
      }
    }

    def validate()(implicit am: ClassManifest[A], bm: ClassManifest[B]) {
      root.validate(true, am.newArray(1)(0), bm.newArray(1)(0))
      var s = 0
      root visit { _ => s += 1 }
      assert(_size == s)
      if (_size >= 2) {
        val ss = elements.toSeq
        for (entries <- ss.sliding(2)) {
          assert(cmp.compare(entries(0)._1, entries(1)._1) < 0)
        }
      }
      assert(_size == elements.toSeq.size)
    }

    override def clone() = new MutableTree[A,B](root.copyForClone(), _size)

    def put(k: A, v: B): Option[B] = {
      val z = putImpl(k, v)
      if (z eq NotFound) None else Some(z.asInstanceOf[B])
    }

    def update(k: A, v: B) { putImpl(k, v) }

    def putImpl(k: A, v: B): AnyRef = {
      val z = root.put(k, v)
      if (root.numKeys == MaxKeys)
        splitRoot(k)
      if (z eq NotFound)
        _size += 1
      //validate()
      z
    }

    def splitRoot(dummy: A) {
      pushDownRoot(dummy)
      root.splitChild(dummy, 0)
    }

    def pushDownRoot(dummy: A) {
      val r = newEmptyRoot[A,B](root.generation)
      r.children = new Array[Node[A,B]](MaxKeys + 1)
      r.children(0) = root
      root = r
    }

    def remove(k: A): Option[B] = {
      val z = removeImpl(k)
      if (z eq NotFound) None else Some(z.asInstanceOf[B])
    }

    def -=(k: A) { removeImpl(k) }

    def removeImpl(k: A): AnyRef = {
      val z = root.remove(k)
      if (root.numKeys == 0 && root.children != null)
        root = root.unsharedChild(0)
      if (z ne NotFound)
        _size -= 1
      //validate()
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
    val rands = Array.tabulate(6) { _ => new scala.util.Random(0) }
    for (pass <- 0 until 1) {
      testInt(rands(0))
    }
    println("------------- adding short")
    for (pass <- 0 until 1) {
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

  def Range = 200
  def InitialGetPct = 30
  def GetPct = 95
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

  def test[@specialized A](name: String, rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A], am: ClassManifest[A]) {
    cmpCount = 0
    val (abest,aavg) = testBTree2(rand, keyGen)
    val ac = cmpCount
    //println("!!")
    cmpCount = 0
    val (bbest,bavg) = testFatLeaf4(rand, keyGen)
    val bc = cmpCount
    cmpCount = 0
    val (cbest,cavg) = testJavaTree(rand, keyGen)
    val cc = cmpCount
    println(name + ": BTree2: " + abest + " nanos/op (" + aavg + " avg),  " +
            name + ": FatLeaf4: " + bbest + " nanos/op (" + bavg + " avg),  " +
            "java.util.TreeMap: " + cbest + " nanos/op (" + cavg + " avg)")
    if (ac > 0)
      println("  BTree2: " + ac + " compares,  FatLeaf4: " + bc + " compares,  java.util.TreeMap: " + cc + " compares")
  }

  def testBTree2[@specialized A](rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A], am: ClassManifest[A]): (Long,Long) = {
    val tt0 = System.currentTimeMillis
    val m = newTree[A,String]
    var best = Long.MaxValue
    for (group <- 1 until 10000) {
      val gp = if (group < 1000) InitialGetPct else GetPct
      var i = 1000
      val t0 = System.nanoTime
      var matching = 0
      while (i > 0) {
        matching += testBTree2One(rand, keyGen, gp, m)
        matching += testBTree2One(rand, keyGen, gp, m)
        matching += testBTree2One(rand, keyGen, gp, m)
        matching += testBTree2One(rand, keyGen, gp, m)
        i -= 4
      }
      if (matching < 0) println("unlikely")
      val elapsed = System.nanoTime - t0
      if (group >= 1000) best = best min elapsed
    }
    val total = System.currentTimeMillis - tt0
    (best / 1000, total / 10)
  }

  def testBTree2One[@specialized A](rand: scala.util.Random, keyGen: () => A, gp: Double, m: BTree2.MutableTree[A,String]) = {
    var matching = 0
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
    matching
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
        matching += testFatLeaf4One(rand, keyGen, gp, m)
        matching += testFatLeaf4One(rand, keyGen, gp, m)
        matching += testFatLeaf4One(rand, keyGen, gp, m)
        matching += testFatLeaf4One(rand, keyGen, gp, m)
        i -= 4
      }
      if (matching < 0) println("unlikely")
      val elapsed = System.nanoTime - t0
      if (group >= 1000) best = best min elapsed
    }
    val total = System.currentTimeMillis - tt0
    (best / 1000, total / 10)
  }

  def testFatLeaf4One[@specialized A](rand: scala.util.Random, keyGen: () => A, gp: Double, m: FatLeaf4.MutableTree[A,String]) = {
    var matching = 0
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
    matching
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
        matching += testJavaTreeOne(rand, keyGen, gp, m)
        matching += testJavaTreeOne(rand, keyGen, gp, m)
        matching += testJavaTreeOne(rand, keyGen, gp, m)
        matching += testJavaTreeOne(rand, keyGen, gp, m)
        i -= 4
      }
      if (matching < 0) println("unlikely")
      val elapsed = System.nanoTime - t0
      if (group >= 1000) best = best min elapsed
    }
    val total = System.currentTimeMillis - tt0
    (best / 1000, total / 10)
  }

  def testJavaTreeOne[@specialized A](rand: scala.util.Random, keyGen: () => A, gp: Double, m: java.util.TreeMap[A,String]) = {
    var matching = 0
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
    matching
  }
}