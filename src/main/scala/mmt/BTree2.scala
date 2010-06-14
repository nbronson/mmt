package mmt

import annotation.tailrec
import java.util.NoSuchElementException

// BTree2

object BTree2 {
  // try 1 for testing
  def MinKeys = 8
  def MaxKeys = 2 * MinKeys + 1

  final class Node[A,B](var generation: Long, // TODO: replace with Int + rollover logic
                        var numKeys: Int,     // TODO: replace with Short
                        var keysShared: Boolean,
                        var valuesShared: Boolean,
                        var keys: Array[A],
                        var values: Array[B],
                        var children: Array[Node[A,B]]) {

    //////// read

    def keySearch(k: A)(implicit cmp: Ordering[A]): Int = {
      var b = 0
      var e = numKeys
      while (b < e) {
        val mid = (b + e) >>> 1
        val c = cmp.compare(k, keys(mid))
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

    @tailrec def contains(k: A)(implicit cmp: Ordering[A]): Boolean = {
      val i = keySearch(k)
      i >= 0 || (children != null && children(~i).contains(k))
    }

    @tailrec def get(k: A)(implicit cmp: Ordering[A]): Option[B] = {
      val i = keySearch(k)
      if (i >= 0)
        Some(values(i))
      else if (children == null)
        None
      else
        children(~i).get(k)
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

    def put(k: A, v: B)(implicit cmp: Ordering[A]): Option[B] = put(0, numKeys, k, v)

    @tailrec def put(b: Int, e: Int, k: A, v: B)(implicit cmp: Ordering[A]): Option[B] = {
      if (b < e) {
        // keep binary searching in this node
        val mid = (b + e) >>> 1
        val c = cmp.compare(k, keys(mid))
        if (c < 0) {
          put(b, mid, k, v)
        } else if (c > 0) {
          put(mid + 1, e, k, v)
        } else {
          // hit, update
          val z = values(mid)
          unsharedValues(mid) = v
          Some(z)
        }
      } else if (children == null) {
        // this is a leaf, insert here
        insertEntry(b, k, v)
        None
      } else {
        // not found in this node, move down
        val ch = unsharedChild(b)
        if (ch.numKeys == MaxKeys) {
          // Split the child first.  We then need to decide whether to go to
          // the left or the right of the resulting split, or possibly stay at
          // this node (because one key moves to this level during the split).
          splitChild(b)
          put(b, b + 1, k, v)
        } else {
          // just move down
          ch.put(0, ch.numKeys, k, v)
        }
      }
    }

    def splitChild(i: Int) {
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

    def remove(k: A)(implicit cmp: Ordering[A]): Option[B] = {
      // Pre-splitting during put is not too hard, but we can't pre-join.  This
      // means that put is tail recursive, but not remove.
      val i = keySearch(k)
      if (i >= 0) {
        // hit
        val z = values(i)
        if (children == null)
          leafRemove(i)
        else
          branchRemove(i)
        Some(z)
      } else if (children == null) {
        // miss
        None
      } else {
        // recurse
        val z = unsharedChild(~i).remove(k)
        checkJoin(~i)
        z
      }
    }

    def branchRemove(i: Int) {
      unsharedChild(i).removeMax(this, i)
      checkJoin(i)
    }

    def removeMax(target: Node[A,B], targetI: Int) {
      if (children == null) {
        target.unsharedKeys(targetI) = keys(numKeys - 1)
        target.unsharedValues(targetI) = values(numKeys - 1)
        leafTrimMax()
      } else {
        unsharedChild(numKeys).removeMax(target, targetI)
        checkJoin(numKeys)
      }
    }

    def leafRemove(i: Int) {
      val kk = unsharedKeys
      val vv = unsharedValues
      System.arraycopy(kk, i + 1, kk, i, numKeys - i - 1)
      System.arraycopy(vv, i + 1, vv, i, numKeys - i - 1)
      leafTrimMax()
    }

    def leafTrimMax() {
      unsharedKeys(numKeys - 1) = null.asInstanceOf[A]
      unsharedValues(numKeys - 1) = null.asInstanceOf[B]
      numKeys -= 1
    }

    def checkJoin(i: Int) {
      if (children(i).numKeys < MinKeys && numKeys > 0)
        refillChild(i)
    }

    def refillChild(i: Int) {
      // we either need to steal an entry, or merge with a sibling
      if (i > 0) {
        // possible merge or steal with left sibling
        if (children(i - 1).numKeys == MinKeys)
          joinChildren(i - 1)
        else
          shuffleRight(i - 1)
      } else {
        // consider only right sibling
        if (children(i + 1).numKeys == MinKeys)
          joinChildren(i)
        else
          shuffleLeft(i)
      }
    }

    def joinChildren(i: Int) {
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
      trimMax()
    }

    def trimMax() {
      if (children != null)
        children(numKeys) = null
      leafTrimMax()
    }

    // moves one entry from leftI+1 to leftI
    def shuffleLeft(leftI: Int) {
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
      rhs.leafRemove(0)
    }

    // moves one entry from leftI to leftI+1
    def shuffleRight(leftI: Int) {
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
      lhs.trimMax()
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

  def newEmptyRoot[A,B](gen: Long)(implicit am: ClassManifest[A], bm: ClassManifest[B]) =
      new Node[A,B](gen, 0, false, false, new Array[A](MaxKeys), new Array[B](MaxKeys), null)

  abstract class Base[A,B](var root: BTree2.Node[A,B], var _size: Int)(implicit cmp: Ordering[A]) {

    def isEmpty = _size == 0
    def size = _size

    def contains(k: A): Boolean = root.contains(k)

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
  }

  class MutableTree[A,B](root0: BTree2.Node[A,B], size0: Int)(
          implicit cmp: Ordering[A], am: ClassManifest[A], bm: ClassManifest[B]) extends Base[A,B](root0, size0) {
    def this()(implicit cmp: Ordering[A], am: ClassManifest[A], bm: ClassManifest[B]) =
        this(newEmptyRoot[A,B](0L), 0)

    override def clone() = new MutableTree[A,B](root.copyForClone(), _size)

    def -=(k: A) { remove(k) }
    def update(k: A, v: B) { put(k, v) }

    def put(k: A, v: B): Option[B] = {
      val z = root.put(k, v)
      if (root.numKeys == MaxKeys)
        splitRoot()
      if (z.isEmpty)
        _size += 1
      //validate()
      z
    }

    def splitRoot() {
      pushDownRoot()
      root.splitChild(0)
    }

    def pushDownRoot() {
      val r = newEmptyRoot[A,B](root.generation)
      r.children = new Array[Node[A,B]](MaxKeys + 1)
      r.children(0) = root
      root = r
    }

    def remove(k: A): Option[B] = {
      val z = root.remove(k)
      if (root.numKeys == 0 && root.children != null)
        root = root.unsharedChild(0)
      if (!z.isEmpty)
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
    println("------------- adding long")
    for (pass <- 0 until 10) {
      testInt(rands(3))
      testShort(rands(4))
      testLong(rands(5))
    }
  }

  def Range = 100
  def InitialGetPct = 50
  def GetPct = 100
  def IterPct = 1.0 / Range

  def testInt(rand: scala.util.Random) = {
    test[Int]("  Int", rand, () => rand.nextInt(Range))
  }

  def testShort(rand: scala.util.Random) = {
    test[Short]("Short", rand, () => rand.nextInt(Range).asInstanceOf[Short])
  }

  def testLong(rand: scala.util.Random) = {
    test[Long](" Long", rand, () => rand.nextInt(Range).asInstanceOf[Long])
  }

  def test[A](name: String, rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A], am: ClassManifest[A]) {
    cmpCount = 0
    val (abest,aavg) = testBTree2(rand, keyGen)
    val ac = cmpCount
    //println("!!")
    cmpCount = 0
    val (bbest,bavg) = testFatLeaf(rand, keyGen)
    val bc = cmpCount
    cmpCount = 0
    val (cbest,cavg) = testJavaTree(rand, keyGen)
    val cc = cmpCount
    println(name + ": BTree2: " + abest + " nanos/op (" + aavg + " avg),  " +
            name + ": FatLeaf: " + bbest + " nanos/op (" + bavg + " avg),  " +
            "java.util.TreeMap: " + cbest + " nanos/op (" + cavg + " avg)")
    if (ac > 0)
      println("  BTree2: " + ac + " compares,  FatLeaf: " + bc + " compares,  java.util.TreeMap: " + cc + " compares")
  }

  def testBTree2[A](rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A], am: ClassManifest[A]): (Long,Long) = {
    val tt0 = System.currentTimeMillis
    val m = new MutableTree[A,String]
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