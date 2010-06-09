package mmt

import annotation.tailrec
import java.util.NoSuchElementException

// BTree

object BTree {
  // try 3, 2 for testing
  def MaxKeys = 16 // 15
  def MinKeysForPair = MaxKeys - 1

  final class Node[A,B](var generation: Long, // TODO: replace with Int + rollover logic
                        var numKeys: Int,     // TODO: replace with Short
                        var kvShared: Boolean,
                        var keysAndValues: Array[AnyRef],
                        var children: Array[Node[A,B]]) {

    //////// access to keys and values

    def keys(i: Int) = keysAndValues(2*i).asInstanceOf[A]
    def values(i: Int) = keysAndValues(2*i+1).asInstanceOf[B]

    def setKey(i: Int, k: A) { unsharedKeysAndValues()(2*i) = k.asInstanceOf[AnyRef] }
    def setValue(i: Int, v: B) { unsharedKeysAndValues()(2*i+1) = v.asInstanceOf[AnyRef] }

    def unsharedKeysAndValues(): Array[AnyRef] = {
      if (kvShared) {
        keysAndValues = keysAndValues.clone()
        kvShared = false
      }
      keysAndValues
    }

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
      return -(b + 1)
    }

    //////// read

    @tailrec def contains(k: A)(implicit cmp: Ordering[A]): Boolean = {
      val i = keySearch(k)
      i >= 0 || (children != null && children(-(i+1)).contains(k))
    }

    @tailrec def get(k: A)(implicit cmp: Ordering[A]): Option[B] = {
      val i = keySearch(k)
      if (i >= 0)
        Some(values(i))
      else if (children == null)
        None
      else
        children(-(i+1)).get(k)
    }

    //////// sharing machinery

    def copy(gen: Long) = {
      kvShared = true
      new Node[A,B](gen, numKeys, true, keysAndValues, if (children == null) null else children.clone())      
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

    def overfullChild(i: Int) {
      // TODO: optimize
      splitChild(i)
      checkJoin(i) || checkJoin(i + 1)
    }

    def splitChild(i: Int) {
      val lhs = children(i)
      assert(lhs.numKeys == MaxKeys && lhs.generation == generation)

      val leftN = MaxKeys / 2
      val rightN = MaxKeys - 1 - leftN
      // the other key goes into this node

      // create the new child
      val rhs = new Node[A,B](generation, rightN, false, new Array[AnyRef](2 * MaxKeys), null)

      // fix up this node
      insertEntry(i, lhs.keys(leftN), lhs.values(leftN), rhs)

      // copy the values to the rhs and reduce the size of lhs
      System.arraycopy(lhs.keysAndValues, 2 * (leftN + 1), rhs.keysAndValues, 0, 2 * rightN)
      clear(lhs.keysAndValues, 2 * leftN, 2 * (rightN + 1))
      if (lhs.children != null) {
        rhs.children = new Array[Node[A,B]](MaxKeys + 1)
        System.arraycopy(lhs.children, leftN + 1, rhs.children, 0, rightN + 1)
        clear(lhs.children, leftN + 1, rightN + 1)
      }
      lhs.numKeys = leftN
    }

    def insertEntry(i: Int, k: A, v: B, ch: Node[A,B]) {
      System.arraycopy(children, i + 1, children, i + 2, numKeys - i)
      children(i + 1) = ch
      insertEntry(i, k, v)
    }

    def insertEntry(i: Int, k: A, v: B) {
      System.arraycopy(keysAndValues, 2 * i, keysAndValues, 2 * (i + 1), 2 * (numKeys - i))
      setKey(i, k)
      setValue(i, v)
      numKeys += 1
    }

    def clear[T <: AnyRef](a: Array[T], pos: Int, len: Int) {
      var i = 0
      while (i < len) { a(pos + i) = null.asInstanceOf[T] ; i += 1 }
    }

    //////// write

    def put(k: A, v: B)(implicit cmp: Ordering[A]): Option[B] = {
      val i = keySearch(k)
      if (i >= 0) {
        // update
        val z = values(i)
        setValue(i, v)
        Some(z)
      } else if (children == null) {
        // insert here
        insertEntry(-(i + 1), k, v)
        None
      } else {
        // insert in child
        val c = unsharedChild(-(i+1))
        val z = c.put(k, v)
        if (c.numKeys == MaxKeys)
          overfullChild(-(i+1))
        z
      }
    }

    def remove(k: A)(implicit cmp: Ordering[A]): Option[B] = {
      val i = keySearch(k)
      if (i >= 0) {
        // hit
        if (children == null) leafRemove(i) else branchRemove(i)
      } else if (children == null) {
        // miss
        None
      } else {
        val ii = -(i+1)
        val z = unsharedChild(ii).remove(k)
        checkJoin(ii)
        z
      }
    }

    def branchRemove(i: Int): Option[B] = {
      val z = Some(values(i))
      unsharedChild(i).removeMax(this, i)
      checkJoin(i)
      z
    }

    def removeMax(target: Node[A,B], targetI: Int) {
      if (children == null) {
        target.setKey(targetI, keys(numKeys - 1))
        target.setValue(targetI, values(numKeys - 1))
        setKey(numKeys - 1, null.asInstanceOf[A])
        setValue(numKeys - 1, null.asInstanceOf[B])
        numKeys -= 1
      } else {
        unsharedChild(numKeys).removeMax(target, targetI)
        checkJoin(numKeys)
      }
    }

    def leafRemove(i: Int): Option[B] = {
      val z = Some(values(i))
      val kv = unsharedKeysAndValues
      System.arraycopy(kv, 2 * (i + 1), kv, 2 * i, 2 * (numKeys - i - 1))
      kv(2 * (numKeys - 1)) = null
      kv(2 * (numKeys - 1) + 1) = null
      numKeys -= 1
      z
    }

    def checkJoin(i: Int): Boolean = {
      if (i + 1 <= numKeys && children(i).numKeys + children(i + 1).numKeys < MinKeysForPair) {
        joinChildren(i)
        true
      } else if (i > 0 && children(i - 1).numKeys + children(i).numKeys < MinKeysForPair) {
        joinChildren(i - 1)
        true
      } else if (children(i).numKeys == 0) {
        // TODO: optimize
        // neighbors may have Max - 1, so we can't necessarily join (without a subsequent split)
        val ii = math.max(i - 1, 0)
        joinChildren(ii)
        if (children(ii).numKeys == MaxKeys) {
          overfullChild(ii)
          false
        } else {
          true
        }
      } else {
        false
      }
    }

    def joinChildren(i: Int) {
      val lhs = children(i)
      val rhs = children(i + 1)
      assert(lhs.numKeys + 1 + rhs.numKeys <= MaxKeys)

      // merge the children into lhs
      lhs.setKey(lhs.numKeys, keys(i))
      lhs.setValue(lhs.numKeys, values(i))
      System.arraycopy(rhs.keysAndValues, 0, lhs.keysAndValues, 2 * (lhs.numKeys + 1), 2 * rhs.numKeys)
      if (lhs.children != null)
        System.arraycopy(rhs.children, 0, lhs.children, lhs.numKeys + 1, rhs.numKeys + 1)
      lhs.numKeys += 1 + rhs.numKeys

      // splice out rhs
      val kv = unsharedKeysAndValues
      System.arraycopy(kv, 2 * (i + 1), kv, 2 * i, 2 * (numKeys - i - 1))
      System.arraycopy(children, i + 2, children, i + 1, numKeys - i - 1)
      kv(2 * (numKeys - 1)) = null
      kv(2 * (numKeys - 1) + 1) = null
      children(numKeys) = null
      numKeys -= 1
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

    def validate(isRoot: Boolean) {
      assert(numKeys > 0 || (isRoot && children == null))
      assert(numKeys <= MaxKeys)
      for (i <- 0 until MaxKeys) {
        assert((keys(i) == null) == (i >= numKeys))
        assert((values(i) == null) == (i >= numKeys))
      }
      if (children != null) {
        for (i <- 0 to MaxKeys)
          assert((children(i) == null) == (i >= numKeys + 1))
        for (i <- 0 until numKeys)
          assert(children(i).numKeys + children(i+1).numKeys >= MinKeysForPair)
        for (i <- 0 to numKeys)
          children(i).validate(false)
      }
    }
  }

  def newRoot[A,B](gen: Long) = new Node[A,B](gen, 0, false, new Array[AnyRef](2 * MaxKeys), null)

  abstract class Base[A,B](var root: BTree.Node[A,B], var _size: Int)(implicit cmp: Ordering[A]) {

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

    def validate() {
      root.validate(true)
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

  class MutableTree[A,B](root0: BTree.Node[A,B], size0: Int)(implicit cmp: Ordering[A]) extends Base[A,B](root0, size0) {
    def this()(implicit cmp: Ordering[A]) = this(newRoot[A,B](0L), 0)

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
      val r = newRoot[A,B](root.generation)
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
    for (pass <- 0 until 10) {
      testInt(rands(0))
    }
    println("------------- adding short")
    for (pass <- 0 until 10) {
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

  def Range = 10000
  def GetPct = 95
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

  def test[A](name: String, rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A]) {
    cmpCount = 0
    val (abest,aavg) = testBTree(rand, keyGen)
    val ac = cmpCount
    //println("!!")
    cmpCount = 0
    val (bbest,bavg) = testFatLeaf(rand, keyGen)
    val bc = cmpCount
    cmpCount = 0
    val (cbest,cavg) = testJavaTree(rand, keyGen)
    val cc = cmpCount
    println(name + ": BTree: " + abest + " nanos/op (" + aavg + " avg),  " +
            name + ": FatLeaf: " + bbest + " nanos/op (" + bavg + " avg),  " +
            "java.util.TreeMap: " + cbest + " nanos/op (" + cavg + " avg)")
    if (ac > 0)
      println("  BTree: " + ac + " compares,  FatLeaf: " + bc + " compares,  java.util.TreeMap: " + cc + " compares")
  }

  def testBTree[A](rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A]): (Long,Long) = {
    val tt0 = System.currentTimeMillis
    val m = new MutableTree[A,String]
    var best = Long.MaxValue
    for (group <- 1 until 10000) {
      var i = 1000
      val t0 = System.nanoTime
      var matching = 0
      while (i > 0) {
        val key = keyGen()
        val pct = rand.nextDouble() * 100
        if (pct < GetPct) {
          if (m.contains(key)) matching += 1
        } else if (pct < GetPct + IterPct) {
          // iterate
          var n = 0
          //for (e <- m.elements) n += 1
          for (e <- m) n += 1
          assert(n == m.size)
        } else if (pct < 50 + (GetPct + IterPct) / 2) {
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

  def testFatLeaf[A](rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A]): (Long,Long) = {
    val tt0 = System.currentTimeMillis
    val m = new FatLeaf.MutableTree[A,String]
    var best = Long.MaxValue
    for (group <- 1 until 10000) {
      var i = 1000
      val t0 = System.nanoTime
      var matching = 0
      while (i > 0) {
        val key = keyGen()
        val pct = rand.nextDouble() * 100
        if (pct < GetPct) {
          if (m.contains(key)) matching += 1
        } else if (pct < GetPct + IterPct) {
          // iterate
          var n = 0
          //for (e <- m.elements) n += 1
          for (e <- m) n += 1
          assert(n == m.size)
        } else if (pct < 50 + (GetPct + IterPct) / 2) {
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
        val pct = rand.nextDouble() * 100
        if (pct < GetPct) {
          if (m.containsKey(key)) matching += 1
        } else if (pct < GetPct + IterPct) {
          // iterate
          var n = 0
          val iter = m.entrySet.iterator
          while (iter.hasNext) {
            iter.next()
            n += 1
          }
          assert(n == m.size)
        } else if (pct < 50 + (GetPct + IterPct) / 2) {
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