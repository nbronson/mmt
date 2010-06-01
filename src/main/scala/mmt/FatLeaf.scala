package mmt

import annotation.tailrec

// FatLeaf

private object FatLeafNotFound

object FatLeaf {
  import mmt.{FatLeafNotFound => NotFound}

  private def Capacity = 15

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
                         var _leftOrExtras: AnyRef,
                         var right: Node[A,B]) {

    def this(h: Int, k: A, v: B, p: Node[A,B], left0: Node[A,B], right0: Node[A,B]) =
      this(h.asInstanceOf[Byte], 0: Byte, k, v, p, left0, right0)

    def this(es: Int, p: Node[A,B], extras: Array[AnyRef]) =
      this(1: Byte, es.asInstanceOf[Byte], null.asInstanceOf[A], null.asInstanceOf[B], p, extras, null)

    def this(es: Int, p: Node[A,B]) = this(es, p, new Array[AnyRef](2 * Capacity))

    
    def height = _height: Int
    def height_=(v: Int) { _height = v.asInstanceOf[Byte] }

    def isLeaf = _extraSize != (0: Byte)

    def extraSize = _extraSize: Int
    def extraSize_=(s: Int) { _extraSize = s.asInstanceOf[Byte] }

    def left = {
      assert(!isLeaf) // TODO: remove
      _leftOrExtras.asInstanceOf[Node[A,B]]
    }
    def left_=(n: Node[A,B]) { _leftOrExtras = n }

    def extras: Array[AnyRef] = _leftOrExtras.asInstanceOf[Array[AnyRef]]

    def keys(i: Int): A = extras(2 * i).asInstanceOf[A]
    def setKey(i: Int, k: A) { extras(2 * i) = k.asInstanceOf[AnyRef] }

    def values(i: Int): B = extras(2 * i + 1).asInstanceOf[B]
    def setValue(i: Int, v: B) { extras(2 * i + 1) = v.asInstanceOf[AnyRef] }

    def shared = parent eq null

    //////// reads

    @tailrec def nodeForGet(k: A)(implicit cmp: Ordering[A]): Node[A,B] = {
      if (isLeaf) {
        this
      } else {
        val c = cmp.compare(k, key)
        if (c < 0) {
          left.nodeForGet(k)
        } else if (c > 0) {
          right.nodeForGet(k)
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
      if (shared) {
        this
      } else if (isLeaf) {
        // clone the keys and values array as well
        new Node[A,B](1: Byte, _extraSize, key, value, p, extras.clone(), null)
      } else {
        // push down the mark first
        left.markShared()
        right.markShared()
        new Node[A,B](_height, 0: Byte, key, value, p, _leftOrExtras, right)
      }
    }

    def markShared() {
      if (!shared)
        parent = null
    }

    //////// writes

    @tailrec def put(k: A, v: B)(implicit cmp: Ordering[A]): AnyRef = {
      if (isLeaf) {
        leafPut(k, v)
      } else {
        val c = cmp.compare(k, key)
        if (c < 0)
          unsharedLeft().put(k, v)
        else if (c > 0)
          unsharedRight().put(k, v)
        else
          internalUpdate(v)
      }
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

      // link the nodes properly, but let fix() recompute the height
      extraSize = 0
      left = newLeft
      right = newRight

      // we've grown, so we might need to rebalance
      fix()
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

      nR
    }

    def rotateLeftOverRight(): Node[A,B] = {
      right = right.unshare(this).rotateRight()
      rotateLeft()
    }

    @tailrec def minKey: A = if (!isLeaf) left.minKey else keys(0)

    @tailrec def maxKey: A = if (!isLeaf) right.maxKey else keys(extraSize - 1)

    def computeSize: Int = {
      if (isLeaf)
        extraSize
      else
        1 + left.computeSize + right.computeSize
    }

    def validate()(implicit cmp: Ordering[A]) {
      if (height < 0) {
        // rootHolder
        assert(left == null && right != null)
      } else if (isLeaf) {
        assert(extraSize > 0 && extraSize <= Capacity)
        assert(right == null)
      } else {
        assert(left != null && (left.parent eq this))
        assert(right != null && (right.parent eq this))
        assert(extraSize == 0)
        assert(height == 1 + math.max(height(left), height(right)))
        assert(math.abs(height(left) - height(right)) <= 1)
        left.validate()
        right.validate()
      }
    }
  }

  abstract class Tree[A,B](implicit cmp: Ordering[A]) {

    protected val rootHolder = new Node[A,B](-1: Byte, 0: Byte, null.asInstanceOf[A], null.asInstanceOf[B], null, null, null)

    protected def root = rootHolder.right
    protected var _size = 0

    def isEmpty: Boolean = (_size == 0)
    def size: Int = _size

    def contains(key: A): Boolean = {
      if (root == null) {
        false
      } else {
        val n = root.nodeForGet(key)
        !n.isLeaf || n.keySearch(key) >= 0
      }
    }

    def get(key: A): Option[B] = {
      if (root != null) {
        val n = root.nodeForGet(key)
        if (!n.isLeaf) {
          return Some(n.value)
        } else {
          val i = n.keySearch(key)
          if (i >= 0)
            return Some(n.values(i))
        }
      }
      return None
    }

    def apply(key: A): B = {
      if (root != null) {
        val n = root.nodeForGet(key)
        if (n.extraSize == 0) {
          return n.value
        } else {
          val i = n.keySearch(key)
          if (i >= 0)
            return n.values(i)
        }
      }
      return default(key)
    }

    def default(key: A): B = throw new IllegalArgumentException

    def elements: Iterator[(A,B)] = new Iterator[(A,B)] {
      // TODO: rewrite using a stack to support iteration without unsharing
      
      private var current: Node[A,B] = if (root == null) null else root.unsharedLeftmost()
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
        assert(root == null)
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
      validate()
    }

    def put(key: A, value: B): Option[B] = {
      val z = putImpl(key, value)
      if (z eq NotFound) None else Some(z.asInstanceOf[B])
    }

    private def putImpl(key: A, value: B): AnyRef = {
      if (root == null) {
        rootHolder.right = new Node(1, rootHolder)
        root.setKey(0, key)
        root.setValue(0, value)
        _size += 1
        NotFound
      } else {
        val z = root.put(key, value)
        if (z eq NotFound)
          _size += 1
        z
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
    println(name + ": FatLeaf: " + a + " nanos/op,  java.util.TreeMap: " + b + " nanos/op")
    if (ac > 0) println("  FatLeaf: " + ac + " compares,  java.util.TreeMap: " + bc + " compares")
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