package mmt

import annotation.tailrec
import reflect.ClassManifest

object FatLeafTree {

  //////// factory method

  def empty[A, B](implicit cmp: Ordering[A], am: ClassManifest[A]): FatLeafTree[A, B] = {
    (cmp.asInstanceOf[Ordering[_]] match {
      case Ordering.Boolean => new DefaultBoolean[B]()
      case Ordering.Byte    => new DefaultByte[B]()
      case Ordering.Short   => new DefaultShort[B]()
      case Ordering.Char    => new DefaultChar[B]()
      case Ordering.Int     => new DefaultInt[B]()
      case Ordering.Float   => new DefaultFloat[B]()
      case Ordering.Long    => new DefaultLong[B]()
      case Ordering.Double  => new DefaultDouble[B]()
      case _                => new Generic[A, B]()
    }).asInstanceOf[FatLeafTree[A, B]]
  }

  //////// tree structure

  def LeafMin = 15
  def LeafMax = 2 * LeafMin + 1
  def RootInitialCap = 4

  abstract class Node[A, B](var parent: Branch[A, B]) {
    def isEmpty: Boolean
    def height: Int
  }

  class Branch[A, B](par0: Branch[A, B], 
                     var height: Int,
                     var key: A,
                     var value: B,
                     var left: Node[A, B],
                     var right: Node[A, B]) extends Node[A, B](par0) {
    def isEmpty = false
  }

  class Leaf[A, B](par0: Branch[A, B], 
                   var size: Int,
                   var keys: Array[A],
                   var values: Array[AnyRef]) extends Node[A, B](par0) {
    def this(par0: Branch[A, B])(implicit am: ClassManifest[A]) =
      this(par0, 0, new Array[A](RootInitialCap), new Array[AnyRef](RootInitialCap))

    def isEmpty = size == 0
    def height = 1
    def getValue(i: Int): B = values(i).asInstanceOf[B]
    def setValue(i: Int, v: B) { values(i) = v.asInstanceOf[AnyRef] }
  }

  //////// iteration

  abstract class Iter[A, B, Z](root: Node[A, B]) extends Iterator[Z] {

    //////// abstract

    protected def result(k: A, v: B): Z

    //////// implementation

    private val stack = new Array[Node[A, B]](root.height)
    private var depth = 0
    private var index = 0

    if (!root.isEmpty) pushMin(root)

    @tailrec final def pushMin(n: Node[A, B]) {
      stack(depth) = n
      depth += 1
      n match {
        case b: Branch[A, B] => pushMin(b.left)
        case _ => {}
      }
    }

    private def advance() {
      stack(depth - 1) match {
        case t: Leaf[A, B] => {
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
        case b: Branch[A, B] => {
          // pop current node
          depth -= 1
          pushMin(b.right)
        }
      }
    }

    def hasNext = depth > 0

    def next: Z = {
      if (depth == 0) throw new IllegalStateException
      val z = stack(depth - 1) match {
        case t: Leaf[A, B] => result(t.keys(index), t.getValue(index))
        case b: Branch[A, B] => result(b.key, b.value)
      }
      advance()
      z
    }
  }

  //////// concrete tree implementations

  class DefaultBoolean[B](root0: Node[Boolean, B], sic0: Int) extends FatLeafTree[Boolean, B](root0, sic0) with Ordering.BooleanOrdering {
    def this() = { this(null, 0) ; right = new Leaf[Boolean, B](this) }
    def cloneImpl() = new DefaultBoolean(frozenRoot, sizeIfCached)
  }
  class DefaultByte[B](root0: Node[Byte, B], sic0: Int) extends FatLeafTree[Byte, B](root0, sic0) with Ordering.ByteOrdering {
    def this() = { this(null, 0) ; right = new Leaf[Byte, B](this) }
    def cloneImpl() = new DefaultByte(frozenRoot, sizeIfCached)
  }
  class DefaultShort[B](root0: Node[Short, B], sic0: Int) extends FatLeafTree[Short, B](root0, sic0) with Ordering.ShortOrdering {
    def this() = { this(null, 0) ; right = new Leaf[Short, B](this) }
    def cloneImpl() = new DefaultShort(frozenRoot, sizeIfCached)
  }
  class DefaultChar[B](root0: Node[Char, B], sic0: Int) extends FatLeafTree[Char, B](root0, sic0) with Ordering.CharOrdering {
    def this() = { this(null, 0) ; right = new Leaf[Char, B](this) }
    def cloneImpl() = new DefaultChar(frozenRoot, sizeIfCached)
  }
  class DefaultInt[B](root0: Node[Int, B], sic0: Int) extends FatLeafTree[Int, B](root0, sic0) with Ordering.IntOrdering {
    def this() = { this(null, 0) ; right = new Leaf[Int, B](this) }
    def cloneImpl() = new DefaultInt(frozenRoot, sizeIfCached)
  }
  class DefaultFloat[B](root0: Node[Float, B], sic0: Int) extends FatLeafTree[Float, B](root0, sic0) with Ordering.FloatOrdering {
    def this() = { this(null, 0) ; right = new Leaf[Float, B](this) }
    def cloneImpl() = new DefaultFloat(frozenRoot, sizeIfCached)
  }
  class DefaultLong[B](root0: Node[Long, B], sic0: Int) extends FatLeafTree[Long, B](root0, sic0) with Ordering.LongOrdering {
    def this() = { this(null, 0) ; right = new Leaf[Long, B](this) }
    def cloneImpl() = new DefaultLong(frozenRoot, sizeIfCached)
  }
  class DefaultDouble[B](root0: Node[Double, B], sic0: Int) extends FatLeafTree[Double, B](root0, sic0) with Ordering.DoubleOrdering {
    def this() = { this(null, 0) ; right = new Leaf[Double, B](this) }
    def cloneImpl() = new DefaultDouble(frozenRoot, sizeIfCached)
  }
  class Generic[A : Ordering : ClassManifest, B](root0: Node[A, B], sic0: Int) extends FatLeafTree[A, B](root0, sic0)  {
    def this() = { this (null, 0) ; right = new Leaf[A, B](this) }
    def cloneImpl() = new Generic(frozenRoot, sizeIfCached)
    def compare(lhs: A, rhs: A): Int = ordering.compare(lhs, rhs)
  }

}

abstract class FatLeafTree[@specialized A, B](
        root0: FatLeafTree.Node[A, B], private var _cachedSize: Int)(
        implicit val ordering: Ordering[A], val am: ClassManifest[A]) extends FatLeafTree.Branch[A, B](
    null, -1, null.asInstanceOf[A], null.asInstanceOf[B], null, root0) {

  import FatLeafTree._

  //////// abstract members

  def cloneImpl(): FatLeafTree[A, B]

  def compare(lhs: A, rhs: A): Int

  //////// public interface

  override def clone(): FatLeafTree[A, B] = cloneImpl()

  override def isEmpty: Boolean = right.isEmpty
  def size: Int = sizeImpl
  def sizeIfCached: Int = _cachedSize

  def clear() {
    if (!isEmpty) {
      right = empty[A, B].right
      assert(right.parent != null)
      right.parent = this
      _cachedSize = 0
    }
  }

  def firstKey: A = firstKey(right)
  def lastKey: A = lastKey(right)
  def head: (A, B) = head(right)
  def last: (A, B) = last(right)
  def contains(k: A): Boolean = contains(right, k)
  def get(k: A): Option[B] = get(right, k)

  def put(k: A, v: B): Option[B] = {
    val z = put(unsharedRight(this), k, v)
    if (_cachedSize >= 0 && z.isEmpty)
      _cachedSize += 1
    z
  }

  def putAll(rhs: FatLeafTree[A, _ <: B]) {
    if (isEmpty) {
      right = rhs.frozenRoot.asInstanceOf[Nd]
      _cachedSize = rhs._cachedSize
    } else if (!rhs.isEmpty) {
      // extract the right-most element to use as a new root
      val newRoot = new Br(this, 0, null.asInstanceOf[A], null.asInstanceOf[B], null, null)
      copyAndRemoveMax(newRoot, right)

      // the overlapping portion we must visit one-by-one, the distinct portion
      // we can share
      val overlap = rhs.clone().removeGT(newRoot.key)
      val distinct = rhs.clone().removeLE(newRoot.key)

      newRoot.left = right
      newRoot.right = distinct.right.asInstanceOf[Nd]
      right = newRoot
      repair(newRoot)

      if (_cachedSize >= 0 && distinct._cachedSize >= 0)
        _cachedSize += distinct._cachedSize
      else
        _cachedSize = -1

      // now handle the rest
      overlap.unstableForeach { (k, v) => put(k, v) }
    }
  }

  def remove(k: A): Option[B] = {
    val z = if (isShared(right)) removeFromShared(this, right, k) else remove(right, k)
    if (_cachedSize >= 0 && !z.isEmpty)
      _cachedSize -= 1
    z
  }

  def removeLT(k: A): this.type = { if (removeLT(unsharedRight(this), k, false)) _cachedSize = -1 ; this }
  def removeLE(k: A): this.type = { if (removeLE(unsharedRight(this), k, false)) _cachedSize = -1 ; this }
  def removeGE(k: A): this.type = { if (removeGE(unsharedRight(this), k, false)) _cachedSize = -1 ; this }
  def removeGT(k: A): this.type = { if (removeGT(unsharedRight(this), k, false)) _cachedSize = -1 ; this }

//  def filter(f: (A, B) => Boolean): this.type = {
//    filter(right, f)
//    _cachedSize = -1
//  }

  def keysIterator: Iterator[A] = new Iter[A, B, A](frozenRoot) {
    protected def result(k: A, v: B) = k
  }
  def valuesIterator: Iterator[B] = new Iter[A, B, B](frozenRoot) {
    protected def result(k: A, v: B) = v
  }
  def iterator: Iterator[(A, B)] = new Iter[A, B, (A, B)](frozenRoot) {
    protected def result(k: A, v: B) = (k, v)
  }
  def stableForeach(f: (A, B) => Unit) { foreach(frozenRoot, f) }
  def unstableForeach(f: (A, B) => Unit) { foreach(right, f) }

  //////// internal machinery

  private type Nd = Node[A, B]
  private type Lf = Leaf[A, B]
  private type Br = Branch[A, B]

  private def frozenRoot: Node[A, B] = markShared(right)

  def validateTree {
    def recurse(n: Nd): Int = {
      n match {
        case t: Lf => {
          assert(t.size <= LeafMax)
          if (t ne this.right)
            assert(t.size >= LeafMin)
          t.size
        }
        case b: Br => {
          assert(b.left != null)
          assert(b.right != null)
          assert(math.abs(balance(b)) <= 1)
          assert(b.height == math.max(b.left.height, b.right.height) + 1)
          recurse(b.left) + 1 + recurse(b.right)
        }
      }
    }

    assert(left == null)
    assert(height == -1)
    val s = recurse(right)
    assert(s == computeSize(right))
    if (_cachedSize >= 0)
      assert(s == _cachedSize)
    var prev: Option[A] = None
    var count = 0
    unstableForeach { (k,v) =>
      count += 1
      for (p <- prev) assert(ordering.compare(p, k) < 0)
      prev = Some(k)
    }
    assert(count == s)
  }

  //////// size

  private def sizeImpl: Int = {
    if (_cachedSize < 0)
      _cachedSize = computeSize(right)
    _cachedSize
  }

  private def computeSize(n: Nd): Int = n match {
    case t: Lf => t.size
    case b: Br => computeSize(b.left) + 1 + computeSize(b.right)
  }

  //////// reads

  @tailrec private def firstKey(n: Nd): A = n match {
    case t: Lf => {
      if (t.size == 0)
        throw new NoSuchElementException
      t.keys(0)
    }
    case b: Br => firstKey(b.left)
  }

  @tailrec private def lastKey(n: Nd): A = n match {
    case t: Lf => {
      if (t.size == 0)
        throw new NoSuchElementException
      t.keys(t.size - 1)
    }
    case b: Br => lastKey(b.right)
  }

  @tailrec private def head(n: Nd): (A, B) = n match {
    case t: Lf => {
      if (t.size == 0)
        throw new NoSuchElementException
      (t.keys(0), t.getValue(0))
    }
    case b: Br => head(b.left)
  }

  @tailrec private def last(n: Nd): (A, B) = n match {
    case t: Lf => {
      if (t.size == 0)
        throw new NoSuchElementException
      (t.keys(t.size - 1), t.getValue(t.size - 1))
    }
    case b: Br => last(b.right)
  }

  @tailrec private def contains(n: Nd, k: A): Boolean = n match {
    case t: Lf => keySearch(t, k) >= 0
    case b: Br => {
      val c = compare(k, b.key)
      (c == 0) || contains(if (c < 0) b.left else b.right, k)
    }
  }

  @tailrec private def get(n: Nd, k: A): Option[B] = n match {
    case t: Lf => {
      val i = keySearch(t, k)
      if (i >= 0) Some(t.getValue(i)) else None
    }
    case b: Br => {
      val c = compare(k, b.key)
      if (c == 0) Some(b.value) else get(if (c < 0) b.left else b.right, k)
    }
  }

  private def keySearch(t: Lf, k: A): Int = {
    var b = 0
    var e = t.size
    while (b < e) {
      val mid = (b + e) >>> 1
      val c = compare(k, t.keys(mid))
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

  @tailrec private def put(n: Nd, k: A, v: B): Option[B] = n match {
    case t: Lf => leafPut(t, k, v)
    case b: Br => {
      val c = compare(k, b.key)
      if (c == 0) branchUpdate(b, v) else put(if (c < 0) unsharedLeft(b) else unsharedRight(b), k, v)
    }
  }

  private def leafPut(t: Lf, k: A, v: B): Option[B] = {
    val i = keySearch(t, k)
    if (i >= 0) {
      val z = t.getValue(i)
      t.setValue(i, v)
      Some(z)
    } else {
      leafInsert(t, ~i, k, v)
      None
    }
  }

  private def branchUpdate(b: Br, v: B): Some[B] = {
    val z = b.value
    b.value = v
    Some(z)
  }

  private def leafInsert(t: Lf, i: Int, k: A, v: B) {
    // make space
    val num = t.size

    // root node might be allocated less than LeafMax in size
    if (num == t.keys.length)
      growArrays(t)

    System.arraycopy(t.keys, i, t.keys, i + 1, num - i)
    System.arraycopy(t.values, i, t.values, i + 1, num - i)
    t.size = num + 1

    // copy the values
    t.keys(i) = k
    t.setValue(i, v)

    // split if necessary
    if (num + 1 == LeafMax)
      split(t)
  }

  private def growArrays(t: Lf) {
    val nn = math.min(t.keys.length * 2, LeafMax)
    val kk = t.keys
    t.keys = new Array[A](nn)
    System.arraycopy(kk, 0, t.keys, 0, kk.length)
    val vv = t.values
    t.values = new Array[AnyRef](nn)
    System.arraycopy(vv, 0, t.values, 0, vv.length)
  }

  private def split(tL: Lf) {
    val leftSize = LeafMax / 2
    val rightSize = LeafMax - 1 - leftSize

    // existing terminal becomes left leaf, create new branch
    val b = new Br(tL.parent, 2, tL.keys(leftSize), tL.getValue(leftSize), tL, null)
    val tR = new Lf(b, rightSize, new Array[A](LeafMax), new Array[AnyRef](LeafMax))
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

  private def clear(t: Lf, pos: Int, len: Int) {
    clear(t.keys, pos, len)
    clear(t.values, pos, len)
  }

  private def clear[@specialized C](a: Array[C], pos: Int, len: Int) {
    var i = pos
    while (i < pos + len) {
      a(i) = null.asInstanceOf[C]
      i += 1
    }
  }

  //////// remove

  @tailrec private def remove(n: Nd, k: A): Option[B] = n match {
    case t: Lf => leafRemove(t, k)
    case b: Br => {
      val c = compare(k, b.key)
      if (c == 0) {
        branchRemove(b)
      } else {
        val child = if (c < 0) b.left else b.right
        if (isShared(child))
          removeFromShared(b, child, k)
        else
          remove(child, k)
      }
    }
  }

  private def removeFromShared(p: Br, child: Nd, k: A): Option[B] = {
    if (!contains(child, k))
      None
    else
      removeContained(if (child eq p.right) unsharedRight(p) else unsharedLeft(p), k)
  }

  @tailrec private def removeContained(n: Nd, k: A): Option[B] = n match {
    case t: Lf => leafRemove(t, k)
    case b: Br => {
      val c = compare(k, b.key)
      if (c == 0)
        branchRemove(b)
      else
        removeContained(if (c < 0) unsharedLeft(b) else unsharedRight(b), k)
    }
  }

  private def branchRemove(b: Br): Option[B] = {
    val z = b.value
    copyAndRemoveMax(b, unsharedLeft(b))
    Some(z)
  }

  private def leafRemove(t: Lf, k: A): Option[B] = {
    val i = keySearch(t, k)
    if (i >= 0) {
      val z = t.getValue(i)
      leafRemoveByIndex(t, i)
      Some(z)
    } else {
      None
    }
  }

  @tailrec private def copyAndRemoveMax(target: Br, n: Nd) {
    n match {
      case t: Lf => {
        // steal one
        val i = t.size - 1
        target.key = t.keys(i)
        target.value = t.getValue(i)
        leafRemoveMax(t)
      }
      case b: Br => copyAndRemoveMax(target, unsharedRight(b))
    }
  }

  private def leafRemoveMax(t: Lf) {
    val num = t.size - 1
    t.size = num
    clear(t, num, 1)
    if (num < LeafMin)
      refill(t)
  }

  private def leafRemoveByIndex(t: Lf, i: Int) {
    val tailSize = t.size - 1 - i
    System.arraycopy(t.keys, i + 1, t.keys, i, tailSize)
    System.arraycopy(t.values, i + 1, t.values, i, tailSize)
    leafRemoveMax(t)
  }

  private def refill(t: Lf) {
    t.parent.height match {
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
  }

  private def refillAsLeft(tL: Lf) {
    //assert(tL.size == LeafMin - 1)
    val b = tL.parent
    val tR = unsharedRight(b).asInstanceOf[Lf]
    if (tR.size <= LeafMin)
      merge(b, tL, tR)
    else {
      tL.keys(LeafMin - 1) = b.key
      tL.setValue(LeafMin - 1, b.value)
      tL.size = LeafMin
      b.key = tR.keys(0)
      b.value = tR.getValue(0)
      leafRemoveByIndex(tR, 0)
    }
  }

  private def refillAsRight(tR: Lf) {
    //assert(tR.size == LeafMin - 1)
    val b = tR.parent
    val tL = unsharedLeft(b).asInstanceOf[Lf]
    if (tL.size <= LeafMin)
      merge(b, tL, tR)
    else {
      leafInsert(tR, 0, b.key, b.value)
      b.key = tL.keys(tL.size - 1)
      b.value = tL.getValue(tL.size - 1)
      leafRemoveMax(tL)
    }
  }

  private def merge(b: Br, tL: Lf, tR: Lf) {
    tL.keys(tL.size) = b.key
    tL.setValue(tL.size, b.value)
    System.arraycopy(tR.keys, 0, tL.keys, tL.size + 1, tR.size)
    System.arraycopy(tR.values, 0, tL.values, tL.size + 1, tR.size)
    tL.size += 1 + tR.size
    tL.parent = b.parent

    replaceAndRepair(b, tL)
  }

  //////// bulk removal

  @tailrec private def removeLT(n: Nd, k: A, z: Boolean): Boolean = {
    n match {
      case t: Lf => {
        val i = keySearch(t, k)
        if (i >= 0)
          leafRemoveByIndex(t, 0, i)
        else
          leafRemoveByIndex(t, 0, ~i)
        z
      }
      case b: Br => {
        val c = compare(k, b.key)
        if (c < 0) {
          removeLT(unsharedLeft(b), k, z)
        } else {
          val nR = unsharedRight(b)
          nR.parent = b.parent
          replaceAndRepair(b, nR)
          if (c == 0) {
            put(nR, b.key, b.value)
            true
          } else {
            removeLT(nR, k, true)
          }
        }
      }
    }
  }

  @tailrec private def removeLE(n: Nd, k: A, z: Boolean): Boolean = {
    n match {
      case t: Lf => {
        val i = keySearch(t, k)
        if (i >= 0)
          leafRemoveByIndex(t, 0, i + 1)
        else
          leafRemoveByIndex(t, 0, ~i)
        z
      }
      case b: Br => {
        val c = compare(k, b.key)
        if (c < 0) {
          removeLE(unsharedLeft(b), k, z)
        } else {
          val nR = unsharedRight(b)
          nR.parent = b.parent
          replaceAndRepair(b, nR)
          (c <= 0) || removeLE(nR, k, true)
        }
      }
    }
  }

  @tailrec private def removeGE(n: Nd, k: A, z: Boolean): Boolean = {
    n match {
      case t: Lf => {
        val i = keySearch(t, k)
        if (i >= 0)
          leafRemoveByIndex(t, i, t.size)
        else
          leafRemoveByIndex(t, ~i, t.size)
        z
      }
      case b: Br => {
        val c = compare(k, b.key)
        if (c <= 0) {
          val nL = unsharedLeft(b)
          nL.parent = b.parent
          replaceAndRepair(b, nL)
          (c >= 0) || removeGE(nL, k, true)
        } else {
          removeGE(unsharedRight(b), k, z)
        }
      }
    }
  }

  @tailrec private def removeGT(n: Nd, k: A, z: Boolean): Boolean = {
    n match {
      case t: Lf => {
        val i = keySearch(t, k)
        if (i >= 0)
          leafRemoveByIndex(t, i + 1, t.size)
        else
          leafRemoveByIndex(t, ~i, t.size)
        z
      }
      case b: Br => {
        val c = compare(k, b.key)
        if (c <= 0) {
          val nL = unsharedLeft(b)
          nL.parent = b.parent
          replaceAndRepair(b, nL)
          if (c < 0) {
            removeGT(nL, k, true)
          } else {
            put(nL, b.key, b.value)
            true
          }
        } else {
          removeGT(unsharedRight(b), k, z)
        }
      }
    }
  }

  private def leafRemoveByIndex(t: Lf, begin: Int, end: Int) {
    if (begin != end) {
      val n = end - begin
      val tailSize = t.size - end
      System.arraycopy(t.keys, end, t.keys, begin, tailSize)
      System.arraycopy(t.values, end, t.values, begin, tailSize)

      val num = t.size - n
      t.size = num
      clear(t, num, n)
      if (num < LeafMin)
        refill(t)
    }
  }

  //////// sharing machinery

  private def isShared(n: Nd) = n.parent == null
  
  private def markShared(n: Nd): Nd = {
    if (n.parent != null)
      n.parent = null
    n
  }

  private def unsharedLeft(b: Br): Nd = {
    if (isShared(b.left))
      b.left = unshare(b.left, b)
    b.left
  }

  private def unsharedRight(b: Br): Nd = {
    if (isShared(b.right))
      b.right = unshare(b.right, b)
    b.right
  }

  private def unshare(n: Nd, p: Br): Nd = n match {
    case t: Lf =>
      new Lf(p, t.size, t.keys.clone(), t.values.clone())
    case b: Br =>
      markShared(b.left)
      markShared(b.right)
      new Br(p, b.height, b.key, b.value, b.left, b.right)
  }

  //////// AVL rebalancing

  private def balance(n: Nd) = n match {
    case b: Br => b.left.height - b.right.height
    case _ => 0
  }

  @tailrec private def repair(b: Br) {
    val h0 = b.height

    // only repair if we're not the root holder
    if (h0 >= 0) {
      val hL = b.left.height
      val hR = b.right.height
      val bal = hL - hR
      if (bal > 1) {
        // Both left and right are valid AVL trees, but left is too large so we
        // must rotate right.  If this is from a bulk insertion or removal then
        // left might be _much_ too large.  If left.right is larger than
        // left.left then if we rotate right the result will have a -2 balance,
        // so in that case we must first rotateLeft on left.  In either case,
        // if bal > 2 then the right node of the result may need repair, which
        // happens to be the new location of b.
        replaceAndMaybeRepair(b, h0, if (balance(b.left) < 0) rotateRightOverLeft(b) else rotateRight(b))
        if (bal > 2)
          repair(b)
      } else if (bal < -1) {
        replaceAndMaybeRepair(b, h0, if (balance(b.right) > 0) rotateLeftOverRight(b) else rotateLeft(b))
        if (bal < -2)
          repair(b)
      } else {
        // no rotations needed, just repair height
        val h = 1 + math.max(hL, hR)
        if (h != h0) {
          b.height = h
          repair(b.parent)
        }
      }
    }
  }

  private def replaceAndMaybeRepair(n0: Nd, h0: Int, n: Br) {
    replace(n0, n)
    if (n.height != h0)
      repair(n.parent)
  }

  private def replaceAndRepair(n0: Nd, n: Nd) {
    replace(n0, n)
    repair(n.parent)
  }

  private def replace(n0: Nd, n: Nd) {
    val p = n.parent
    if (p.left eq n0) p.left = n else p.right = n
  }

  private def rotateRight(b: Br): Br = {
    val nL = unsharedLeft(b).asInstanceOf[Br]
    nL.parent = b.parent

    b.left = nL.right
    if (b.left.parent != null)
      b.left.parent = b

    nL.right = b
    b.parent = nL

    b.height = 1 + math.max(b.left.height, b.right.height)
    nL.height = 1 + math.max(nL.left.height, b.height)

    nL
  }

  private def rotateRightOverLeft(b: Br): Br = {
    b.left = rotateLeft(unsharedLeft(b).asInstanceOf[Br])
    rotateRight(b)
  }

  private def rotateLeft(b: Br): Br = {
    val nR = unsharedRight(b).asInstanceOf[Br]
    nR.parent = b.parent

    b.right = nR.left
    if (b.right.parent != null)
      b.right.parent = b

    nR.left = b
    b.parent = nR

    b.height = 1 + math.max(b.right.height, b.left.height)
    nR.height = 1 + math.max(nR.right.height, b.height)

    nR
  }

  private def rotateLeftOverRight(b: Br): Br = {
    b.right = rotateRight(unsharedRight(b).asInstanceOf[Br])
    rotateLeft(b)
  }

  //////// enumeration

  private def foreach(n: Nd, f: (A, B) => Unit) {
    n match {
      case t: Lf => {
        var i = 0
        while (i < t.size) {
          f(t.keys(i), t.getValue(i))
          i += 1
        }
      }
      case b: Br => {
        foreach(b.left, f)
        f(b.key, b.value)
        foreach(b.right, f)
      }
    }
  }
}
