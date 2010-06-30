package mmt

import annotation.tailrec

object FatLeafTree {

  //////// factory method

  def empty[A,B](implicit cmp: Ordering[A], am: ClassManifest[A], bm: ClassManifest[B]): FatLeafTree[A,B] = {
    val tree = (cmp match {
      case Ordering.Boolean => new DefaultBoolean(null, 0)
      case Ordering.Byte    => new DefaultByte(null, 0)
      case Ordering.Short   => new DefaultShort(null, 0)
      case Ordering.Char    => new DefaultChar(null, 0)
      case Ordering.Int     => new DefaultInt(null, 0)
      case Ordering.Float   => new DefaultFloat(null, 0)
      case Ordering.Long    => new DefaultLong(null, 0)
      case Ordering.Double  => new DefaultDouble(null, 0)
      case _                => new Generic(null, 0, cmp)
    }).asInstanceOf[FatLeafTree[A,B]]
    tree.right = new Leaf[A,B](tree, 0, new Array[A](LeafMax), new Array[B](LeafMax))
    tree
  }

  //////// tree structure

  def LeafMin = 15
  def LeafMax = 2 * LeafMin + 1

  abstract class Node[A,B](var parent: Branch[A,B])

  class Branch[A,B](par0: Branch[A,B],
                    var height: Int,
                    var key: A,
                    var value: B,
                    var left: Node[A,B],
                    var right: Node[A,B]) extends Node[A,B](par0)

  class Leaf[A,B](par0: Branch[A,B],
                  var size: Int,
                  val keys: Array[A],
                  val values: Array[B]) extends Node[A,B](par0)

  //////// concrete tree implementations

  class DefaultBoolean[B](root0: Node[Boolean,B], sic0: Int) extends FatLeafTree[Boolean,B](root0, sic0) with Ordering.BooleanOrdering {
    def cloneImpl() = new DefaultBoolean(frozenRoot, sizeIfCached)
  }
  class DefaultByte[B](root0: Node[Byte,B], sic0: Int) extends FatLeafTree[Byte,B](root0, sic0) with Ordering.ByteOrdering {
    def cloneImpl() = new DefaultByte(frozenRoot, sizeIfCached)
  }
  class DefaultShort[B](root0: Node[Short,B], sic0: Int) extends FatLeafTree[Short,B](root0, sic0) with Ordering.ShortOrdering {
    def cloneImpl() = new DefaultShort(frozenRoot, sizeIfCached)
  }
  class DefaultChar[B](root0: Node[Char,B], sic0: Int) extends FatLeafTree[Char,B](root0, sic0) with Ordering.CharOrdering {
    def cloneImpl() = new DefaultChar(frozenRoot, sizeIfCached)
  }
  class DefaultInt[B](root0: Node[Int,B], sic0: Int) extends FatLeafTree[Int,B](root0, sic0) with Ordering.IntOrdering {
    def cloneImpl() = new DefaultInt(frozenRoot, sizeIfCached)
  }
  class DefaultFloat[B](root0: Node[Float,B], sic0: Int) extends FatLeafTree[Float,B](root0, sic0) with Ordering.FloatOrdering {
    def cloneImpl() = new DefaultFloat(frozenRoot, sizeIfCached)
  }
  class DefaultLong[B](root0: Node[Long,B], sic0: Int) extends FatLeafTree[Long,B](root0, sic0) with Ordering.LongOrdering {
    def cloneImpl() = new DefaultLong(frozenRoot, sizeIfCached)
  }
  class DefaultDouble[B](root0: Node[Double,B], sic0: Int) extends FatLeafTree[Double,B](root0, sic0) with Ordering.DoubleOrdering {
    def cloneImpl() = new DefaultDouble(frozenRoot, sizeIfCached)
  }
  class Generic[A,B](root0: Node[A,B], sic0: Int, cmp: Ordering[A]) extends FatLeafTree[A,B](root0, sic0)  {
    def compare(lhs: A, rhs: A): Int = cmp.compare(lhs, rhs)
    def cloneImpl() = new Generic(frozenRoot, sizeIfCached, cmp)
  }

}

abstract class FatLeafTree[@specialized A,B](root0: FatLeafTree.Node[A,B], private var _cachedSize: Int) extends FatLeafTree.Branch[A,B](
    null, -1, null.asInstanceOf[A], null.asInstanceOf[B], null, root0) with Ordering[A] {

  import FatLeafTree._

  //////// abstract members

  def cloneImpl(): FatLeafTree[A,B]
  //def compare(lhs: A, rhs: A): Int

  //////// public interface

  override def clone(): FatLeafTree[A,B] = cloneImpl()

  def isEmpty: Boolean = isEmpty(right)
  def size: Int = sizeImpl
  def sizeIfCached: Int = _cachedSize

  def firstKey: A = firstKey(right)
  def lastKey: A = lastKey(right)
  def contains(k: A): Boolean = contains(right, k)
  def get(k: A): Option[B] = get(right, k)

  def put(k: A, v: B): Option[B] = put(unsharedRight(this), k, v)
  def remove(k: A): Option[B] = remove(unsharedRight(this), k)

  def removeLT(k: A) { _cachedSize = -1 ; removeLT(unsharedRight(this), k) }
  def removeLE(k: A) { _cachedSize = -1 ; removeLE(unsharedRight(this), k) }
  def removeGE(k: A) { _cachedSize = -1 ; removeGE(unsharedRight(this), k) }
  def removeGT(k: A) { _cachedSize = -1 ; removeGT(unsharedRight(this), k) }

  def frozenRoot: Node[A,B] = markShared(right)

  //////// internal machinery

  private type Nd = Node[A,B]
  private type Lf = Leaf[A,B]
  private type Br = Branch[A,B]

  //////// size

  private def isEmpty(n: Nd): Boolean = n match {
    case t: Lf => t.size > 0
    case _ => true
  }

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
      if (i >= 0) Some(t.values(i)) else None
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
      val z = t.values(i)
      t.values(i) = v
      Some(z)
    } else {
      leafInsert(t, ~i, k, v)
      if (_cachedSize >= 0)
        _cachedSize += 1
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
    System.arraycopy(t.keys, i, t.keys, i + 1, num - i)
    System.arraycopy(t.values, i, t.values, i + 1, num - i)
    t.size = num + 1

    // copy the values
    t.keys(i) = k
    t.values(i) = v

    // split if necessary
    if (num + 1 == LeafMax)
      split(t)
  }

  private def split(tL: Lf) {
    val leftSize = LeafMax / 2
    val rightSize = LeafMax - 1 - leftSize

    // existing terminal becomes left leaf, create new branch
    val b = new Br(tL.parent, 2, tL.keys(leftSize), tL.values(leftSize), tL, null)
    val tR = new Lf(b, rightSize, tL.keys.clone(), tL.values.clone())
    b.right = tR

    // copy to right
    System.arraycopy(tL.keys, leftSize + 1, tR.keys, 0, rightSize)
    System.arraycopy(tL.values, leftSize + 1, tR.values, 0, rightSize)
    clear(tR, rightSize, LeafMax - rightSize)

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
        val z = b.value
        copyAndRemoveMax(b, unsharedLeft(b))
        if (_cachedSize >= 0)
          _cachedSize -= 1
        return Some(z)
      } else {
        remove(if (c < 0) unsharedLeft(b) else unsharedRight(b), k)
      }
    }
  }

  private def leafRemove(t: Lf, k: A): Option[B] = {
    val i = keySearch(t, k)
    if (i >= 0) {
      val z = t.values(i)
      leafRemoveByIndex(t, i)
      if (_cachedSize >= 0)
        _cachedSize -= 1
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
        target.value = t.values(i)
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
      tL.values(LeafMin - 1) = b.value
      tL.size = LeafMin
      b.key = tR.keys(0)
      b.value = tR.values(0)
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
      b.value = tL.values(tL.size - 1)
      leafRemoveMax(tL)
    }
  }

  private def merge(b: Br, tL: Lf, tR: Lf) {
    tL.keys(tL.size) = b.key
    tL.values(tL.size) = b.value
    System.arraycopy(tR.keys, 0, tL.keys, tL.size + 1, tR.size)
    System.arraycopy(tR.values, 0, tL.values, tL.size + 1, tR.size)
    tL.size += 1 + tR.size
    tL.parent = b.parent

    replaceAndRepair(b, tL)
  }

  //////// bulk removal

  @tailrec private def removeLT(n: Nd, k: A) {
    n match {
      case t: Lf => {
        val i = keySearch(t, k)
        if (i >= 0)
          leafRemoveByIndex(t, 0, i)
        else
          leafRemoveByIndex(t, 0, ~i)
      }
      case b: Br => {
        val c = compare(k, b.key)
        if (c < 0) {
          removeLT(unsharedLeft(b), k)
        } else {
          val nR = unsharedRight(b)
          nR.parent = b.parent
          replaceAndRepair(b, nR)
          if (c == 0)
            put(nR, b.key, b.value)
          else
            removeLT(nR, k)
        }
      }
    }
  }

  @tailrec private def removeLE(n: Nd, k: A) {
    n match {
      case t: Lf => {
        val i = keySearch(t, k)
        if (i >= 0)
          leafRemoveByIndex(t, 0, i + 1)
        else
          leafRemoveByIndex(t, 0, ~i)
      }
      case b: Br => {
        val c = compare(k, b.key)
        if (c < 0) {
          removeLE(unsharedLeft(b), k)
        } else {
          val nR = unsharedRight(b)
          nR.parent = b.parent
          replaceAndRepair(b, nR)
          if (c > 0)
            removeLE(nR, k)
        }
      }
    }
  }

  @tailrec private def removeGE(n: Nd, k: A) {
    n match {
      case t: Lf => {
        val i = keySearch(t, k)
        if (i >= 0)
          leafRemoveByIndex(t, i, t.size)
        else
          leafRemoveByIndex(t, ~i, t.size)
      }
      case b: Br => {
        val c = compare(k, b.key)
        if (c <= 0) {
          val nL = unsharedLeft(b)
          nL.parent = b.parent
          replaceAndRepair(b, nL)
          if (c < 0)
            removeGE(nL, k)
        } else {
          removeGE(unsharedRight(b), k)
        }
      }
    }
  }

  @tailrec private def removeGT(n: Nd, k: A) {
    n match {
      case t: Lf => {
        val i = keySearch(t, k)
        if (i >= 0)
          leafRemoveByIndex(t, i + 1, t.size)
        else
          leafRemoveByIndex(t, ~i, t.size)
      }
      case b: Br => {
        val c = compare(k, b.key)
        if (c <= 0) {
          val nL = unsharedLeft(b)
          nL.parent = b.parent
          replaceAndRepair(b, nL)
          if (c < 0)
            removeGT(nL, k)
          else
            put(nL, b.key, b.value)
        } else {
          removeGT(unsharedRight(b), k)
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

  private def unsharedLeft(b: Br): Nd = {
    if (b.left.parent == null)
      b.left = unshare(b.left, b)
    b.left
  }

  private def unsharedRight(b: Br): Nd = {
    if (b.right.parent == null)
      b.right = unshare(b.right, b)
    b.right
  }

  private def unshare(n: Nd, p: Br): Nd = n match {
    case t: Lf =>
      // TODO: manifest?
      new Lf(p, t.size, t.keys.clone(), t.values.clone())
    case b: Br =>
      markShared(b.left)
      markShared(b.right)
      new Br(p, b.height, b.key, b.value, b.left, b.right)
  }

  private def markShared(n: Nd): Nd = {
    if (n.parent != null)
      n.parent = null
    n
  }

  //////// AVL rebalancing

  private def height(n: Nd) = n match {
    case b: Br => b.height
    case _ => 1
  }

  private def balance(n: Nd) = n match {
    case b: Br => height(b.left) - height(b.right)
    case _ => 0
  }

  private def repair(b: Br) {
    val h0 = b.height

    // no repair for the root holder
    if (h0 < 0)
      return

    val hL = height(b.left)
    val hR = height(b.right)
    val bal = hL - hR
    if (bal > 1) {
      // Left is too large, rotate right.  If left.right is larger than
      // left.left then rotating right will lead to a -2 balance, so
      // first we have to rotateLeft on left.
      replaceAndMaybeRepair(b, h0, if (balance(b.left) < 0) rotateRightOverLeft(b) else rotateRight(b))
      // TODO: multi-repair right
    } else if (bal < -1) {
      replaceAndMaybeRepair(b, h0, if (balance(b.right) > 0) rotateLeftOverRight(b) else rotateLeft(b))
      // TODO: multi-repair left
    } else {
      // no rotations needed, just repair height
      val h = 1 + math.max(hL, hR)
      if (h != h0) {
        b.height = h
        repair(b.parent)
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

    b.height = 1 + math.max(height(b.left), height(b.right))
    nL.height = 1 + math.max(height(nL.left), b.height)

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

    b.height = 1 + math.max(height(b.right), height(b.left))
    nR.height = 1 + math.max(height(nR.right), b.height)

    nR
  }

  private def rotateLeftOverRight(b: Br): Br = {
    b.right = rotateRight(unsharedRight(b).asInstanceOf[Br])
    rotateLeft(b)
  }

//  //////// enumeration
//
//  def foreach(block: ((A,B)) => Unit) { foreach(right, block) }
//
//  def foreach(n: Nd, block: ((A,B)) => Unit): Unit = n match {
//    case b: Br => {
//      foreach(b.left, block)
//      block((b.key, b.value))
//      foreach(b.right, block)
//    }
//    case t: Lf => {
//      var i = 0
//      while (i < t.size) { block((t.keys(i), t.values(i))) ; i += 1 }
//    }
//  }
//
//  def elements: Iterator[(A,B)] = new Iterator[(A,B)] {
//    private val stack = new Array[Nd](height(right))
//    private var depth = 0
//    private var index = 0
//
//    if (_size > 0) pushMin(right)
//
//    @tailrec final def pushMin(n: Nd) {
//      stack(depth) = n
//      depth += 1
//      n match {
//        case b: Br => pushMin(b.left)
//        case _ => {}
//      }
//    }
//
//    private def advance(): Unit = stack(depth - 1) match {
//      case b: Br => {
//        // pop current node
//        depth -= 1
//        pushMin(b.right)
//      }
//      case t: Lf => {
//        if (index + 1 < t.size) {
//          // more entries in this node
//          index += 1
//        } else {
//          index = 0
//          // no children, so just pop
//          depth -= 1
//          stack(depth) = null
//        }
//      }
//    }
//
//    def hasNext = depth > 0
//
//    def next = {
//      if (depth == 0) throw new IllegalStateException
//      val z = stack(depth - 1) match {
//        case b: Br => (b.key, b.value)
//        case t: Lf => (t.keys(index), t.values(index))
//      }
//      advance()
//      z
//    }
//  }
}