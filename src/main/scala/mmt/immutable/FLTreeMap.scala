package mmt
package immutable

// FLTreeMap

import scala.collection.generic._
import collection.{TraversableOnce, SortedMapLike}
import math.Ordering
import collection.immutable.{List, MapLike, SortedMap}
import reflect.ClassManifest
import collection.mutable.{ArrayBuilder, ArrayBuffer, ListBuffer, Builder}

object FLTreeMap extends ImmutableSortedMapFactory[FLTreeMap] {

  def empty[A,B](implicit ord: Ordering[A]) = new FLTreeMap[A,B]()(ord)

  override def newBuilder[A,B](implicit ord: Ordering[A]) = new Builder[(A,B), FLTreeMap[A,B]] {
    private val tree = FatLeafTree.empty[A,B]

    def clear() { tree.clear() }
    def result(): FLTreeMap[A,B] = { tree.freeze() ; new FLTreeMap(tree) }
    def +=(elem: (A,B)): this.type = { tree.put(elem._1, elem._2) ; this }
  }

  implicit def canBuildFrom[A,B](implicit ord: Ordering[A]): CanBuildFrom[Coll, (A,B), FLTreeMap[A,B]] =
      new SortedMapCanBuildFrom[A,B]
}

class FLTreeMap[A,+B](private val tree: FatLeafTree[A,_ <: B])
    extends SortedMap[A,B]
    with SortedMapLike[A,B, FLTreeMap[A,B]]
    with MapLike[A,B, FLTreeMap[A,B]] {

  override protected[this] def newBuilder : Builder[(A,B), FLTreeMap[A,B]] = FLTreeMap.newBuilder[A,B]

  def this()(implicit ordering: Ordering[A]) = this(FatLeafTree.empty[A,B])

  override def rangeImpl(from: Option[A], until: Option[A]): FLTreeMap[A,B] = {
    val t = tree.clone()
    for (k <- from) t.removeLT(k)
    for (k <- until) t.removeGE(k)
    new FLTreeMap(t)
  }

  override def firstKey = tree.firstKey
  override def lastKey = tree.lastKey
  override def compare(lhs: A, rhs: A): Int = tree.compare(lhs, rhs)
  implicit def ordering: Ordering[A] = tree.ordering

  override def empty: FLTreeMap[A,B] = FLTreeMap.empty[A,B](tree.ordering)

  override def updated[B1 >: B](key: A, value: B1): FLTreeMap[A,B1] = {
    val t = tree.clone().asInstanceOf[FatLeafTree[A,B1]]
    t.put(key, value)
    new FLTreeMap(t)
  }

  override def + [B1 >: B] (kv: (A,B1)): FLTreeMap[A,B1] = updated(kv._1, kv._2)

  override def + [B1 >: B] (elem1: (A,B1), elem2: (A,B1), elems: (A,B1)*): FLTreeMap[A,B1] = {
    val t = tree.clone().asInstanceOf[FatLeafTree[A,B1]]
    t.put(elem1._1, elem1._2)
    t.put(elem2._1, elem2._2)
    for (e <- elems) t.put(e._1, e._2)
    new FLTreeMap(t)
  }

  def insert[B1 >: B](key: A, value: B1): FLTreeMap[A,B1] = {
    val t = tree.clone().asInstanceOf[FatLeafTree[A,B1]]
    val prev = t.put(key, value)
    assert(prev.isEmpty)
    new FLTreeMap(t)
  }

  def - (key: A): FLTreeMap[A,B] = {
    if (!tree.contains(key))
      this
    else {
      val t = tree.clone()
      t.remove(key)
      new FLTreeMap(t)
    }
  }

  override def get(key: A): Option[B] = tree.get(key)

  def iterator: Iterator[(A,B)] = tree.iterator

  override def toList: List[(A,B)] = {
    val buf = new ListBuffer[(A,B)]
    tree.unstableForeach { (k,v) => buf += (k -> v) }
    buf.result
  }

  override def toStream: Stream[(A,B)] = tree.iterator.toStream

  override def foreach[U](f: ((A,B)) =>  U) = tree.stableForeach { (k,v) => f((k, v)) }
}




