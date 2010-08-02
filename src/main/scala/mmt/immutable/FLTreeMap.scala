package mmt
package immutable

// FLTreeMap

import scala.collection.generic._
import scala.collection.{SortedMapLike, immutable}
import scala.math.Ordering
import scala.reflect.ClassManifest
import scala.collection.mutable.{ListBuffer, Builder}

object FLTreeMap {

  def empty[A : Ordering : ClassManifest, B] = new FLTreeMap[A, B]()

  def apply[A : Ordering : ClassManifest, B](elems: (A, B)*): FLTreeMap[A, B] = (newBuilder[A, B] ++= elems).result

  def newBuilder[A : Ordering : ClassManifest, B] = new Builder[(A, B), FLTreeMap[A, B]] {
    private val tree = FatLeafTree.empty[A, B]

    def clear() { tree.clear() }
    def result(): FLTreeMap[A, B] = { new FLTreeMap(tree.clone()) }
    def +=(elem: (A, B)): this.type = { tree.put(elem._1, elem._2) ; this }
  }

  class FLTreeMapCanBuildFrom[A : Ordering : ClassManifest, B] extends CanBuildFrom[FLTreeMap[_, _], (A, B), FLTreeMap[A, B]] {
    def apply(from: FLTreeMap[_, _]) = newBuilder[A, B]
    def apply() = newBuilder[A, B]
  }

  implicit def canBuildFrom[A : Ordering : ClassManifest, B]: CanBuildFrom[FLTreeMap[_, _], (A, B), FLTreeMap[A, B]] =
      new FLTreeMapCanBuildFrom[A, B]
}

class FLTreeMap[A, +B](private val tree: FatLeafTree[A, _ <: B])
    extends immutable.SortedMap[A, B]
    with SortedMapLike[A, B, FLTreeMap[A, B]]
    with immutable.MapLike[A, B, FLTreeMap[A, B]] {

  override protected[this] def newBuilder : Builder[(A, B), FLTreeMap[A, B]] = FLTreeMap.newBuilder[A, B]

  def this()(implicit ordering: Ordering[A], am: ClassManifest[A]) = this(FatLeafTree.empty[A, B])

  override def rangeImpl(from: Option[A], until: Option[A]): FLTreeMap[A, B] = {
    val t = tree.clone()
    for (k <- from) t.removeLT(k)
    for (k <- until) t.removeGE(k)
    new FLTreeMap(t)
  }

  override def firstKey = tree.firstKey
  override def lastKey = tree.lastKey
  override def compare(lhs: A, rhs: A): Int = tree.compare(lhs, rhs)
  implicit def ordering: Ordering[A] = tree.ordering
  private implicit def am: ClassManifest[A] = tree.am

  override def empty: FLTreeMap[A, B] = FLTreeMap.empty[A, B]

  override def updated[B1 >: B](key: A, value: B1): FLTreeMap[A, B1] = {
    val t = tree.clone().asInstanceOf[FatLeafTree[A, B1]]
    t.put(key, value)
    new FLTreeMap(t)
  }


  override def + [B1 >: B] (kv: (A, B1)): FLTreeMap[A, B1] = updated(kv._1, kv._2)

  override def + [B1 >: B] (elem1: (A, B1), elem2: (A, B1), elems: (A, B1)*): FLTreeMap[A, B1] = {
    val t = tree.clone().asInstanceOf[FatLeafTree[A, B1]]
    t.put(elem1._1, elem1._2)
    t.put(elem2._1, elem2._2)
    for (e <- elems) t.put(e._1, e._2)
    new FLTreeMap(t)
  }

  def insert[B1 >: B](key: A, value: B1): FLTreeMap[A, B1] = {
    val t = tree.clone().asInstanceOf[FatLeafTree[A, B1]]
    val prev = t.put(key, value)
    assert(prev.isEmpty)
    new FLTreeMap(t)
  }

  def - (key: A): FLTreeMap[A, B] = {
    if (!tree.contains(key))
      this
    else {
      val t = tree.clone()
      t.remove(key)
      new FLTreeMap(t)
    }
  }

  override def get(key: A): Option[B] = tree.get(key)

  def iterator: Iterator[(A, B)] = tree.iterator

  override def toList: List[(A, B)] = {
    val buf = new ListBuffer[(A, B)]
    tree.unstableForeach { (k, v) => buf += (k -> v) }
    buf.result
  }

  override def toStream: Stream[(A, B)] = tree.iterator.toStream

  override def foreach[U](f: ((A, B)) =>  U) = tree.stableForeach { (k, v) => f((k, v)) }
}




