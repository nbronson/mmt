package mmt.experimental

import util.Random
import math.Ordering
import java.lang.String

// PPTreap

object PPTreap {
  val rand = new Random

  abstract class Thunk[A,B] {
    def prio: Int
    def force(implicit cmp: Ordering[A]): Option[Concrete[A,B]]
    def render(prefix: String)

    def get(k: A)(implicit cmp: Ordering[A]): Option[B] = force match {
      case None => None
      case Some(ch) => ch.get(k)
    }

    def put(k: A, v: B)(implicit cmp: Ordering[A]): Thunk[A,B] = force match {
      case None => new Concrete(rand.nextInt, new Empty[A,B], new Empty[A,B], k, v)
      case Some(ch) => ch.put(k, v)
    }
  }

  class Concrete[A,B](val prio: Int, val left: Thunk[A,B], val right: Thunk[A,B], val key: A, val value: B) extends Thunk[A,B] {
    def force(implicit cmp: Ordering[A]): Option[Concrete[A, B]] = Some(this)

    override def get(k: A)(implicit cmp: Ordering[A]): Option[B] = {
      val c = cmp.compare(k, key)
      if (c < 0)
        left.get(k)
      else if (c > 0)
        right.get(k)
      else
        Some(value)
    }

    override def put(k: A, v: B)(implicit cmp: Ordering[A]): Thunk[A,B] = {
      val c = cmp.compare(k, key)
      val z = if (c < 0)
        new Concrete(prio, left.put(k, v), right, key, value)
      else if (c > 0)
        new Concrete(prio, left, right.put(k, v), key, value)
      else
        new Concrete(prio, left, right, key, v)
      z.balance
    }

    private def balance(implicit cmp: Ordering[A]): Concrete[A,B] = {
      if (left.prio > prio) {
        // rotate right
        rotateRight
      } else if (right.prio > prio) {
        // rotate left
        rotateLeft
      } else {
        // no change
        this
      }
    }

    private def rotateRight(implicit cmp: Ordering[A]): Concrete[A,B] = left.force match {
      case None => this
      case Some(x) => new Concrete(x.prio, x.left, new Concrete(prio, x.right, right, key, value).balance, x.key, x.value) // TODO: is this .balance needed?
    }

    private def rotateLeft(implicit cmp: Ordering[A]): Concrete[A,B] = right.force match {
      case None => this
      case Some(x) => new Concrete(x.prio, new Concrete(prio, left, x.left, key, value).balance, x.right, x.key, x.value) // TODO: is this .balance needed?
    }

    def render(prefix: String) {
      println(prefix + "(" + key + "," + value + ", prio=" + prio)
      left.render(prefix + "  ")
      right.render(prefix + "  ")
    }
  }

  class Empty[A,B] extends Thunk[A,B] {
    def prio = Int.MinValue
    def force(implicit cmp: Ordering[A]) = None
    def render(prefix: String) {
      println(prefix + "NIL")
    }
  }

  abstract class CachingThunk[A,B] extends Thunk[A,B] {
    protected def forceImpl(implicit cmp: Ordering[A]): Option[Concrete[A,B]]
    protected def renderImpl(prefix: String)

    @volatile private var cache: Option[Concrete[A,B]] = null

    final def force(implicit cmp: Ordering[A]): Option[Concrete[A,B]] = {
      var z = cache
      if (z == null) {
        this.synchronized {
          z = cache
          if (z == null) {
            z = forceImpl
            cache = z
          }
        }
      }
      z
    }

    final def render(prefix: String) {
      cache match {
        case null => renderImpl(prefix)
        case None => println(prefix + "empty forced " + getClass.getSimpleName)
        case Some(ch) => {
          println(prefix + "forced " + getClass.getSimpleName)
          ch.render(prefix + "  ")
        }
      }
    }
  }

  class LessThan[A,B](max: A, x: Thunk[A,B]) extends CachingThunk[A,B] {
    def prio = x.prio

    protected def forceImpl(implicit cmp: Ordering[A]) = x.force match {
      case None => None
      case Some(ch) => {
        if (cmp.compare(ch.key, max) < 0)
          Some(new Concrete(ch.prio, ch.left, new LessThan(max, ch.right), ch.key, ch.value))
        else
          new LessThan(max, ch.left).force
      }
    }

    protected def renderImpl(prefix: String) {
      println(prefix + "< " + max)
      x.render(prefix + "  ")
    }
  }

  class GreaterThan[A,B](min: A, x: Thunk[A,B]) extends CachingThunk[A,B] {
    def prio = x.prio

    protected def forceImpl(implicit cmp: Ordering[A]) = x.force match {
      case None => None
      case Some(ch) => {
        if (cmp.compare(ch.key, min) > 0)
          Some(new Concrete(ch.prio, new GreaterThan(min, ch.left), ch.right, ch.key, ch.value))
        else
          new GreaterThan(min, ch.right).force
      }
    }

    protected def renderImpl(prefix: String) {
      println(prefix + "> " + min)
      x.render(prefix + "  ")
    }
  }

  class PutAll[A,B](x: Thunk[A,B], y: Thunk[A,B]) extends CachingThunk[A,B] {
    val prio = x.prio max y.prio
    
    protected def forceImpl(implicit cmp: Ordering[A]) = x.force match {
      case None => y.force
      case Some(xx) => y.force match {
        case None => Some(xx)
        case Some(yy) => {
          val left = new PutAll(new LessThan(yy.key, xx), yy.left)
          val right = new PutAll(new GreaterThan(yy.key, xx), yy.right)
          Some(new Concrete(yy.prio, left, right, yy.key, yy.value))
        }
      }
    }

    protected def renderImpl(prefix: String) {
      println(prefix + "+")
      x.render(prefix + "  ")
      y.render(prefix + "  ")
    }
  }
}

class PPTreap[A,B](implicit cmp: Ordering[A]) {
  import PPTreap._

  var root: Thunk[A,B] = new Empty[A,B]

  def get(k: A): Option[B] = root.get(k)

  def put(k: A, v: B) {
    root = root.put(k, v)
  }

  def putAll(rhs: PPTreap[A,B]) {
    root = new PutAll(root, rhs.root)
  }

  def render {
    root.render("")
  }
}