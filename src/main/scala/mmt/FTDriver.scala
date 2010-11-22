package mmt

// Main

private[mmt] object FLTester {
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

  def Range = 1000
  def InitialGetPct = 50
  def GetPct = 50 // 70 //95
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

  def test[@specialized A](name: String, rand: scala.util.Random, keyGen: () => A)(
          implicit cmp: Ordering[A], am: ClassManifest[A]) {
    val (abest,aavg) = testFLTreeMap(rand, keyGen)
    val (bbest,bavg) = testJavaTree(rand, keyGen)
    println(name + ": FLTreeMap: " + abest + " nanos/op (" + aavg + " avg),  " +
            "java.util.TreeMap: " + bbest + " nanos/op (" + bavg + " avg)")
  }

  def testFLTreeMap[@specialized A](rand: scala.util.Random, keyGen: () => A)(
          implicit cmp: Ordering[A], am: ClassManifest[A]): (Long,Long) = {
    val tt0 = System.currentTimeMillis
    val m = new mutable.FLTreeMap[A,String]
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
          //m.tree.validateTree
        } else if (pct < gp + IterPct) {
          // iterate
          var n = 0
          //for (e <- m.elements) n += 1
          for (e <- m) n += 1
          assert(n == m.size)
          //m.tree.validateTree
        } else if (pct < 50 + (gp + IterPct) / 2) {
          m(key) = "abc"
          //m.tree.validateTree
        } else {
          m -= key
          //m.tree.validateTree
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

  def testJavaTree[@specialized A](rand: scala.util.Random, keyGen: () => A)(implicit cmp: Ordering[A], am: ClassManifest[A]): (Long,Long) = {
    val tt0 = System.currentTimeMillis
    val m = new java.util.TreeMap[A,String](if (am.erasure.isInstanceOf[Comparable[_]]) null else cmp)
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
