package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

object ListLemmas {
  def associativeToListL[T, M](
      l1: List[Node[T, M]],
      l2: List[Node[T, M]],
      depth: BigInt
  )(implicit m: Measure[T, M]): Boolean = {
    require(
      depth >= 0
        && l1.forall(_.isWellFormed(depth))
        && l2.forall(_.isWellFormed(depth))
    )
    forallConcat(l1, l2, _.isWellFormed(depth))
    Helpers.toListL(l1 ++ l2, depth) ==
      Helpers.toListL(l1, depth) ++ Helpers.toListL(l2, depth) because {
        l1 match {
          case Cons(h, t) =>
            associativeToListL(t, l2, depth)
            associativeConcat(
              h.toListL(depth),
              Helpers.toListL(t, depth),
              Helpers.toListL(l2, depth)
            )
          case Nil() => Helpers.toListL(l1, depth) == Nil[T]()
        }
      }
  }.holds

  def associativeToListR[T, M](
      l1: List[Node[T, M]],
      l2: List[Node[T, M]],
      depth: BigInt
  )(implicit m: Measure[T, M]): Boolean = {
    require(
      depth >= 0
        && l1.forall(_.isWellFormed(depth))
        && l2.forall(_.isWellFormed(depth))
    )
    forallConcat(l1, l2, _.isWellFormed(depth))
    Helpers.toListR(l1 ++ l2, depth) ==
      Helpers.toListR(l2, depth) ++ Helpers.toListR(l1, depth) because {
        l1 match {
          case Cons(h, t) =>
            associativeToListR(t, l2, depth)
            associativeConcat(
              Helpers.toListR(l2, depth),
              Helpers.toListR(t, depth),
              h.toListR(depth)
            )
          case Nil() => Helpers.toListR(l1, depth) == Nil[T]()
        }
      }
  }.holds

  def associativeConcat[T](
      l1: List[T],
      l2: List[T],
      l3: List[T]
  ): Boolean = {
    (l1 ++ l2) ++ l3 == l1 ++ (l2 ++ l3) because {
      l1 match {
        case Nil()      => trivial
        case Cons(h, t) => associativeConcat(t, l2, l3)
      }
    }
  }.holds

  def associativeConcat[T](
      l1: List[T],
      l2: List[T],
      l3: List[T],
      l4: List[T]
  ): Boolean = {
    val res = (l1 ++ l2) ++ (l3 ++ l4)
    res == ((l1 ++ l2) ++ l3) ++ l4
    && res == (l1 ++ (l2 ++ l3)) ++ l4
    && res == l1 ++ ((l2 ++ l3) ++ l4)
    && res == l1 ++ (l2 ++ (l3 ++ l4)) because {
      l1 match {
        case Nil()      => associativeConcat(l2, l3, l4)
        case Cons(h, t) => associativeConcat(t, l2, l3, l4)
      }
    }
  }.holds

  def forallConcat[T](
      l1: List[T],
      l2: List[T],
      p: T => Boolean
  ): Boolean = {
    require(l1.forall(p) && l2.forall(p))
    (l1 ++ l2).forall(p) because {
      l1 match {
        case Nil()      => l2.forall(p)
        case Cons(h, t) => p(h) && forallConcat(t, l2, p)
      }
    }
  }.holds

  def lastConcat[T](l1: List[T], l2: List[T]): Boolean = {
    require(!l2.isEmpty)
    (l1 ++ l2).lastOption == l2.lastOption because {
      l1 match {
        case Nil()      => l1 ++ l2 == l2
        case Cons(h, t) => lastConcat(t, l2)
      }
    }
  }.holds

  def headConcat[T](l1: List[T], l2: List[T]): Boolean = {
    require(!l1.isEmpty)
    (l1 ++ l2).head == l1.head
  }.holds

  def tailConcat[T](l1: List[T], l2: List[T]): Boolean = {
    require(!l1.isEmpty)
    (l1 ++ l2).tail == l1.tail ++ l2
  }.holds

  def appendConcat[T](l1: List[T], l2: List[T], e: T): Boolean = {
    l1 ++ (l2 :+ e) == (l1 ++ l2) :+ e because {
      l1 match {
        case Cons(h, t) => appendConcat(t, l2, e)
        case Nil()      => trivial
      }
    }
  }.holds

  def reverseAppend[T](l1: List[T], e: T): Boolean = {
    (l1 :+ e).reverse == e :: l1.reverse because {
      l1 match {
        case Cons(h, t) => reverseAppend(t, e)
        case Nil()      => trivial
      }
    }
  }.holds

  def reverseSymetry[T](l1: List[T]): Boolean = {
    l1.reverse.reverse == l1 because {
      l1 match {
        case Cons(h, t) =>
          reverseSymetry(t)
          reverseAppend(t.reverse, h)
        case Nil() => trivial
      }
    }
  }.holds

  def reverseConcat[T](l1: List[T], l2: List[T]): Boolean = {
    (l1 ++ l2).reverse == l2.reverse ++ l1.reverse because {
      l1 match {
        case Cons(h, t) =>
          appendConcat(l2.reverse, t.reverse, h)
          reverseConcat(t, l2)
        case Nil() => trivial
      }
    }
  }.holds

  def appendLast[T](l: List[T], e: T): Boolean = {
    (l :+ e).lastOption == Some[T](e) because {
      l match {
        case Nil()      => trivial
        case Cons(_, t) => appendLast(t, e)
      }
    }
  }.holds

  def reverseHead[T](l: List[T]): Boolean = {
    l.reverse.lastOption == l.headOption because {
      l match {
        case Cons(h, t) =>
          check(l.reverse == t.reverse :+ h)
          appendLast(t.reverse, h)
        case Nil() => trivial
      }
    }
  }.holds
}

object FingerTreeLemmas {
  def nodesToListRReverse[T, M](node: Node[T, M], depth: BigInt)(implicit
      m: Measure[T, M]
  ): Boolean = {
    require(depth >= 0 && node.isWellFormed(depth))
    node.toListL(depth) == node.toListR(depth).reverse because
      ListLemmas.reverseSymetry(node.toListL(depth))
  }.holds

  def nodeListToListRReverse[T, M](
      elems: List[Node[T, M]],
      depth: BigInt
  )(implicit m: Measure[T, M]): Boolean = {
    require(depth >= 0 && elems.forall(_.isWellFormed(depth)))
    Helpers.toListL(elems, depth) ==
      Helpers.toListR(elems, depth).reverse because
      ListLemmas.reverseSymetry(Helpers.toListL(elems, depth))
  }.holds

  def digitToListRReverse[T, M](digit: Digit[T, M], depth: BigInt)(implicit
      m: Measure[T, M]
  ): Boolean = {
    require(depth >= 0 && digit.isWellFormed(depth))
    digit.toListL(depth) == digit.toListR(depth).reverse because
      ListLemmas.reverseSymetry(digit.toListL(depth))
  }.holds

  def treeToListRReverse[T, M](
      tree: FingerTree[T, M],
      depth: BigInt
  )(implicit m: Measure[T, M]): Boolean = {
    require(depth >= 0 && tree.isWellFormed(depth))
    tree.toListL(depth) == tree.toListR(depth).reverse because
      ListLemmas.reverseSymetry(tree.toListL(depth))
  }.holds

  def headTailConcatL[T, M](digit: Digit[T, M], depth: BigInt)(implicit
      m: Measure[T, M]
  ): Boolean = {
    require(depth >= 0 && digit.isWellFormed(depth))
    val tailList = digit.tailL(depth) match {
      case Some(tail) => tail.toListL(depth)
      case None()     => List()
    }
    digit.toListL(depth) ==
      digit.headL(depth).toListL(depth) ++ tailList because {
        digit match {
          case Digit1(a)    => trivial
          case Digit2(a, b) => trivial
          case Digit3(a, b, c) =>
            ListLemmas.associativeConcat(
              a.toListL(depth),
              b.toListL(depth),
              c.toListL(depth)
            )
          case Digit4(a, b, c, d) =>
            ListLemmas.associativeConcat(
              a.toListL(depth),
              b.toListL(depth),
              c.toListL(depth),
              d.toListL(depth)
            )
        }
      }
  }.holds

  def headTailConcatR[T, M](digit: Digit[T, M], depth: BigInt)(implicit
      m: Measure[T, M]
  ): Boolean = {
    require(depth >= 0 && digit.isWellFormed(depth))
    val tailList = digit.tailR(depth) match {
      case Some(tail) => tail.toListR(depth)
      case None()     => List()
    }
    digit.toListR(depth) ==
      digit.headR(depth).toListR(depth) ++ tailList because {
        digit match {
          case Digit1(a)    => trivial
          case Digit2(a, b) => trivial
          case Digit3(a, b, c) =>
            ListLemmas.associativeConcat(
              c.toListR(depth),
              b.toListR(depth),
              a.toListR(depth)
            )
          case Digit4(a, b, c, d) =>
            ListLemmas.associativeConcat(
              d.toListR(depth),
              c.toListR(depth),
              b.toListR(depth),
              a.toListR(depth)
            )
        }
      }
  }.holds
}
