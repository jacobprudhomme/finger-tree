package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

// Helper functions
object Helpers {
  def toListL[T](elems: List[Node[T]], depth: BigInt): List[T] = {
    require(depth >= 0 && elems.forall(_.isWellFormed(depth)))
    elems match {
      case Cons(head, tail) =>
        ListLemmas.reverseConcat(head.toListL(depth), toListL(tail, depth))
        head.toListL(depth) ++ toListL(tail, depth)
      case Nil() => Nil()
    }
  }.ensuring(res => res.reverse == toListR(elems, depth))

  def toListR[T](elems: List[Node[T]], depth: BigInt): List[T] = {
    require(depth >= 0 && elems.forall(_.isWellFormed(depth)))
    elems match {
      case Cons(head, tail) => toListR(tail, depth) ++ head.toListR(depth)
      case Nil()            => Nil()
    }
  }

  def toNodes[T](elems: List[Node[T]], depth: BigInt): List[Node[T]] = {
    require(
      depth >= 0
        && elems.size >= 2
        && elems.forall(_.isWellFormed(depth))
    )
    elems match {
      case Nil()                   => ???
      case Cons(a, Nil())          => ???
      case Cons(a, Cons(b, Nil())) => List(Node2(a, b))
      case Cons(a, Cons(b, Cons(c, Nil()))) =>
        ListLemmas.associativeConcat(
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth)
        )
        List[Node[T]](Node3(a, b, c))
      case Cons(a, Cons(b, Cons(c, Cons(d, Nil())))) =>
        ListLemmas.associativeConcat(
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth),
          d.toListL(depth)
        )
        ListLemmas.associativeConcat(
          d.toListR(depth),
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )
        check(
          toListL(Cons(c, Cons(d, Nil())), depth) ==
            c.toListL(depth) ++ d.toListL(depth)
        )
        check(
          toListR(Cons(c, Cons(d, Nil())), depth) ==
            d.toListR(depth) ++ c.toListR(depth)
        )
        List[Node[T]](Node2(a, b), Node2(c, d))
      case Cons(a, Cons(b, Cons(c, tail))) => {
        ListLemmas.associativeConcat(
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth),
          toListL(tail, depth)
        )
        ListLemmas.associativeConcat(
          toListR(tail, depth),
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )
        Cons(Node3(a, b, c), toNodes(tail, depth))
      }
    }
  }.ensuring(res =>
    res.forall(_.isWellFormed(depth + 1))
      && toListL(res, depth + 1) == toListL(elems, depth)
      && toListR(res, depth + 1) == toListR(elems, depth)
  )

  def deepL[T](
      prefixTail: Option[Digit[T]],
      spine: FingerTree[T],
      suffix: Digit[T],
      depth: BigInt
  ): FingerTree[T] = {
    require(
      depth >= 0
        && spine.isWellFormed(depth + 1)
        && prefixTail.forall(_.isWellFormed(depth))
        && suffix.isWellFormed(depth)
    )
    prefixTail match {
      case Some(digit) =>
        Deep(digit, spine, suffix)
      case None() =>
        spine match {
          case Empty()       => suffix.toTree(depth)
          case Single(value) => Deep(value.toDigit(depth + 1), Empty(), suffix)
          case Deep(spinePrefix, spineSpine, spineSuffix) =>
            val prefix = spinePrefix.tailL(depth + 1) match {
              case Some(pref) => pref.toListL(depth + 1)
              case None()     => List()
            }
            FingerTreeLemmas.headTailConcatL(spinePrefix, depth + 1)
            ListLemmas.associativeConcat(
              spinePrefix.headL(depth + 1).toListL(depth + 1),
              prefix,
              spineSpine.toListL(depth + 2),
              spineSuffix.toListL(depth + 1)
            )
            Deep(
              spinePrefix.headL(depth + 1).toDigit(depth + 1),
              deepL(
                spinePrefix.tailL(depth + 1),
                spineSpine,
                spineSuffix,
                depth + 1
              ),
              suffix
            )
        }
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && {
        val prefix = prefixTail match {
          case Some(pref) => pref.toListL(depth)
          case None()     => List()
        }
        res.toListL(depth) ==
          prefix ++ spine.toListL(depth + 1) ++ suffix.toListL(depth)
      }
  )

  def deepR[T](
      prefix: Digit[T],
      spine: FingerTree[T],
      suffixTail: Option[Digit[T]],
      depth: BigInt
  ): FingerTree[T] = {
    require(
      depth >= 0
        && spine.isWellFormed(depth + 1)
        && prefix.isWellFormed(depth)
        && suffixTail.forall(_.isWellFormed(depth))
    )
    suffixTail match {
      case Some(digit) => Deep(prefix, spine, digit)
      case None() =>
        spine match {
          case Empty()       => prefix.toTree(depth)
          case Single(value) => Deep(prefix, Empty(), value.toDigit(depth + 1))
          case Deep(spinePrefix, spineSpine, spineSuffix) =>
            val suffix = spineSuffix.tailR(depth + 1) match {
              case Some(suff) => suff.toListR(depth + 1)
              case None()     => List()
            }
            FingerTreeLemmas.headTailConcatR(spineSuffix, depth + 1)
            ListLemmas.associativeConcat(
              spineSuffix.headR(depth + 1).toListR(depth + 1),
              suffix,
              spineSpine.toListR(depth + 2),
              spinePrefix.toListR(depth + 1)
            )
            Deep(
              prefix,
              deepR(
                spinePrefix,
                spineSpine,
                spineSuffix.tailR(depth + 1),
                depth + 1
              ),
              spineSuffix.headR(depth + 1).toDigit(depth + 1)
            )
        }
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && {
        val suffix = suffixTail match {
          case Some(suff) => suff.toListR(depth)
          case None()     => List()
        }
        res.toListR(depth) ==
          suffix ++ spine.toListR(depth + 1) ++ prefix.toListR(depth)
      }
  )

}
