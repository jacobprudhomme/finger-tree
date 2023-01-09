package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

private sealed trait Digit[T, M]:
  def headL(depth: BigInt)(implicit m: Measure[T, M]): Node[T, M] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(a)          => a
      case Digit2(a, _)       => a
      case Digit3(a, _, _)    => a
      case Digit4(a, _, _, _) => a
    }
  }.ensuring(res => res.isWellFormed(depth))

  def headR(depth: BigInt)(implicit m: Measure[T, M]): Node[T, M] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(a)          => a
      case Digit2(_, b)       => b
      case Digit3(_, _, c)    => c
      case Digit4(_, _, _, d) => d
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && res == this.toNodeList(depth).last
  )

  def tailL(depth: BigInt)(implicit m: Measure[T, M]): Option[Digit[T, M]] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(_)          => None()
      case Digit2(_, b)       => Some(Digit1(b))
      case Digit3(_, b, c)    => Some(Digit2(b, c))
      case Digit4(_, b, c, d) => Some(Digit3(b, c, d))
    }
  }.ensuring(res => res.forall(_.isWellFormed(depth)))

  def tailR(depth: BigInt)(implicit m: Measure[T, M]): Option[Digit[T, M]] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(_)          => None()
      case Digit2(a, _)       => Some(Digit1(a))
      case Digit3(a, b, _)    => Some(Digit2(a, b))
      case Digit4(a, b, c, _) => Some(Digit3(a, b, c))
    }
  }.ensuring(res => res.forall(_.isWellFormed(depth)))

  // this is awful but stainless loves it
  def toNodeList(depth: BigInt)(implicit m: Measure[T, M]): List[Node[T, M]] = {
    require(depth >= 0 && this.isWellFormed(depth))
    decreases(this)
    this.tailL(depth) match {
      case None() => List(this.headL(depth))
      case Some(tail) =>
        FingerTreeLemmas.headTailConcatL(this, depth)
        Cons(this.headL(depth), tail.toNodeList(depth))
    }
  }.ensuring(res =>
    !res.isEmpty
      && res.forall(_.isWellFormed(depth))
      && res == (this match {
        case Digit1(a)          => List[Node[T, M]](a)
        case Digit2(a, b)       => List[Node[T, M]](a, b)
        case Digit3(a, b, c)    => List[Node[T, M]](a, b, c)
        case Digit4(a, b, c, d) => List[Node[T, M]](a, b, c, d)
      })
      && Helpers.toListL(res, depth) == this.toListL(depth)
      && Helpers.toListR(res, depth) == this.toListR(depth)
  )

  def toListL(depth: BigInt)(implicit m: Measure[T, M]): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(a) => a.toListL(depth)
      case Digit2(a, b) =>
        ListLemmas.reverseConcat(a.toListL(depth), b.toListL(depth))
        a.toListL(depth) ++ b.toListL(depth)
      case Digit3(a, b, c) =>
        ListLemmas.reverseConcat(a.toListL(depth), b.toListL(depth))
        ListLemmas.reverseConcat(
          a.toListL(depth) ++ b.toListL(depth),
          c.toListL(depth)
        )
        ListLemmas.associativeConcat(
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )
        a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth)
      case Digit4(a, b, c, d) =>
        ListLemmas.reverseConcat(a.toListL(depth), b.toListL(depth))
        ListLemmas.reverseConcat(
          a.toListL(depth) ++ b.toListL(depth),
          c.toListL(depth)
        )
        ListLemmas.reverseConcat(
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth),
          d.toListL(depth)
        )
        ListLemmas.associativeConcat(
          d.toListR(depth),
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )
        a.toListL(depth) ++ b.toListL(depth)
          ++ c.toListL(depth) ++ d.toListL(depth)
    }
  }.ensuring(res =>
    !res.isEmpty
      && res.reverse == this.toListR(depth)
  )

  def toListR(depth: BigInt)(implicit m: Measure[T, M]): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(a)    => a.toListR(depth)
      case Digit2(a, b) => b.toListR(depth) ++ a.toListR(depth)
      case Digit3(a, b, c) =>
        c.toListR(depth) ++ b.toListR(depth) ++ a.toListR(depth)
      case Digit4(a, b, c, d) =>
        d.toListR(depth) ++ c.toListR(depth)
          ++ b.toListR(depth) ++ a.toListR(depth)
    }
  }.ensuring(!_.isEmpty)

  def toTree(depth: BigInt)(implicit m: Measure[T, M]): FingerTree[T, M] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(a)    => Single(a)
      case Digit2(a, b) => Deep(Digit1(a), Empty(), Digit1(b))
      case Digit3(a, b, c) =>
        ListLemmas.associativeConcat(
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )
        Deep(Digit2(a, b), Empty(), Digit1(c))
      case Digit4(a, b, c, d) =>
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
        Deep(Digit2(a, b), Empty(), Digit2(c, d))
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && !res.isEmpty(depth)
      && res.toListL(depth) == this.toListL(depth)
      && res.toListR(depth) == this.toListR(depth)
  )

  def forall(p: Node[T, M] => Boolean)(implicit m: Measure[T, M]): Boolean = {
    this match
      case Digit1(a)          => p(a)
      case Digit2(a, b)       => p(a) && p(b)
      case Digit3(a, b, c)    => p(a) && p(b) && p(c)
      case Digit4(a, b, c, d) => p(a) && p(b) && p(c) && p(d)
  }
  def isWellFormed(depth: BigInt)(implicit m: Measure[T, M]): Boolean = {
    require(depth >= 0)
    this.forall(_.isWellFormed(depth))
  }

private final case class Digit1[T, M](a: Node[T, M]) extends Digit[T, M]
private final case class Digit2[T, M](a: Node[T, M], b: Node[T, M])
    extends Digit[T, M]
private final case class Digit3[T, M](
    a: Node[T, M],
    b: Node[T, M],
    c: Node[T, M]
) extends Digit[T, M]
private final case class Digit4[T, M](
    a: Node[T, M],
    b: Node[T, M],
    c: Node[T, M],
    d: Node[T, M]
) extends Digit[T, M]
