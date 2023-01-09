package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

/// This file defines the data structure for the digits in a finger tree, which
/// represent a special case at the top level of the 2-3 trees (Nodes[T]) composing
/// a finger tree. These top levels can optionally have 1 or 4 children, which we'll
/// call segments, to make operations on the finger tree simpler. The case classes
/// of Digit[T] are found at the end of the file.

private sealed trait Digit[T]:

  /// ***INVARIANT AND PROOF HELPER FUNCTIONS*** ///

  /// Applies a predicate to each segment of the digit
  def forall(p: Node[T] => Boolean): Boolean =
    this match {
      case Digit1(a)          => p(a)
      case Digit2(a, b)       => p(a) && p(b)
      case Digit3(a, b, c)    => p(a) && p(b) && p(c)
      case Digit4(a, b, c, d) => p(a) && p(b) && p(c) && p(d)
    }

  /// Checks the invariant that segment of the digit is a fully-balanced tree
  /// of the given depth
  def isWellFormed(depth: BigInt): Boolean = {
    require(depth >= 0)

    this.forall(_.isWellFormed(depth))
  }

  /// ***CONVERSION AND HELPER FUNCTIONS*** ///

  /// Gets first segment in a digit
  def headL(depth: BigInt): Node[T] = {
    require(depth >= 0 && this.isWellFormed(depth))

    this match {
      case Digit1(a)          => a
      case Digit2(a, _)       => a
      case Digit3(a, _, _)    => a
      case Digit4(a, _, _, _) => a
    }
  }.ensuring(res => res.isWellFormed(depth))

  /// Gets last segment in a digit
  def headR(depth: BigInt): Node[T] = {
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

  /// Produces a new digit with all the segments of the original except for the first
  def tailL(depth: BigInt): Option[Digit[T]] = {
    require(depth >= 0 && this.isWellFormed(depth))

    this match {
      case Digit1(_)          => None()
      case Digit2(_, b)       => Some(Digit1(b))
      case Digit3(_, b, c)    => Some(Digit2(b, c))
      case Digit4(_, b, c, d) => Some(Digit3(b, c, d))
    }
  }.ensuring(res => res.forall(_.isWellFormed(depth)))

  /// Produces a new digit with all the segments of the original except for the last
  def tailR(depth: BigInt): Option[Digit[T]] = {
    require(depth >= 0 && this.isWellFormed(depth))

    this match {
      case Digit1(_)          => None()
      case Digit2(a, _)       => Some(Digit1(a))
      case Digit3(a, b, _)    => Some(Digit2(a, b))
      case Digit4(a, b, c, _) => Some(Digit3(a, b, c))
    }
  }.ensuring(res => res.forall(_.isWellFormed(depth)))

  /// Converts a digit to a list of Node[T]'s, for easier proof ergonomics
  def toNodeList(depth: BigInt): List[Node[T]] = {
    require(depth >= 0 && this.isWellFormed(depth))
    decreases(this)

    this.tailL(depth) match {
      case None() => List(this.headL(depth))
      case Some(tail) => {
        FingerTreeLemmas.headTailConcatL(this, depth)

        Cons(this.headL(depth), tail.toNodeList(depth))
      }
    }
  }.ensuring(res =>
    !res.isEmpty
      && res.forall(_.isWellFormed(depth))
      && res == (this match {
        case Digit1(a)          => List[Node[T]](a)
        case Digit2(a, b)       => List[Node[T]](a, b)
        case Digit3(a, b, c)    => List[Node[T]](a, b, c)
        case Digit4(a, b, c, d) => List[Node[T]](a, b, c, d)
      })
      && Helpers.toListL(res, depth) == this.toListL(depth)
      && Helpers.toListR(res, depth) == this.toListR(depth)
  )

  /// Constructs a list from a node, according to an in-order traversal
  def toListL(depth: BigInt): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))

    this match {
      case Digit1(a) => a.toListL(depth)
      case Digit2(a, b) => {
        ListLemmas.reverseConcat(a.toListL(depth), b.toListL(depth))

        a.toListL(depth) ++ b.toListL(depth)
      }
      case Digit3(a, b, c) => {
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
      }
      case Digit4(a, b, c, d) => {
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
    }
  }.ensuring(res =>
    !res.isEmpty
      && res.reverse == this.toListR(depth)
  )

  /// Constructs a list from a node, according to a reversed in-order traversal
  def toListR(depth: BigInt): List[T] = {
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

  /// Constructs a simple one-level finger tree from a digit
  def toTree(depth: BigInt): FingerTree[T] = {
    require(depth >= 0 && this.isWellFormed(depth))

    this match {
      case Digit1(a)    => Single(a)
      case Digit2(a, b) => Deep(Digit1(a), Empty(), Digit1(b))
      case Digit3(a, b, c) => {
        ListLemmas.associativeConcat(
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )

        Deep(Digit2(a, b), Empty(), Digit1(c))
      }
      case Digit4(a, b, c, d) => {
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
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && !res.isEmpty(depth)
      && res.toListL(depth) == this.toListL(depth)
      && res.toListR(depth) == this.toListR(depth)
  )

/// A Digit[T] is either a:
/// - Digit1[T](Node[T]),
/// - Digit2[T](Node[T], Node[T]),
/// - Digit3[T](Node[T], Node[T], Node[T]), or
/// - Digit4[T](Node[T], Node[T], Node[T], Node[T])
private final case class Digit1[T](a: Node[T]) extends Digit[T]
private final case class Digit2[T](a: Node[T], b: Node[T]) extends Digit[T]
private final case class Digit3[T](a: Node[T], b: Node[T], c: Node[T])
    extends Digit[T]
private final case class Digit4[T](
    a: Node[T],
    b: Node[T],
    c: Node[T],
    d: Node[T]
) extends Digit[T]
