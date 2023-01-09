package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

/// This file defines the data structure for the nodes in a finger tree, which
/// represent fully-balanced 2-3 trees of a given depth, maintaining the invariant
/// for finger trees that the original polymorphically recursive type would have.
/// The case classes of Node[T] are found at the end of the file.

sealed trait Node[T]:

  /// ***INVARIANT FUNCTIONS*** ///

  /// Checks the invariant that the node is a fully-balanced tree of the given depth
  def isWellFormed(depth: BigInt): Boolean = {
    require(depth >= 0)

    this match {
      case Leaf(a) => depth == 0
      case Node2(left, right) =>
        depth != 0
          && left.isWellFormed(depth - 1)
          && right.isWellFormed(depth - 1)
      case Node3(left, middle, right) =>
        depth != 0
          && left.isWellFormed(depth - 1)
          && middle.isWellFormed(depth - 1)
          && right.isWellFormed(depth - 1)
    }
  }

  /// ***CONVERSION FUNCTIONS*** ///

  /// Constructs a list from a node, according to an in-order traversal
  def toListL(depth: BigInt): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))

    this match {
      case Leaf(a) => List(a)
      case Node2(left, right) => {
        ListLemmas.reverseConcat(
          left.toListL(depth - 1),
          right.toListL(depth - 1)
        )

        left.toListL(depth - 1) ++ right.toListL(depth - 1)
      }
      case Node3(left, middle, right) => {
        ListLemmas.reverseConcat(
          left.toListL(depth - 1),
          middle.toListL(depth - 1)
        )
        ListLemmas.reverseConcat(
          left.toListL(depth - 1) ++ middle.toListL(depth - 1),
          right.toListL(depth - 1)
        )
        ListLemmas.associativeConcat(
          right.toListR(depth - 1),
          middle.toListR(depth - 1),
          left.toListR(depth - 1)
        )

        left.toListL(depth - 1) ++ middle.toListL(depth - 1)
          ++ right.toListL(depth - 1)
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
      case Leaf(a) => List(a)
      case Node2(left, right) =>
        right.toListR(depth - 1) ++ left.toListR(depth - 1)
      case Node3(left, middle, right) =>
        right.toListR(depth - 1) ++ middle.toListR(depth - 1)
          ++ left.toListR(depth - 1)
    }
  }.ensuring(!_.isEmpty)

  /// Constructs a digit from a node, using each branch as an element in the digit
  def toDigit(depth: BigInt): Digit[T] = {
    require(depth >= 1 && this.isWellFormed(depth))

    this match {
      case Leaf(_)                    => ??? // Should never get here
      case Node2(left, right)         => Digit2(left, right)
      case Node3(left, middle, right) => Digit3(left, middle, right)
    }
  }.ensuring(res =>
    res.isWellFormed(depth - 1)
      && res.toListL(depth - 1) == this.toListL(depth)
      && res.toListR(depth - 1) == this.toListR(depth)
  )

/// A Node[T] is either a Leaf[T](value), Node2[T](left, right) or Node3[T](left, middle, right)
final case class Leaf[T](a: T) extends Node[T]
final case class Node2[T](left: Node[T], right: Node[T]) extends Node[T]
final case class Node3[T](
    left: Node[T],
    middle: Node[T],
    right: Node[T]
) extends Node[T]
