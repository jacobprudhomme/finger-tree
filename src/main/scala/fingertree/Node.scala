package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

sealed trait Node[T]:
  def toListL(depth: BigInt): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Leaf(a) => List(a)
      case Node2(left, right) =>
        ListLemmas.reverseConcat(
          left.toListL(depth - 1),
          right.toListL(depth - 1)
        )
        left.toListL(depth - 1) ++ right.toListL(depth - 1)
      case Node3(left, middle, right) =>
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
  }.ensuring(res =>
    !res.isEmpty
      && res.reverse == this.toListR(depth)
  )

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

  def toDigit(depth: BigInt): Digit[T] = {
    require(depth >= 1 && this.isWellFormed(depth))
    this match {
      case Leaf(_)                    => ???
      case Node2(left, right)         => Digit2(left, right)
      case Node3(left, middle, right) => Digit3(left, middle, right)
    }
  }.ensuring(res =>
    res.isWellFormed(depth - 1)
      && res.toListL(depth - 1) == this.toListL(depth)
      && res.toListR(depth - 1) == this.toListR(depth)
  )

  def isWellFormed(depth: BigInt): Boolean = {
    require(depth >= 0)
    this match
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

final case class Leaf[T](a: T) extends Node[T]
final case class Node2[T](left: Node[T], right: Node[T]) extends Node[T]
final case class Node3[T](
    left: Node[T],
    middle: Node[T],
    right: Node[T]
) extends Node[T]
