package fingertree

import stainless.lang.{Option, Some, None, decreases}

private sealed trait Node[T]
private final case class Node2[T](a: T, b: T) extends Node[T]
private final case class Node3[T](a: T, b: T, c: T) extends Node[T]

private sealed trait Digit[T]
private final case class Digit1[T](a: T) extends Digit[T]
private final case class Digit2[T](a: T, b: T) extends Digit[T]
private final case class Digit3[T](a: T, b: T, c: T) extends Digit[T]
private final case class Digit4[T](a: T, b: T, c: T, d: T) extends Digit[T]

sealed trait FingerTree[T]
final case class Empty[T]() extends FingerTree[T]
final case class Single[T](value: T) extends FingerTree[T]
final case class Deep[T](
    prefix: Digit[T],
    spine: FingerTree[Node[T]],
    suffix: Digit[T]
) extends FingerTree[T]

object FingerTree {
  /// INTERNAL HELPERS ///

  private def headL[T](digit: Digit[T]): T =
    digit match {
      case Digit1(a)          => a
      case Digit2(a, _)       => a
      case Digit3(a, _, _)    => a
      case Digit4(a, _, _, _) => a
    }

  private def tailL[T](digit: Digit[T]): Option[Digit[T]] =
    digit match {
      case Digit1(_)          => None()
      case Digit2(_, b)       => Some(Digit1(b))
      case Digit3(_, b, c)    => Some(Digit2(b, c))
      case Digit4(_, b, c, d) => Some(Digit3(b, c, d))
    }

  private def toDigit[T](node: Node[T]): Digit[T] =
    node match {
      case Node2(a, b)    => Digit2(a, b)
      case Node3(a, b, c) => Digit3(a, b, c)
    }

  private def toTree[T](elems: Digit[T]): FingerTree[T] =
    elems match {
      case Digit1(a)          => Single(a)
      case Digit2(a, b)       => Deep(Digit1(a), Empty(), Digit1(b))
      case Digit3(a, b, c)    => Deep(Digit2(a, b), Empty(), Digit1(c))
      case Digit4(a, b, c, d) => Deep(Digit2(a, b), Empty(), Digit2(c, d))
    }

  private def deepL[T](
      prefixTail: Option[Digit[T]],
      spine: FingerTree[Node[T]],
      suffix: Digit[T]
  ): FingerTree[T] = {
    decreases(spine)
    spine match {
      case Empty()       => toTree(suffix)
      case Single(value) => Deep(toDigit(value), Empty(), suffix)
      case Deep(spinePrefix, spineSpine, spineSuffix) =>
        Deep(
          toDigit(headL(spinePrefix)),
          deepL(tailL(spinePrefix), spineSpine, spineSuffix),
          suffix
        )
    }
  }
}
