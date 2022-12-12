package fingertree

import stainless.collection._

private sealed trait Node[+T]
private final case class Node2[+T](a: T, b: T) extends Node[T]
private final case class Node3[+T](a: T, b: T, c: T) extends Node[T]

private sealed trait Digit[+T]
private final case class Digit1[+T](a: T) extends Digit[T]
private final case class Digit2[+T](a: T, b: T) extends Digit[T]
private final case class Digit3[+T](a: T, b: T, c: T) extends Digit[T]
private final case class Digit4[+T](a: T, b: T, c: T, d: T) extends Digit[T]

sealed trait FingerTree[+T]
private case object Empty extends FingerTree[Nothing]
private final case class Single[+T](value: T) extends FingerTree[T]
private final case class Deep[+T](
  prefix: Digit[T],
  spine: FingerTree[Node[T]],
  suffix: Digit[T]
) extends FingerTree[T]

object FingerTree {
  def addL[T](tree: FingerTree[T], value: T): FingerTree[T] =
    tree match {
      case Empty => Single(value)
      case Single(existingValue) =>
        Deep(
          Digit1(value),
          Empty,
          Digit1(existingValue)
        )
      case Deep(Digit1(a), spine, suffix) =>
        Deep(
          Digit2(value, a),
          spine,
          suffix
        )
      case Deep(Digit2(a, b), spine, suffix) =>
        Deep(
          Digit3(value, a, b),
          spine,
          suffix
        )
      case Deep(Digit3(a, b, c), spine, suffix) =>
        Deep(
          Digit4(value, a, b, c),
          spine,
          suffix
        )
      case Deep(Digit4(a, b, c, d), spine, suffix) =>
        Deep(
          Digit2(value, a),
          addL(spine, Node3(b, c, d)),
          suffix
        )
    }

  def addR[T](tree: FingerTree[T], value: T): FingerTree[T] =
    tree match {
      case Empty => Single(value)
      case Single(existingValue) =>
        Deep(
          Digit1(existingValue),
          Empty,
          Digit1(value)
        )
      case Deep(prefix, spine, Digit1(a)) =>
        Deep(
          prefix,
          spine,
          Digit2(a, value)
        )
      case Deep(prefix, spine, Digit2(a, b)) =>
        Deep(
          prefix,
          spine,
          Digit3(a, b, value)
        )
      case Deep(prefix, spine, Digit3(a, b, c)) =>
        Deep(
          prefix,
          spine,
          Digit4(a, b, c, value)
        )
      case Deep(prefix, spine, Digit4(a, b, c, d)) =>
        Deep(
          prefix,
          addR(spine, Node3(a, b, c)),
          Digit2(d, value)
        )
    }
}
