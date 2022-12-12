package fingertree

import stainless.collection._

private enum Node[+T]:
  case Node2(a: T, b: T)
  case Node3(a: T, b: T, c: T)

private enum Digit[+T]:
  case Digit1(a: T)
  case Digit2(a: T, b: T)
  case Digit3(a: T, b: T, c: T)
  case Digit4(a: T, b: T, c: T, d: T)

enum FingerTree[+T]:
  case Empty
  case Single(value: T)
  case Deep(prefix: Digit[T], spine: FingerTree[Node[T]], suffix: Digit[T])

object FingerTree {
  import Digit._
  import Node._

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
