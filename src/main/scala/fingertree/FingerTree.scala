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

  private def deepL[T](
      prefixTail: Option[Digit[T]],
      spine: FingerTree[Node[T]],
      suffix: Digit[T]
  ): FingerTree[T] = {
    spine match {
      case Deep(spinePrefix, spineSpine, spineSuffix) =>
        Deep(
          suffix,
          deepL(None(), spineSpine, spineSuffix),
          suffix
        )
      case _ => Empty()
    }
  }
}
