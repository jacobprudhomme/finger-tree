package fingertree

import stainless.collection.List

private sealed trait Node[T]
private final case class Node2[T](val1: T, val2: T) extends Node[T]
private final case class Node3[T](val1: T, val2: T, val3: T) extends Node[T]

private final case class Digit[T](elems: List[T])

sealed trait FingerTree[T]
private case object Empty extends FingerTree[Nothing]
private final case class Single[T](value: T) extends FingerTree[T]
private final case class Deep[T](
  left: Digit[T],
  spine: FingerTree[Node[T]],
  right: Digit[T]
) extends FingerTree[T]

object FingerTree {
  // Implementation goes here?
}
