package fingertree

sealed trait View[T]:
  def isEmpty: Boolean =
    this match {
      case NilV()      => true
      case ConsV(_, _) => false
    }

final case class NilV[T]() extends View[T]
final case class ConsV[T](head: T, rest: FingerTree[T]) extends View[T]
