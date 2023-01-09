package fingertree

sealed trait View[T, M]:
  def isEmpty: Boolean =
    this match {
      case NilV()      => true
      case ConsV(_, _) => false
    }

final case class NilV[T, M]() extends View[T, M]
final case class ConsV[T, M](head: T, rest: FingerTree[T, M]) extends View[T, M]
