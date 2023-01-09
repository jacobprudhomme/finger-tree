package fingertree

/// This file defines the data structure for a view of a finger tree, a
/// decomposition of it into a chosen element and the rest of the tree.
/// The case classes of View[T] are found at the end of the file.

sealed trait View[T]:

  /// Determines if we have the view of an empty finger tree
  def isEmpty: Boolean =
    this match {
      case NilV()      => true
      case ConsV(_, _) => false
    }

/// A View[T] is either a:
/// - NilV[T](), or
/// - ConsV[T](T, FingerTree[T]),
final case class NilV[T]() extends View[T]
final case class ConsV[T](head: T, rest: FingerTree[T]) extends View[T]
