package fingertree

import stainless.collection.{List, Cons, Nil}
import stainless.lang.{Option, Some, None}

private sealed trait Node[T]
private final case class Leaf[T](a: T) extends Node[T]
private final case class Node2[T](left: Node[T], right: Node[T]) extends Node[T]
private final case class Node3[T](
    left: Node[T],
    middle: Node[T],
    right: Node[T]
) extends Node[T]

private sealed trait Digit[T]
private final case class Digit1[T](a: T) extends Digit[T]
private final case class Digit2[T](a: T, b: T) extends Digit[T]
private final case class Digit3[T](a: T, b: T, c: T) extends Digit[T]
private final case class Digit4[T](a: T, b: T, c: T, d: T) extends Digit[T]

sealed trait FingerTree[T]
final case class Empty[T]() extends FingerTree[T]
final case class Single[T](value: Node[T]) extends FingerTree[T]
final case class Deep[T](
    prefix: Digit[Node[T]],
    spine: FingerTree[T],
    suffix: Digit[Node[T]]
) extends FingerTree[T]

sealed trait View[T]
final case class NilV[T]() extends View[T]
final case class ConsV[T](value: T, rest: FingerTree[T]) extends View[T]

object FingerTree {
  /// INTERNAL HELPERS ///

  private def headL[T](digit: Digit[Node[T]]): Node[T] =
    digit match {
      case Digit1(a)          => a
      case Digit2(a, _)       => a
      case Digit3(a, _, _)    => a
      case Digit4(a, _, _, _) => a
    }

  private def headR[T](digit: Digit[Node[T]]): Node[T] =
    digit match {
      case Digit1(a)          => a
      case Digit2(_, b)       => b
      case Digit3(_, _, c)    => c
      case Digit4(_, _, _, d) => d
    }

  private def tailL[T](digit: Digit[Node[T]]): Option[Digit[Node[T]]] =
    digit match {
      case Digit1(_)          => None()
      case Digit2(_, b)       => Some(Digit1(b))
      case Digit3(_, b, c)    => Some(Digit2(b, c))
      case Digit4(_, b, c, d) => Some(Digit3(b, c, d))
    }

  private def tailR[T](digit: Digit[Node[T]]): Option[Digit[Node[T]]] =
    digit match {
      case Digit1(_)          => None()
      case Digit2(a, _)       => Some(Digit1(a))
      case Digit3(a, b, _)    => Some(Digit2(a, b))
      case Digit4(a, b, c, _) => Some(Digit3(a, b, c))
    }

  private def toNodeList[T](digit: Digit[Node[T]]): List[Node[T]] =
    digit match {
      case Digit1(a)          => List(a)
      case Digit2(a, b)       => List(a, b)
      case Digit3(a, b, c)    => List(a, b, c)
      case Digit4(a, b, c, d) => List(a, b, c, d)
    }

  private def toList[T](node: Node[T]): List[T] =
    node match {
      case Leaf(a)            => List(a)
      case Node2(left, right) => toList(left) ++ toList(right)
      case Node3(left, middle, right) =>
        toList(left) ++ toList(middle) ++ toList(right)
    }

  private def toList[T](digit: Digit[Node[T]]): List[T] =
    digit match {
      case Digit1(a)       => toList(a)
      case Digit2(a, b)    => toList(a) ++ toList(b)
      case Digit3(a, b, c) => toList(a) ++ toList(b) ++ toList(c)
      case Digit4(a, b, c, d) =>
        toList(a) ++ toList(b) ++ toList(c) ++ toList(d)
    }

  private def toDigit[T](node: Node[T]): Digit[Node[T]] =
    node match {
      case Leaf(_)                    => ???
      case Node2(left, right)         => Digit2(left, right)
      case Node3(left, middle, right) => Digit3(left, middle, right)
    }

  private def toTree[T](elems: Digit[Node[T]]): FingerTree[T] =
    elems match {
      case Digit1(a)          => Single(a)
      case Digit2(a, b)       => Deep(Digit1(a), Empty(), Digit1(b))
      case Digit3(a, b, c)    => Deep(Digit2(a, b), Empty(), Digit1(c))
      case Digit4(a, b, c, d) => Deep(Digit2(a, b), Empty(), Digit2(c, d))
    }

  private def deepL[T](
      prefixTail: Option[Digit[Node[T]]],
      spine: FingerTree[T],
      suffix: Digit[Node[T]]
  ): FingerTree[T] =
    prefixTail match {
      case Some(digit) => Deep(digit, spine, suffix)
      case None() =>
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

  private def deepR[T](
      prefix: Digit[Node[T]],
      spine: FingerTree[T],
      suffixTail: Option[Digit[Node[T]]]
  ): FingerTree[T] =
    suffixTail match {
      case Some(digit) => Deep(prefix, spine, digit)
      case None() =>
        spine match {
          case Empty()       => toTree(prefix)
          case Single(value) => Deep(prefix, Empty(), toDigit(value))
          case Deep(spinePrefix, spineSpine, spineSuffix) =>
            Deep(
              prefix,
              deepR(spinePrefix, spineSpine, tailR(spineSuffix)),
              toDigit(headR(spineSuffix))
            )
        }
    }

  /// CONVERSION FUNCTIONS ///

  def toList[T](tree: FingerTree[T]): List[T] =
    tree match {
      case Empty()   => Nil()
      case Single(a) => toList(a)
      case Deep(prefix, spine, suffix) =>
        toList(prefix) ++ toList(spine) ++ toList(suffix)
    }

  def toTree[T](elems: List[T]): FingerTree[T] =
    elems match {
      case Nil()      => Empty()
      case Cons(a, b) => addR(toTree(b), a)
    }

  /// 3.2 DEQUE OPERATIONS ///

  private def addL[T](tree: FingerTree[T], value: Node[T]): FingerTree[T] =
    tree match {
      case Empty() => Single(value)
      case Single(existingValue) =>
        Deep(
          Digit1(value),
          Empty(),
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

  def addL[T](tree: FingerTree[T], value: T): FingerTree[T] =
    addL(tree, Leaf(value))

  def addR[T](tree: FingerTree[T], value: Node[T]): FingerTree[T] =
    tree match {
      case Empty() => Single(value)
      case Single(existingValue) =>
        Deep(
          Digit1(existingValue),
          Empty(),
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

  def addR[T](tree: FingerTree[T], value: T): FingerTree[T] =
    addR(tree, Leaf(value))

  def viewL[T](tree: FingerTree[T]): View[T] =
    tree match {
      case Empty()             => NilV()
      case Single(Leaf(value)) => ConsV(value, Empty())
      case Single(_)           => ??? // not supposed to happen I think ?
      case Deep(prefix, spine, suffix) =>
        headL(prefix) match {
          case Leaf(value) =>
            ConsV(
              value,
              deepL(tailL(prefix), spine, suffix)
            )
          case _ => ??? // not supposed to happen I think ?
        }
    }

  def viewR[T](tree: FingerTree[T]): View[T] =
    tree match {
      case Empty()             => NilV()
      case Single(Leaf(value)) => ConsV(value, Empty())
      case Single(_)           => ??? // not supposed to happen I think ?
      case Deep(prefix, spine, suffix) =>
        headR(suffix) match {
          case Leaf(value) =>
            ConsV(
              value,
              deepR(prefix, spine, tailR(suffix))
            )
          case _ => ??? // not supposed to happen I think ?
        }
    }

  def headL[T](tree: FingerTree[T]): Option[T] =
    tree match {
      case Empty()         => None()
      case Single(Leaf(e)) => Some(e)
      case Single(_)       => ??? // not supposed to happen I think ?
      case Deep(prefix, _, _) =>
        headL(prefix) match {
          case Leaf(value) => Some(value)
          case _           => ??? // not supposed to happen I think ?
        }
    }

  def headR[T](tree: FingerTree[T]): Option[T] =
    tree match {
      case Empty()         => None()
      case Single(Leaf(e)) => Some(e)
      case Single(_)       => ??? // not supposed to happen I think ?
      case Deep(prefix, _, _) =>
        headR(prefix) match {
          case Leaf(value) => Some(value)
          case _           => ??? // not supposed to happen I think ?
        }
    }

  def tailL[T](tree: FingerTree[T]): Option[FingerTree[T]] =
    viewL(tree) match {
      case ConsV(_, rest) => Some(rest)
      case NilV()         => None()
    }

  def tailR[T](tree: FingerTree[T]): Option[FingerTree[T]] =
    viewR(tree) match {
      case ConsV(_, rest) => Some(rest)
      case NilV()         => None()
    }

  def isEmpty[T](tree: FingerTree[T]): Boolean =
    tree match {
      case Empty() => true
      case _       => false
    }

  /// 3.3 CONCATENATION ///

  private def toNodes[T](elems: List[Node[T]]): List[Node[T]] =
    elems match {
      case Nil()                            => Nil()
      case Cons(a, Nil())                   => ???
      case Cons(a, Cons(b, Nil()))          => List(Node2(a, b))
      case Cons(a, Cons(b, Cons(c, Nil()))) => List(Node3(a, b, c))
      case Cons(a, Cons(b, Cons(c, Cons(d, Nil())))) =>
        List(Node2(a, b), Node2(c, d))
      case Cons(a, Cons(b, Cons(c, tail))) =>
        Cons(Node3(a, b, c), toNodes(tail))
    }

  private def concat[T](
      tree1: FingerTree[T],
      elems: List[Node[T]],
      tree2: FingerTree[T]
  ): FingerTree[T] =
    tree1 match {
      case Empty()   => tree2
      case Single(e) => addL(tree2, e)
      case Deep(prefix1, spine1, suffix1) =>
        tree2 match {
          case Empty()   => tree1
          case Single(e) => addR(tree1, e)
          case Deep(prefix2, spine2, suffix2) =>
            Deep(
              prefix1,
              concat(
                spine1,
                toNodes(toNodeList(suffix1) ++ elems ++ toNodeList(prefix1)),
                spine2
              ),
              suffix2
            )
        }
    }

  def ++[T](tree1: FingerTree[T], tree2: FingerTree[T]): FingerTree[T] =
    concat(tree1, Nil(), tree2)
}
