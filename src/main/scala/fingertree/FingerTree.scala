package fingertree

// import stainless.lang._
import stainless.collection.{List, Cons, Nil}

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

enum View[+T]:
  case Nil
  case Cons(value: T, rest: FingerTree[T])

object FingerTree {
  import Digit._
  import Node._

  /// INTERNAL HELPERS ///

  private def headL[T](digit: Digit[T]): T =
    digit match {
      case Digit1(a) => a
      case Digit2(a, _) => a
      case Digit3(a, _, _) => a
      case Digit4(a, _, _, _) => a
    }

  private def headR[T](digit: Digit[T]): T =
    digit match {
      case Digit1(a) => a
      case Digit2(_, b) => b
      case Digit3(_, _, c) => c
      case Digit4(_, _, _, d) => d
    }

  private def tailL[T](digit: Digit[T]): List[T] =
    digit match {
      case Digit1(_) => List()
      case Digit2(_, b) => List(b)
      case Digit3(_, b, c) => List(b, c)
      case Digit4(_, b, c, d) => List(b, c, d)
    }

  private def tailR[T](digit: Digit[T]): List[T] =
    digit match {
      case Digit1(_) => List()
      case Digit2(a, _) => List(a)
      case Digit3(a, b, _) => List(a, b)
      case Digit4(a, b, c, _) => List(a, b, c)
    }

  private def toList[T](digit:Digit[T]): List[T] =
    digit match {
      case Digit1(a) => List(a)
      case Digit2(a, b) => List(a, b)
      case Digit3(a, b, c) => List(a, b, c)
      case Digit4(a, b, c, d) => List(a, b, c, d)
    }

  private def toDigit[T](node: Node[T]): Digit[T] =
    node match {
      case Node2(a, b) => Digit2(a, b)
      case Node3(a, b, c) => Digit3(a, b, c)
    }

  private def toTree[T](elems: Digit[T]): FingerTree[T] =
    elems match {
      case Digit1(a) => Single(a)
      case Digit2(a, b) => Deep(Digit1(a), Empty, Digit1(b))
      case Digit3(a, b, c) => Deep(Digit2(a, b), Empty, Digit1(c))
      case Digit4(a, b, c, d) => Deep(Digit2(a, b), Empty, Digit2(c, d))
    }

  private def deepL[T](prefixTail: List[T], spine: FingerTree[Node[T]], suffix: Digit[T]): FingerTree[T] =
    prefixTail match {
      case Cons(a, Cons(b, Cons(c, _))) => Deep(Digit3(a, b, c), spine, suffix)
      case Cons(a, Cons(b, _)) => Deep(Digit2(a, b), spine, suffix)
      case Cons(a, _) => Deep(Digit1(a), spine, suffix)
      case Nil() =>
        viewL(spine) match {
          case View.Cons(value, rest) => Deep(toDigit(value), rest, suffix)
          case View.Nil => toTree(suffix)
        }
    }

  private def deepR[T](prefix: Digit[T], spine: FingerTree[Node[T]], suffixTail: List[T]): FingerTree[T] =
    suffixTail match {
      case Cons(a, Cons(b, Cons(c, _))) => Deep(prefix, spine, Digit3(a, b, c))
      case Cons(a, Cons(b, _)) => Deep(prefix, spine, Digit2(a, b))
      case Cons(a, _) => Deep(prefix, spine, Digit1(a))
      case Nil() =>
        viewR(spine) match {
          case View.Cons(value, rest) => Deep(prefix, rest, toDigit(value))
          case View.Nil => toTree(prefix)
        }
    }

  /// CONVERSION FUNCTIONS ///

  def toList[T](tree: FingerTree[T]): List[T] = {
    ???
  }

  def toTree[T](elems: List[T]): FingerTree[T] = {
    ???
  }

  /// 3.2 DEQUE OPERATIONS ///

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

  def viewL[T](tree: FingerTree[T]): View[T] =
    tree match {
      case Empty => View.Nil
      case Single(value) => View.Cons(value, Empty)
      case Deep(prefix, spine, suffix) =>
        View.Cons(
          headL(prefix),
          deepL(tailL(prefix), spine, suffix)
        )
    }

  def viewR[T](tree: FingerTree[T]): View[T] =
    tree match {
      case Empty => View.Nil
      case Single(value) => View.Cons(value, Empty)
      case Deep(prefix, spine, suffix) =>
        View.Cons(
          headR(suffix),
          deepR(prefix, spine, tailR(suffix))
        )
    }

  def headL[T](tree: FingerTree[T]): T =
    tree match {
      case Empty => throw Exception("Empty tree")
      case Single(e) => e
      case Deep(prefix, _, _) => headL(prefix)
    }

  def headR[T](tree: FingerTree[T]): T =
    tree match {
      case Empty => throw Exception("Empty tree")
      case Single(e) => e
      case Deep(_, _, suffix) => headR(suffix)
    }

  def tailL[T](tree: FingerTree[T]): FingerTree[T] =
    viewL(tree) match {
      case View.Cons(_, rest) => rest
      case View.Nil => throw Exception("Empty tree")
    }

  def tailR[T](tree: FingerTree[T]): FingerTree[T] =
    viewR(tree) match {
      case View.Cons(_, rest) => rest
      case View.Nil => throw Exception("Empty tree")
    }

  def isEmpty[T](tree: FingerTree[T]): Boolean =
    tree == Empty

  /// 3.3 CONCATENATION ///

  private def toNodes[T](elems: List[T]): List[Node[T]] =
    elems match {
      case Nil() => Nil()
      case Cons(a, Nil()) => ???
      case Cons(a, Cons(b, Nil())) => List(Node2(a, b))
      case Cons(a, Cons(b, Cons(c, Nil()))) => List(Node3(a,b, c))
      case Cons(a, Cons(b, Cons(c, Cons(d, Nil())))) => List(Node2(a,b), Node2(c, d))
      case Cons(a, Cons(b, Cons(c, tail))) => Cons(Node3(a, b, c), toNodes(tail))
    }

  private def concat[T](tree1: FingerTree[T], elems: List[T], tree2: FingerTree[T]): FingerTree[T] =
    tree1 match {
      case Empty => tree2
      case Single(e) => addL(tree2, e)
      case Deep(prefix1, spine1, suffix1) => tree2 match {
        case Empty => tree1
        case Single(e) => addR(tree1, e)
        case Deep(prefix2, spine2, suffix2) =>
          Deep(prefix1, concat(spine1, toNodes(toList(suffix1) ++ elems ++ toList(prefix1)), spine2), suffix2)
      }
    }

  def ++[T](tree1: FingerTree[T], tree2: FingerTree[T]): FingerTree[T] =
    concat(tree1, Nil(), tree2)
}
