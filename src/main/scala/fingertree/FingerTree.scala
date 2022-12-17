import stainless.collection.{List, Cons, Nil}

// Verification of the postcondition of ToNodeList
// is slow (> 30sec) while the condition seems trivial...

// nativez3-opt: 21s
// nativez3, smt-z3, smt-z3-opt, unrollz3: > 30s
// princess: stackoverflow ??

// Removing any of Node2 or Node3 case class makes
// the verification almost instantaneous.

private sealed trait Node[T]
private final case class Leaf[T](a: T) extends Node[T]
private final case class Node2[T](left: Node[T], right: Node[T]) extends Node[T]
private final case class Node3[T](
    left: Node[T],
    middle: Node[T],
    right: Node[T]
) extends Node[T]

private sealed trait Digit[T]:
  def toNodeList: List[Node[T]] = {
    this match {
      // case Digit1(a)          => List(a)
      // case Digit2(a, b)       => List(a, b)
      // case Digit3(a, b, c)    => List(a, b, c)
      case Digit4(a, b, c, d) => List(a, b, c, d)
    }
  }.ensuring(res => {
    res.length >= 1 && res.length <= 4
  })

// Changing the Node[T] into T make the verification almost instantaneous.

// private final case class Digit1[T](a: Node[T]) extends Digit[T]
// private final case class Digit2[T](a: Node[T], b: Node[T]) extends Digit[T]
// private final case class Digit3[T](a: Node[T], b: Node[T], c: Node[T])
//     extends Digit[T]
private final case class Digit4[T](
    a: Node[T],
    b: Node[T],
    c: Node[T],
    d: Node[T]
) extends Digit[T]
