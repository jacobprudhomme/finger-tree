package fingertree

import stainless.collection.{List, Cons, Nil}
import stainless.lang.{Option, Some, None, BooleanDecorations}

private sealed trait Node[T]:
  def toList: List[T] =
    this match {
      case Leaf(a)            => List(a)
      case Node2(left, right) => left.toList ++ right.toList
      case Node3(left, middle, right) =>
        left.toList ++ middle.toList ++ right.toList
    }

  def toDigit(depth: BigInt): Digit[T] = {
    require(depth >= 1 && this.isWellFormed(depth))
    this match {
      case Leaf(_)                    => ???
      case Node2(left, right)         => Digit2(left, right)
      case Node3(left, middle, right) => Digit3(left, middle, right)
    }
  }.ensuring(_.isWellFormed(depth - 1))

  def isWellFormed(depth: BigInt): Boolean = {
    require(depth >= 0)
    this match
      case Leaf(a) => depth == 0
      case Node2(left, right) =>
        depth != 0
        && left.isWellFormed(depth - 1)
        && right.isWellFormed(depth - 1)
      case Node3(left, middle, right) =>
        depth != 0
        && left.isWellFormed(depth - 1)
        && middle.isWellFormed(depth - 1)
        && right.isWellFormed(depth - 1)
  }

private final case class Leaf[T](a: T) extends Node[T]
private final case class Node2[T](left: Node[T], right: Node[T]) extends Node[T]
private final case class Node3[T](
    left: Node[T],
    middle: Node[T],
    right: Node[T]
) extends Node[T]

private sealed trait Digit[T]:
  def headL(depth: BigInt): Node[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(a)          => a
      case Digit2(a, _)       => a
      case Digit3(a, _, _)    => a
      case Digit4(a, _, _, _) => a
    }
  }.ensuring(_.isWellFormed(depth))

  def headR(depth: BigInt): Node[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(a)          => a
      case Digit2(_, b)       => b
      case Digit3(_, _, c)    => c
      case Digit4(_, _, _, d) => d
    }
  }.ensuring(_.isWellFormed(depth))

  def tailL(depth: BigInt): Option[Digit[T]] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(_)          => None()
      case Digit2(_, b)       => Some(Digit1(b))
      case Digit3(_, b, c)    => Some(Digit2(b, c))
      case Digit4(_, b, c, d) => Some(Digit3(b, c, d))
    }
  }.ensuring(_.forall(_.isWellFormed(depth)))

  def tailR(depth: BigInt): Option[Digit[T]] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(_)          => None()
      case Digit2(a, _)       => Some(Digit1(a))
      case Digit3(a, b, _)    => Some(Digit2(a, b))
      case Digit4(a, b, c, _) => Some(Digit3(a, b, c))
    }
  }.ensuring(_.forall(_.isWellFormed(depth)))

  def toNodeList(depth: BigInt): List[Node[T]] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(a)          => List(a)
      case Digit2(a, b)       => List(a, b)
      case Digit3(a, b, c)    => List(a, b, c)
      case Digit4(a, b, c, d) => List(a, b, c, d)
    }
  }.ensuring(res =>
    res.length >= 1 && res.length <= 4 && res.forall(_.isWellFormed(depth))
  )

  def toList: List[T] =
    this match {
      case Digit1(a)       => a.toList
      case Digit2(a, b)    => a.toList ++ b.toList
      case Digit3(a, b, c) => a.toList ++ b.toList ++ c.toList
      case Digit4(a, b, c, d) =>
        a.toList ++ b.toList ++ c.toList ++ d.toList
    }

  def toTree(depth: BigInt): FingerTree[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(a)          => Single(a)
      case Digit2(a, b)       => Deep(Digit1(a), Empty(), Digit1(b))
      case Digit3(a, b, c)    => Deep(Digit2(a, b), Empty(), Digit1(c))
      case Digit4(a, b, c, d) => Deep(Digit2(a, b), Empty(), Digit2(c, d))
    }
  }.ensuring(_.isWellFormed(depth))

  def forall(p: Node[T] => Boolean): Boolean =
    this match
      case Digit1(a)          => p(a)
      case Digit2(a, b)       => p(a) && p(b)
      case Digit3(a, b, c)    => p(a) && p(b) && p(c)
      case Digit4(a, b, c, d) => p(a) && p(b) && p(c) && p(d)

  def isWellFormed(depth: BigInt): Boolean = {
    require(depth >= 0)
    this.forall(_.isWellFormed(depth))
  }

private final case class Digit1[T](a: Node[T]) extends Digit[T]
private final case class Digit2[T](a: Node[T], b: Node[T]) extends Digit[T]
private final case class Digit3[T](a: Node[T], b: Node[T], c: Node[T])
    extends Digit[T]
private final case class Digit4[T](
    a: Node[T],
    b: Node[T],
    c: Node[T],
    d: Node[T]
) extends Digit[T]

sealed trait FingerTree[T]:
  /// STAINLESS HELPER ///

  def isWellFormed(depth: BigInt): Boolean = {
    require(depth >= 0)
    this match
      case Empty()       => true
      case Single(value) => value.isWellFormed(depth)
      case Deep(prefix, spine, suffix) =>
        prefix.isWellFormed(depth)
        && suffix.isWellFormed(depth)
        && spine.isWellFormed(depth + 1)
  }

  def isWellFormed: Boolean =
    this.isWellFormed(0)

  /// CONVERSION FUNCTIONS ///

  def toTree[T](elems: List[T]): FingerTree[T] = {
    elems match {
      case Nil()      => Empty()
      case Cons(a, b) => toTree(b).addL(a)
    }
  }.ensuring(_.isWellFormed)

  def toList: List[T] =
    this match {
      case Empty()   => Nil()
      case Single(a) => a.toList
      case Deep(prefix, spine, suffix) =>
        prefix.toList ++ spine.toList ++ suffix.toList
    }

  /// INTERNAL HELPERS ///

  private def deepL[T](
      prefixTail: Option[Digit[T]],
      spine: FingerTree[T],
      suffix: Digit[T],
      depth: BigInt
  ): FingerTree[T] = {
    require(
      depth >= 0
        && spine.isWellFormed(depth + 1)
        && prefixTail.forall(_.isWellFormed(depth))
        && suffix.isWellFormed(depth)
    )
    prefixTail match {
      case Some(digit) => Deep(digit, spine, suffix)
      case None() =>
        spine match {
          case Empty()       => suffix.toTree(depth)
          case Single(value) => Deep(value.toDigit(depth + 1), Empty(), suffix)
          case Deep(spinePrefix, spineSpine, spineSuffix) =>
            Deep(
              spinePrefix.headL(depth + 1).toDigit(depth + 1),
              deepL(
                spinePrefix.tailL(depth + 1),
                spineSpine,
                spineSuffix,
                depth + 1
              ),
              suffix
            )
        }
    }
  }.ensuring(_.isWellFormed(depth))

  private def deepR[T](
      prefix: Digit[T],
      spine: FingerTree[T],
      suffixTail: Option[Digit[T]],
      depth: BigInt
  ): FingerTree[T] = {
    require(
      depth >= 0
        && spine.isWellFormed(depth + 1)
        && prefix.isWellFormed(depth)
        && suffixTail.forall(_.isWellFormed(depth))
    )
    suffixTail match {
      case Some(digit) => Deep(prefix, spine, digit)
      case None() =>
        spine match {
          case Empty()       => prefix.toTree(depth)
          case Single(value) => Deep(prefix, Empty(), value.toDigit(depth + 1))
          case Deep(spinePrefix, spineSpine, spineSuffix) =>
            Deep(
              prefix,
              deepR(
                spinePrefix,
                spineSpine,
                spineSuffix.tailR(depth + 1),
                depth + 1
              ),
              spineSuffix.headR(depth + 1).toDigit(depth + 1)
            )
        }
    }
  }.ensuring(_.isWellFormed(depth))

  /// 3.2 DEQUE OPERATIONS ///

  private def addL(value: Node[T], depth: BigInt): FingerTree[T] = {
    require(depth >= 0 && this.isWellFormed(depth) && value.isWellFormed(depth))
    this match {
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
          spine.addL(Node3(b, c, d), depth + 1),
          suffix
        )
    }
  }.ensuring(_.isWellFormed(depth))

  // preprends the list to the tree
  private def addL(elems: List[Node[T]], depth: BigInt): FingerTree[T] = {
    require(
      depth >= 0
        && this.isWellFormed(depth)
        && elems.forall(_.isWellFormed(depth))
    )
    elems match {
      case Nil()      => this
      case Cons(h, t) => this.addL(t, depth).addL(h, depth)
    }
  }.ensuring(_.isWellFormed(depth))

  def addL(value: T): FingerTree[T] = {
    require(this.isWellFormed)
    this.addL(Leaf(value), 0)
  }.ensuring(_.isWellFormed)

  private def addR(value: Node[T], depth: BigInt): FingerTree[T] = {
    require(depth >= 0 && this.isWellFormed(depth) && value.isWellFormed(depth))
    this match {
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
          spine.addR(Node3(a, b, c), depth + 1),
          Digit2(d, value)
        )
    }
  }.ensuring(_.isWellFormed(depth))

  // appends the list to the tree
  private def addR(elems: List[Node[T]], depth: BigInt): FingerTree[T] = {
    require(
      depth >= 0
        && this.isWellFormed(depth)
        && elems.forall(_.isWellFormed(depth))
    )
    elems match {
      case Nil()      => this
      case Cons(h, t) => this.addR(h, depth).addR(t, depth)
    }
  }.ensuring(_.isWellFormed(depth))

  def addR(value: T): FingerTree[T] = {
    require(this.isWellFormed)
    this.addR(Leaf(value), 0)
  }.ensuring(_.isWellFormed)

  def viewL: View[T] = {
    require(this.isWellFormed)
    this match {
      case Empty()             => NilV()
      case Single(Leaf(value)) => ConsV(value, Empty())
      case Single(_)           => ??? // not supposed to happen I think ?
      case Deep(prefix, spine, suffix) =>
        prefix.headL(0) match {
          case Leaf(value) =>
            ConsV(
              value,
              deepL(prefix.tailL(0), spine, suffix, 0)
            )
          case _ => ??? // not supposed to happen I think ?
        }
    }
  }

  def viewR: View[T] = {
    require(this.isWellFormed)
    this match {
      case Empty()             => NilV()
      case Single(Leaf(value)) => ConsV(value, Empty())
      case Single(_)           => ??? // not supposed to happen I think ?
      case Deep(prefix, spine, suffix) =>
        suffix.headR(0) match {
          case Leaf(value) =>
            ConsV(
              value,
              deepR(prefix, spine, suffix.tailR(0), 0)
            )
          case _ => ??? // not supposed to happen I think ?
        }
    }
  }.ensuring {
    case NilV()             => true
    case ConsV(value, rest) => rest.isWellFormed
  }

  def headL: Option[T] = {
    require(this.isWellFormed)
    this match {
      case Empty()         => None()
      case Single(Leaf(e)) => Some(e)
      case Single(_)       => ??? // not supposed to happen I think ?
      case Deep(prefix, _, _) =>
        prefix.headL(0) match {
          case Leaf(value) => Some(value)
          case _           => ??? // not supposed to happen I think ?
        }
    }
  }

  def headR: Option[T] = {
    require(this.isWellFormed)
    this match {
      case Empty()         => None()
      case Single(Leaf(e)) => Some(e)
      case Single(_)       => ??? // not supposed to happen I think ?
      case Deep(prefix, _, _) =>
        prefix.headR(0) match {
          case Leaf(value) => Some(value)
          case _           => ??? // not supposed to happen I think ?
        }
    }
  }

  def tailL: Option[FingerTree[T]] = {
    require(this.isWellFormed)
    this.viewL match {
      case ConsV(_, rest) => Some(rest)
      case NilV()         => None()
    }
  }

  def tailR: Option[FingerTree[T]] = {
    require(this.isWellFormed)
    this.viewR match {
      case ConsV(_, rest) => Some(rest)
      case NilV()         => None()
    }
  }

  def isEmpty: Boolean =
    this match {
      case Empty() => true
      case _       => false
    }

  /// 3.3 CONCATENATION ///

  private def toNodes[T](elems: List[Node[T]], depth: BigInt): List[Node[T]] = {
    require(
      depth >= 0
        && elems.size >= 2
        && elems.size <= 12
        && elems.forall(_.isWellFormed(depth))
    )
    elems match {
      case Nil()                            => ???
      case Cons(a, Nil())                   => ???
      case Cons(a, Cons(b, Nil()))          => List(Node2(a, b))
      case Cons(a, Cons(b, Cons(c, Nil()))) => List(Node3(a, b, c))
      case Cons(a, Cons(b, Cons(c, Cons(d, Nil())))) =>
        List(Node2(a, b), Node2(c, d))
      case Cons(a, Cons(b, Cons(c, Cons(d, Cons(e, Nil()))))) =>
        List(Node3(a, b, c), Node2(d, e))
      case Cons(a, Cons(b, Cons(c, Cons(d, Cons(e, Cons(f, Nil())))))) =>
        List(Node3(a, b, c), Node3(d, e, f))
      case Cons(
            a,
            Cons(b, Cons(c, Cons(d, Cons(e, Cons(f, Cons(g, Nil()))))))
          ) =>
        List(Node3(a, b, c), Node2(d, e), Node2(f, g))
      case Cons(
            a,
            Cons(b, Cons(c, Cons(d, Cons(e, Cons(f, Cons(g, Cons(h, Nil())))))))
          ) =>
        List(Node3(a, b, c), Node3(d, e, f), Node2(g, h))
      case Cons(
            a,
            Cons(
              b,
              Cons(
                c,
                Cons(d, Cons(e, Cons(f, Cons(g, Cons(h, Cons(i, Nil()))))))
              )
            )
          ) =>
        List(Node3(a, b, c), Node3(d, e, f), Node3(g, h, i))
      case Cons(
            a,
            Cons(
              b,
              Cons(
                c,
                Cons(
                  d,
                  Cons(e, Cons(f, Cons(g, Cons(h, Cons(i, Cons(j, Nil()))))))
                )
              )
            )
          ) =>
        List(Node3(a, b, c), Node3(d, e, f), Node2(g, h), Node2(i, j))
      case Cons(
            a,
            Cons(
              b,
              Cons(
                c,
                Cons(
                  d,
                  Cons(
                    e,
                    Cons(f, Cons(g, Cons(h, Cons(i, Cons(j, Cons(k, Nil()))))))
                  )
                )
              )
            )
          ) =>
        List(Node3(a, b, c), Node3(d, e, f), Node3(g, h, i), Node2(j, k))
      case Cons(
            a,
            Cons(
              b,
              Cons(
                c,
                Cons(
                  d,
                  Cons(
                    e,
                    Cons(
                      f,
                      Cons(
                        g,
                        Cons(h, Cons(i, Cons(j, Cons(k, Cons(l, Nil())))))
                      )
                    )
                  )
                )
              )
            )
          ) =>
        List(Node3(a, b, c), Node3(d, e, f), Node3(g, h, i), Node3(j, k, l))
      case _ => ???
    }
  }.ensuring(res => res.size <= 4 && res.forall(_.isWellFormed(depth + 1)))

  private def concat[T](
      tree1: FingerTree[T],
      elems: List[Node[T]],
      tree2: FingerTree[T],
      depth: BigInt
  ): FingerTree[T] = {
    require(
      depth >= 0
        && tree1.isWellFormed(depth)
        && tree2.isWellFormed(depth)
        && elems.forall(_.isWellFormed(depth))
    )
    tree1 match {
      case Empty()   => tree2.addL(elems, depth)
      case Single(e) => tree2.addL(e, depth).addL(elems, depth)
      case Deep(prefix1, spine1, suffix1) =>
        tree2 match {
          case Empty()   => tree1.addR(elems, depth)
          case Single(e) => tree1.addR(e, depth).addR(elems, depth)
          case Deep(prefix2, spine2, suffix2) =>
            Deep(
              prefix1,
              concat(
                spine1,
                toNodes(
                  suffix1.toNodeList(depth)
                    ++ elems
                    ++ prefix1.toNodeList(depth),
                  depth
                ),
                spine2,
                depth + 1
              ),
              suffix2
            )
        }
    }
  }.ensuring(_.isWellFormed(depth))

  def ++[T](tree1: FingerTree[T], tree2: FingerTree[T]): FingerTree[T] = {
    require(tree1.isWellFormed && tree2.isWellFormed)
    tree1.concat(tree2)
  }.ensuring(_.isWellFormed)

  def concat(tree: FingerTree[T]): FingerTree[T] = {
    require(this.isWellFormed && tree.isWellFormed)
    concat(this, Nil(), tree, 0)
  }.ensuring(_.isWellFormed)

  /// PROOF ///
  def isEmpty_law(t: FingerTree[T]): Boolean = {
    t match{
      case Empty() => t.isEmpty == true
      case _ => t.isEmpty == false
    }
  }.holds

  def isEmpty_left(t: FingerTree[T]): Boolean = {
    t.concat(Empty()).isEmpty == t.isEmpty
  }.holds

  def isEmpty_right(t: FingerTree[T]): Boolean = {
    Empty().concat(t).isEmpty == t.isEmpty
  }.holds

  def isEmpty_concat(t1: FingerTree[T], t2: FingerTree[T]): Boolean = {
    t1.concat(t2).isEmpty == (t1.isEmpty && t2.isEmpty)
  }.holds

  def toTree_toList(l: List[T]): Boolean ={
    toTree(l).toList == l
  }.holds

  def headL_law(t: FingerTree[T]): Boolean ={
    t.headL == t.toList.headOption
  }.holds

  def headR_law(t: FingerTree[T]): Boolean ={
    t.headR == t.toList.lastOption
  }.holds

  def addL_law(t: FingerTree[T], value: T): Boolean ={
    t.addL(value).toList == value :: t.toList
  }.holds

  def addR_law(t: FingerTree[T], value: T): Boolean ={
    t.addR(value).toList == t.toList :+ value
  }.holds

  def concat_law(t1: FingerTree[T], t2: FingerTree[T]): Boolean = {
    t1.concat(t2).toList == t1.toList ++ t2.toList
  }.holds

final case class Empty[T]() extends FingerTree[T]
final case class Single[T](value: Node[T]) extends FingerTree[T]
final case class Deep[T](
    prefix: Digit[T],
    spine: FingerTree[T],
    suffix: Digit[T]
) extends FingerTree[T]

sealed trait View[T]
final case class NilV[T]() extends View[T]
final case class ConsV[T](value: T, rest: FingerTree[T]) extends View[T]
