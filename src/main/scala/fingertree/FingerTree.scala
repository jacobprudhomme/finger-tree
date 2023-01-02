package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

private sealed trait Node[T]:
  def toListL(depth: BigInt): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Leaf(a) => List(a)
      case Node2(left, right) =>
        Utils.reverseConcat(left.toListL(depth - 1), right.toListL(depth - 1))
        left.toListL(depth - 1) ++ right.toListL(depth - 1)
      case Node3(left, middle, right) =>
        Utils.reverseConcat(left.toListL(depth - 1), middle.toListL(depth - 1))
        Utils.reverseConcat(left.toListL(depth - 1)
          ++ middle.toListL(depth - 1), right.toListL(depth - 1))
        Utils.associativeConcat(
          right.toListR(depth - 1),
          middle.toListR(depth - 1),
          left.toListR(depth - 1),
        )
        left.toListL(depth - 1)
          ++ middle.toListL(depth - 1)
          ++ right.toListL(depth - 1)
    }
  }.ensuring(res =>
    !res.isEmpty
    && res.reverse == this.toListR(depth)
  )

  def toListR(depth: BigInt): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Leaf(a) => List(a)
      case Node2(left, right) =>
        right.toListR(depth - 1) ++ left.toListR(depth - 1)
      case Node3(left, middle, right) =>
        right.toListR(depth - 1)
          ++ middle.toListR(depth - 1)
          ++ left.toListR(depth - 1)
    }
  }.ensuring(!_.isEmpty)

  def toDigit(depth: BigInt): Digit[T] = {
    require(depth >= 1 && this.isWellFormed(depth))
    this match {
      case Leaf(_)                    => ???
      case Node2(left, right)         => Digit2(left, right)
      case Node3(left, middle, right) => Digit3(left, middle, right)
    }
  }.ensuring(res =>
    res.isWellFormed(depth - 1)
      && res.toListL(depth - 1) == this.toListL(depth)
      && res.toListR(depth - 1) == this.toListR(depth)
  )

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
  }.ensuring(res =>
    res.isWellFormed(depth)
    // && res == this.toNodeList(depth).head
  )

  def headR(depth: BigInt): Node[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(a)          => a
      case Digit2(_, b)       => b
      case Digit3(_, _, c)    => c
      case Digit4(_, _, _, d) => d
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && res == this.toNodeList(depth).last
  )

  def tailL(depth: BigInt): Option[Digit[T]] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(_)          => None()
      case Digit2(_, b)       => Some(Digit1(b))
      case Digit3(_, b, c)    => Some(Digit2(b, c))
      case Digit4(_, b, c, d) => Some(Digit3(b, c, d))
    }
  }.ensuring(res =>
    res.forall(_.isWellFormed(depth))
    // && (res match {
    //   case None()     => !this.toListL(depth).tailOption.isDefined
    //   case Some(tail) => tail.toListL(depth) == this.toListL(depth).tail
    // })
  )

  def tailR(depth: BigInt): Option[Digit[T]] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(_)          => None()
      case Digit2(a, _)       => Some(Digit1(a))
      case Digit3(a, b, _)    => Some(Digit2(a, b))
      case Digit4(a, b, c, _) => Some(Digit3(a, b, c))
    }
  }.ensuring(res =>
    res.forall(_.isWellFormed(depth))
    // && (res match {
    //   case None()     => !this.toListR(depth).tailOption.isDefined
    //   case Some(tail) => tail.toListR(depth) == this.toListR(depth).tail
    // })
  )

  // this is awful but stainless loves it
  def toNodeList(depth: BigInt): List[Node[T]] = {
    require(depth >= 0 && this.isWellFormed(depth))
    decreases(this)
    this.tailL(depth) match {
      case None()     => List(this.headL(depth))
      case Some(tail) => Cons(this.headL(depth), tail.toNodeList(depth))
    }
  }.ensuring(res =>
    !res.isEmpty
      && res.forall(_.isWellFormed(depth))
      && res == (this match {
        case Digit1(a)          => List[Node[T]](a)
        case Digit2(a, b)       => List[Node[T]](a, b)
        case Digit3(a, b, c)    => List[Node[T]](a, b, c)
        case Digit4(a, b, c, d) => List[Node[T]](a, b, c, d)
      })
      && Utils.toListL(res, depth) == this.toListL(depth)
      && Utils.toListR(res, depth) == this.toListR(depth)
  )

  def toListL(depth: BigInt): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(a)    => a.toListL(depth)
      case Digit2(a, b) =>
        Utils.reverseConcat(a.toListL(depth), b.toListL(depth))
        a.toListL(depth) ++ b.toListL(depth)
      case Digit3(a, b, c) =>
        Utils.reverseConcat(a.toListL(depth), b.toListL(depth))
        Utils.reverseConcat(a.toListL(depth)
          ++ b.toListL(depth), c.toListL(depth))
        Utils.associativeConcat(
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth),
        )
        a.toListL(depth) ++ b.toListL(depth)
          ++ c.toListL(depth)
      case Digit4(a, b, c, d) =>
        Utils.reverseConcat(a.toListL(depth), b.toListL(depth))
        Utils.reverseConcat(a.toListL(depth)
          ++ b.toListL(depth), c.toListL(depth))
        Utils.reverseConcat(a.toListL(depth)
          ++ b.toListL(depth) ++ c.toListL(depth), d.toListL(depth))
        Utils.associativeConcat(
          d.toListR(depth),
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth),
        )
        a.toListL(depth) ++ b.toListL(depth)
          ++ c.toListL(depth) ++ d.toListL(depth)
    }
  }.ensuring(res =>
    !res.isEmpty
    && res.reverse == this.toListR(depth)
  )

  def toListR(depth: BigInt): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(a)    => a.toListR(depth)
      case Digit2(a, b) => b.toListR(depth) ++ a.toListR(depth)
      case Digit3(a, b, c) =>
        c.toListR(depth) ++ b.toListR(depth)
          ++ a.toListR(depth)
      case Digit4(a, b, c, d) =>
        d.toListR(depth) ++ c.toListR(depth)
          ++ b.toListR(depth) ++ a.toListR(depth)
    }
  }.ensuring(!_.isEmpty)

  def toTree(depth: BigInt): FingerTree[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Digit1(a)    => Single(a)
      case Digit2(a, b) => Deep(Digit1(a), Empty(), Digit1(b))
      case Digit3(a, b, c) =>
        Utils.associativeConcat(
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )
        Deep(Digit2(a, b), Empty(), Digit1(c))
      case Digit4(a, b, c, d) =>
        Utils.associativeConcat(
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth),
          d.toListL(depth)
        )
        Utils.associativeConcat(
          d.toListR(depth),
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )
        Deep(Digit2(a, b), Empty(), Digit2(c, d))
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && !res.isEmpty(depth)
      && res.toListL(depth) == this.toListL(depth)
      && res.toListR(depth) == this.toListR(depth)
  )

  def forall(p: Node[T] => Boolean): Boolean = {
    this match
      case Digit1(a)          => p(a)
      case Digit2(a, b)       => p(a) && p(b)
      case Digit3(a, b, c)    => p(a) && p(b) && p(c)
      case Digit4(a, b, c, d) => p(a) && p(b) && p(c) && p(d)
  }
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

  def toTreeL[T](elems: List[T]): FingerTree[T] = {
    elems match {
      case Nil()      => Empty()
      case Cons(h, t) => toTreeL(t).addL(h)
    }
  }.ensuring(res =>
    res.isWellFormed
      && res.toListL() == elems
  )

  def toTreeR[T](elems: List[T]): FingerTree[T] = {
    elems match {
      case Nil()      => Empty()
      case Cons(h, t) => toTreeR(t).addR(h)
    }
  }.ensuring(res =>
    res.isWellFormed
      && res.toListR() == elems
  )

  def toListL(depth: BigInt): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Empty()   => Nil()
      case Single(a) => a.toListL(depth)
      case Deep(prefix, spine, suffix) =>
        Utils.reverseConcat(prefix.toListL(depth), spine.toListL(depth + 1))
        Utils.reverseConcat(prefix.toListL(depth)
          ++ spine.toListL(depth + 1), suffix.toListL(depth))
        Utils.associativeConcat(
          suffix.toListR(depth),
          spine.toListR(depth + 1),
          prefix.toListR(depth),
        )
        prefix.toListL(depth)
          ++ spine.toListL(depth + 1)
          ++ suffix.toListL(depth)
    }
  }.ensuring(res =>
    res.reverse == this.toListR(depth)
  )

  def toListL(): List[T] = {
    require(this.isWellFormed)
    this.toListL(0)
  }.ensuring(res =>
    res.reverse == this.toListR()
  )

  def toListR(depth: BigInt): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Empty()   => Nil()
      case Single(a) => a.toListR(depth)
      case Deep(prefix, spine, suffix) =>
        suffix.toListR(depth)
          ++ spine.toListR(depth + 1)
          ++ prefix.toListR(depth)
    }
  }

  def toListR(): List[T] = {
    require(this.isWellFormed)
    this.toListR(0)
  }

  /// 3.2 DEQUE OPERATIONS ///

  private def addL(value: Node[T], depth: BigInt): FingerTree[T] = {
    require(depth >= 0 && this.isWellFormed(depth) && value.isWellFormed(depth))
    this match {
      case Empty() => Single(value)
      case Single(existingValue) =>
        Deep(Digit1(value), Empty(), Digit1(existingValue))
      case Deep(Digit1(a), spine, suffix) =>
        Utils.associativeConcat(
          value.toListL(depth),
          a.toListL(depth),
          spine.toListL(depth + 1),
          suffix.toListL(depth)
        )
        Utils.associativeConcat(
          suffix.toListR(depth) ++ spine.toListR(depth + 1),
          a.toListR(depth),
          value.toListR(depth)
        )
        Deep(Digit2(value, a), spine, suffix)
      case Deep(Digit2(a, b), spine, suffix) =>
        Utils.associativeConcat(
          value.toListL(depth),
          a.toListL(depth),
          b.toListL(depth),
          spine.toListL(depth + 1)
        )
        Utils.associativeConcat(
          value.toListL(depth),
          a.toListL(depth) ++ b.toListL(depth) ++ spine.toListL(depth + 1),
          suffix.toListL(depth)
        )
        Utils.associativeConcat(
          suffix.toListR(depth) ++ spine.toListR(depth + 1),
          b.toListR(depth),
          a.toListR(depth),
          value.toListR(depth)
        )
        Deep(Digit3(value, a, b), spine, suffix)
      case Deep(Digit3(a, b, c), spine, suffix) =>
        Utils.associativeConcat(
          value.toListL(depth),
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth)
        )
        Utils.associativeConcat(
          value.toListL(depth),
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth),
          spine.toListL(depth + 1),
          suffix.toListL(depth)
        )
        Utils.associativeConcat(
          suffix.toListR(depth) ++ spine.toListR(depth + 1),
          c.toListR(depth) ++ b.toListR(depth) ++ a.toListR(depth),
          value.toListR(depth)
        )
        Utils.associativeConcat(
          suffix.toListR(depth) ++ spine.toListR(depth + 1),
          c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth),
          value.toListR(depth)
        )
        Deep(Digit4(value, a, b, c), spine, suffix)
      case Deep(Digit4(a, b, c, d), spine, suffix) =>
        Utils.associativeConcat(
          value.toListL(depth),
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth)
            ++ d.toListL(depth),
          spine.toListL(depth + 1),
          suffix.toListL(depth)
        )
        Utils.associativeConcat(
          value.toListL(depth),
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth),
          d.toListL(depth),
          spine.toListL(depth + 1)
        )
        Utils.associativeConcat(
          value.toListL(depth),
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth)
        )
        Utils.associativeConcat(
          value.toListL(depth) ++ a.toListL(depth),
          b.toListL(depth) ++ c.toListL(depth),
          d.toListL(depth),
          spine.toListL(depth + 1)
        )
        Utils.associativeConcat(
          suffix.toListR(depth),
          spine.toListR(depth + 1),
          d.toListR(depth) ++ c.toListR(depth) ++ b.toListR(depth)
        )
        Utils.associativeConcat(
          suffix.toListR(depth) ++ spine.toListR(depth + 1),
          d.toListR(depth) ++ c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth),
          value.toListR(depth)
        )
        Deep(Digit2(value, a), spine.addL(Node3(b, c, d), depth + 1), suffix)
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && res.toListL(depth) == value.toListL(depth) ++ this.toListL(depth)
      && res.toListR(depth) == this.toListR(depth) ++ value.toListR(depth)
  )

  // preprends the list to the tree
  private def addL(elems: List[Node[T]], depth: BigInt): FingerTree[T] = {
    require(
      depth >= 0
        && this.isWellFormed(depth)
        && elems.forall(_.isWellFormed(depth))
    )
    elems match {
      case Nil() => this
      case Cons(h, t) => {
        Utils.associativeConcat(
          h.toListL(depth),
          Utils.toListL(t, depth),
          this.toListL(depth)
        )
        Utils.associativeConcat(
          this.toListR(depth),
          Utils.toListR(t, depth),
          h.toListR(depth)
        )
        this.addL(t, depth).addL(h, depth)
      }
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && res
        .toListL(depth) == Utils.toListL(elems, depth) ++ this.toListL(depth)
      && res
        .toListR(depth) == this.toListR(depth) ++ Utils.toListR(elems, depth)
  )

  def addL(value: T): FingerTree[T] = {
    require(this.isWellFormed)
    this.addL(Leaf(value), 0)
  }.ensuring(res =>
    res.isWellFormed
      && res.toListL(0) == value :: this.toListL(0)
      && res.toListR(0) == this.toListR(0) :+ value
  )

  private def addR(value: Node[T], depth: BigInt): FingerTree[T] = {
    require(depth >= 0 && this.isWellFormed(depth) && value.isWellFormed(depth))
    this match {
      case Empty() => Single(value)
      case Single(existingValue) =>
        Deep(Digit1(existingValue), Empty(), Digit1(value))
      case Deep(prefix, spine, Digit1(a)) =>
        Utils.associativeConcat(
          value.toListR(depth),
          a.toListR(depth),
          spine.toListR(depth + 1),
          prefix.toListR(depth)
        )
        Utils.associativeConcat(
          prefix.toListL(depth) ++ spine.toListL(depth + 1),
          a.toListL(depth),
          value.toListL(depth)
        )
        Deep(prefix, spine, Digit2(a, value))
      case Deep(prefix, spine, Digit2(a, b)) =>
        Utils.associativeConcat(
          value.toListR(depth),
          b.toListR(depth),
          a.toListR(depth),
          spine.toListR(depth + 1)
        )
        Utils.associativeConcat(
          value.toListR(depth),
          b.toListR(depth) ++ a.toListR(depth) ++ spine.toListR(depth + 1),
          prefix.toListR(depth)
        )
        Utils.associativeConcat(
          prefix.toListL(depth) ++ spine.toListL(depth + 1),
          a.toListL(depth),
          b.toListL(depth),
          value.toListL(depth)
        )
        Deep(prefix, spine, Digit3(a, b, value))
      case Deep(prefix, spine, Digit3(a, b, c)) =>
        Utils.associativeConcat(
          value.toListR(depth),
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )
        Utils.associativeConcat(
          value.toListR(depth),
          c.toListR(depth) ++ b.toListR(depth) ++ a.toListR(depth),
          spine.toListR(depth + 1),
          prefix.toListR(depth)
        )
        Utils.associativeConcat(
          prefix.toListL(depth) ++ spine.toListL(depth + 1),
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth),
          value.toListL(depth)
        )
        Utils.associativeConcat(
          prefix.toListL(depth) ++ spine.toListL(depth + 1),
          a.toListL(depth) ++ b.toListL(depth),
          c.toListL(depth),
          value.toListL(depth)
        )
        Deep(prefix, spine, Digit4(a, b, c, value))
      case Deep(prefix, spine, Digit4(a, b, c, d)) =>
        Utils.associativeConcat(
          value.toListR(depth),
          d.toListR(depth) ++ c.toListR(depth) ++ b.toListR(depth)
            ++ a.toListR(depth),
          spine.toListR(depth + 1),
          prefix.toListR(depth)
        )
        Utils.associativeConcat(
          value.toListR(depth),
          d.toListR(depth) ++ c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth),
          spine.toListR(depth + 1)
        )
        Utils.associativeConcat(
          value.toListR(depth),
          d.toListR(depth),
          c.toListR(depth),
          b.toListR(depth)
        )
        Utils.associativeConcat(
          value.toListR(depth) ++ d.toListR(depth),
          c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth),
          spine.toListR(depth + 1)
        )
        Utils.associativeConcat(
          prefix.toListL(depth),
          spine.toListL(depth + 1),
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth)
        )
        Utils.associativeConcat(
          prefix.toListL(depth) ++ spine.toListL(depth + 1),
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth),
          d.toListL(depth),
          value.toListL(depth)
        )
        Deep(prefix, spine.addR(Node3(a, b, c), depth + 1), Digit2(d, value))
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && res.toListR(depth) == value.toListR(depth) ++ this.toListR(depth)
      && res.toListL(depth) == this.toListL(depth) ++ value.toListL(depth)
  )

  // appends the list to the tree
  private def addR(elems: List[Node[T]], depth: BigInt): FingerTree[T] = {
    require(
      depth >= 0
        && this.isWellFormed(depth)
        && elems.forall(_.isWellFormed(depth))
    )
    elems match {
      case Nil() => this
      case Cons(h, t) => {
        Utils.associativeConcat(
          Utils.toListR(t, depth),
          h.toListR(depth),
          this.toListR(depth)
        )
        Utils.associativeConcat(
          this.toListL(depth),
          h.toListL(depth),
          Utils.toListL(t, depth)
        )
        this.addR(h, depth).addR(t, depth)
      }
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && res
        .toListR(depth) == Utils.toListR(elems, depth) ++ this.toListR(depth)
      && res
        .toListL(depth) == this.toListL(depth) ++ Utils.toListL(elems, depth)
  )

  def addR(value: T): FingerTree[T] = {
    require(this.isWellFormed)
    this.addR(Leaf(value), 0)
  }.ensuring(res =>
    res.isWellFormed
      && res.toListR(0) == value :: this.toListR(0)
      && res.toListL(0) == this.toListL(0) :+ value
  )

  def viewL: View[T] = {
    require(this.isWellFormed)
    this match {
      case Empty()             => NilV()
      case Single(Leaf(value)) => ConsV(value, Empty())
      case Single(_)           => ???
      case Deep(prefix, spine, suffix) =>
        prefix.headL(0) match {
          case Leaf(value) =>
            ConsV(
              value,
              Utils.deepL(prefix.tailL(0), spine, suffix, 0)
            )
          case _ => ???
        }
    }
  }.ensuring(res =>
    res.isEmpty == this.isEmpty
      && (res match {
        case NilV() => true
        case ConsV(head, rest) =>
          rest.isWellFormed
          && head == this.toListL().head
          && head == this.toListR().last
          && rest.toListL() == this.toListL().tail
      })
  )

  def viewR: View[T] = {
    require(this.isWellFormed)
    this match {
      case Empty()             => NilV()
      case Single(Leaf(value)) => ConsV(value, Empty())
      case Single(_)           => ???
      case Deep(prefix, spine, suffix) =>
        suffix.headR(0) match {
          case Leaf(value) =>
            ConsV(
              value,
              Utils.deepR(prefix, spine, suffix.tailR(0), 0)
            )
          case _ => ???
        }
    }
  }.ensuring(res =>
    res.isEmpty == this.isEmpty
      && (res match {
        case NilV() => true
        case ConsV(head, rest) =>
          rest.isWellFormed
          && head == this.toListR().head
          && head == this.toListL().last
          && rest.toListR() == this.toListR().tail
      })
  )

  def headL: Option[T] = {
    require(this.isWellFormed)
    this match {
      case Empty()         => None[T]()
      case Single(Leaf(e)) => Some(e)
      case Single(_)       => ???
      case Deep(prefix, spine, suffix) =>
        prefix.headL(0) match {
          case Leaf(value) =>
            Utils.reverseHead(this.toListL())
            Some(value)
          case _ => ???
        }
    }
  }.ensuring(res =>
    res.isDefined != this.isEmpty
      && res == this.toListL().headOption
      && res == this.toListR().lastOption
  )

  def headR: Option[T] = {
    require(this.isWellFormed)
    this match {
      case Empty()         => None()
      case Single(Leaf(e)) => Some(e)
      case Single(_)       => ???
      case Deep(prefix, spine, suffix) =>
        suffix.headR(0) match {
          case Leaf(value) =>
            Utils.reverseHead(this.toListR())
            Utils.treeToListRReverse(this, 0)
            Some(value)
          case _ => ???
        }
    }
  }.ensuring(res =>
    res.isDefined != this.isEmpty
      && res == this.toListR().headOption
      && res == this.toListL().lastOption
  )

  def tailL: Option[FingerTree[T]] = {
    require(this.isWellFormed)
    this.viewL match {
      case ConsV(_, rest) =>
        check(!this.isEmpty)
        Some(rest)
      case NilV() => None()
    }
  }.ensuring(res =>
    res.isDefined != this.isEmpty
      && (res match {
        case None() => true
        case Some(rest) =>
          rest.isWellFormed
          && rest.toListL() == this.toListL().tail
      })
  )

  def tailR: Option[FingerTree[T]] = {
    require(this.isWellFormed)
    this.viewR match {
      case ConsV(_, rest) =>
        check(!this.isEmpty)
        Some(rest)
      case NilV() => None()
    }
  }.ensuring(res =>
    res.isDefined != this.isEmpty
      && (res match {
        case None() => true
        case Some(rest) =>
          rest.isWellFormed
          && rest.toListR() == this.toListR().tail
      })
  )

  def isEmpty(depth: BigInt): Boolean = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Empty() => true
      case _       => false
    }
  }.ensuring(res =>
    res == this.toListL(depth).isEmpty
      && res == this.toListR(depth).isEmpty
  )

  def isEmpty: Boolean = {
    require(this.isWellFormed)
    this.isEmpty(0)
  }.ensuring(res =>
    res == this.toListL().isEmpty
      && res == this.toListR().isEmpty
  )

  /// 3.3 CONCATENATION ///

  private def concat(
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
    decreases(tree1)
    (tree1, tree2) match {
      case (Empty(), _) => tree2.addL(elems, depth)
      case (_, Empty()) => tree1.addR(elems, depth)
      case (Single(e), _) =>
        Utils.associativeConcat(
          tree1.toListL(depth),
          Utils.toListL(elems, depth),
          tree2.toListL(depth)
        )
        tree2.addL(elems, depth).addL(e, depth)
      case (_, Single(e)) =>
        Utils.associativeConcat(
          tree2.toListR(depth),
          Utils.toListR(elems, depth),
          tree1.toListR(depth)
        )
        tree1.addR(elems, depth).addR(e, depth)
      case (Deep(prefix1, spine1, suffix1), Deep(prefix2, spine2, suffix2)) =>
        val elemsTree1 = suffix1.toNodeList(depth)
        val elemsTree2 = prefix2.toNodeList(depth)
        Utils.forallConcat(elemsTree1, elems, _.isWellFormed(depth))
        Utils.forallConcat(
          elemsTree1 ++ elems,
          elemsTree2,
          _.isWellFormed(depth)
        )

        Utils.associativeToListL(elemsTree1, elems, depth)
        Utils.associativeToListL(elemsTree1 ++ elems, elemsTree2, depth)
        Utils.associativeConcat(
          prefix1.toListL(depth),
          spine1.toListL(depth + 1),
          suffix1.toListL(depth) ++ Utils.toListL(elems, depth)
            ++ prefix2.toListL(depth),
          spine2.toListL(depth + 1)
        )
        Utils.associativeConcat(
          prefix1.toListL(depth) ++ spine1.toListL(depth + 1),
          suffix1.toListL(depth),
          Utils.toListL(elems, depth),
          prefix2.toListL(depth)
        )
        Utils.associativeConcat(
          prefix1.toListL(depth) ++ spine1.toListL(depth + 1)
            ++ suffix1.toListL(depth),
          Utils.toListL(elems, depth),
          prefix2.toListL(depth),
          spine2.toListL(depth + 1)
        )
        Utils.associativeConcat(
          prefix1.toListL(depth) ++ spine1.toListL(depth + 1)
            ++ suffix1.toListL(depth),
          Utils.toListL(elems, depth),
          prefix2.toListL(depth) ++ spine2.toListL(depth + 1),
          suffix2.toListL(depth)
        )

        Utils.associativeToListR(elemsTree1, elems, depth)
        Utils.associativeToListR(elemsTree1 ++ elems, elemsTree2, depth)
        Utils.associativeConcat(
          Utils.toListR(elemsTree2, depth),
          Utils.toListR(elems, depth),
          Utils.toListR(elemsTree1, depth)
        )

        Utils.associativeConcat(
          suffix2.toListR(depth),
          spine2.toListR(depth + 1),
          prefix2.toListR(depth) ++ Utils.toListR(elems, depth)
            ++ suffix1.toListR(depth),
          spine1.toListR(depth + 1)
        )
        Utils.associativeConcat(
          suffix2.toListR(depth) ++ spine2.toListR(depth + 1),
          prefix2.toListR(depth),
          Utils.toListR(elems, depth),
          suffix1.toListR(depth)
        )
        Utils.associativeConcat(
          suffix2.toListR(depth) ++ spine2.toListR(depth + 1)
            ++ prefix2.toListR(depth),
          Utils.toListR(elems, depth),
          suffix1.toListR(depth),
          spine1.toListR(depth + 1)
        )
        Utils.associativeConcat(
          suffix2.toListR(depth) ++ spine2.toListR(depth + 1)
            ++ prefix2.toListR(depth),
          Utils.toListR(elems, depth),
          suffix1.toListR(depth) ++ spine1.toListR(depth + 1),
          prefix1.toListR(depth)
        )

        val elemsRec = elemsTree1 ++ elems ++ elemsTree2
        val newElems = Utils.toNodes(elemsRec, depth)
        Deep(prefix1, concat(spine1, newElems, spine2, depth + 1), suffix2)
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && res.toListL(depth) == tree1.toListL(depth)
      ++ Utils.toListL(elems, depth)
      ++ tree2.toListL(depth)
      && res.toListR(depth) == tree2.toListR(depth)
      ++ Utils.toListR(elems, depth)
      ++ tree1.toListR(depth)
  )

  def ++[T](tree1: FingerTree[T], tree2: FingerTree[T]): FingerTree[T] = {
    require(tree1.isWellFormed && tree2.isWellFormed)
    tree1.concat(tree2)
  }.ensuring(res =>
    res.isWellFormed
      && res.toListL() == tree1.toListL() ++ tree2.toListL()
      && res.toListR() == tree2.toListR() ++ tree1.toListR()
  )

  def concat(tree: FingerTree[T]): FingerTree[T] = {
    require(this.isWellFormed && tree.isWellFormed)
    concat(this, Nil(), tree, 0)
  }.ensuring(res =>
    res.isWellFormed
      && res.toListL() == this.toListL() ++ tree.toListL()
      && res.toListR() == tree.toListR() ++ this.toListR()
  )

object Utils {

  // Lemmas

  def associativeToListL[T](
      l1: List[Node[T]],
      l2: List[Node[T]],
      depth: BigInt
  ): Boolean = {
    require(
      depth >= 0
        && l1.forall(_.isWellFormed(depth))
        && l2.forall(_.isWellFormed(depth))
    )
    forallConcat(l1, l2, _.isWellFormed(depth))
    toListL(l1 ++ l2, depth) == toListL(l1, depth)
      ++ toListL(l2, depth) because {
        l1 match {
          case Cons(h, t) =>
            associativeToListL(t, l2, depth)
            associativeConcat(
              h.toListL(depth),
              toListL(t, depth),
              toListL(l2, depth)
            )
          case Nil() => toListL(l1, depth) == Nil[T]()
        }
      }
  }.holds

  def associativeToListR[T](
      l1: List[Node[T]],
      l2: List[Node[T]],
      depth: BigInt
  ): Boolean = {
    require(
      depth >= 0
        && l1.forall(_.isWellFormed(depth))
        && l2.forall(_.isWellFormed(depth))
    )
    forallConcat(l1, l2, _.isWellFormed(depth))
    toListR(l1 ++ l2, depth) == toListR(l2, depth)
      ++ toListR(l1, depth) because {
        l1 match {
          case Cons(h, t) =>
            associativeToListR(t, l2, depth)
            associativeConcat(
              toListR(l2, depth),
              toListR(t, depth),
              h.toListR(depth)
            )
          case Nil() => toListR(l1, depth) == Nil[T]()
        }
      }
  }.holds

  def associativeConcat[T](
      l1: List[T],
      l2: List[T],
      l3: List[T]
  ): Boolean = {
    (l1 ++ l2) ++ l3 == l1 ++ (l2 ++ l3) because {
      l1 match {
        case Nil()      => (Nil() ++ l2) ++ l3 == Nil() ++ (l2 ++ l3)
        case Cons(h, t) => associativeConcat(t, l2, l3)
      }
    }
  }.holds

  def associativeConcat[T](
      l1: List[T],
      l2: List[T],
      l3: List[T],
      l4: List[T]
  ): Boolean = {
    val res = (l1 ++ l2) ++ (l3 ++ l4)
    res == ((l1 ++ l2) ++ l3) ++ l4
    && res == (l1 ++ (l2 ++ l3)) ++ l4
    && res == l1 ++ ((l2 ++ l3) ++ l4)
    && res == l1 ++ (l2 ++ (l3 ++ l4)) because {
      l1 match {
        case Nil()      => associativeConcat(l2, l3, l4)
        case Cons(h, t) => associativeConcat(t, l2, l3, l4)
      }
    }
  }.holds

  def forallConcat[T](
      l1: List[T],
      l2: List[T],
      p: T => Boolean
  ): Boolean = {
    require(l1.forall(p) && l2.forall(p))
    (l1 ++ l2).forall(p) because {
      l1 match {
        case Nil()      => l2.forall(p)
        case Cons(h, t) => p(h) && forallConcat(t, l2, p)
      }
    }
  }.holds

  def lastConcat[T](l1: List[T], l2: List[T]): Boolean = {
    require(!l2.isEmpty)
    (l1 ++ l2).lastOption == l2.lastOption because {
      l1 match {
        case Nil()      => l1 ++ l2 == l2
        case Cons(h, t) => lastConcat(t, l2)
      }
    }
  }.holds

  def headConcat[T](l1: List[T], l2: List[T]): Boolean = {
    require(!l1.isEmpty)
    (l1 ++ l2).head == l1.head
  }.holds

  def appendConcat[T](l1: List[T], l2: List[T], e: T): Boolean = {
    l1 ++ (l2 :+ e) == (l1 ++ l2) :+ e because {
      l1 match {
        case Cons(h, t) => appendConcat(t, l2, e)
        case Nil() => trivial
      }
    }
  }.holds

  def reverseAppend[T](l1: List[T], e: T): Boolean = {
    (l1 :+ e).reverse == e :: l1.reverse because {
      l1 match {
        case Cons(h, t) => reverseAppend(t, e)
        case Nil() => trivial
      }
    }
  }.holds

  def reverseSymmetry[T](l1: List[T]): Boolean = {
    l1.reverse.reverse == l1 because {
      l1 match {
        case Cons(h, t) =>
          reverseSymmetry(t)
          reverseAppend(t.reverse, h)
        case Nil() => trivial
      }
    }
  }.holds

  def reverseConcat[T](l1: List[T], l2: List[T]): Boolean = {
    (l1 ++ l2).reverse == l2.reverse ++ l1.reverse because {
      l1 match {
        case Cons(h, t) =>
          appendConcat(l2.reverse, t.reverse, h) // l2.reverse ++ l1.reverse == (l2.reverse ++ t.reverse) :+ h
          reverseConcat(t, l2) // (t ++ l2).reverse == l2.reverse ++ t.reverse
        case Nil() => trivial
      }
    }
  }.holds

  def appendLast[T](l: List[T], e: T): Boolean = {
    (l :+ e).lastOption == Some[T](e) because {
      l match {
        case Nil() => trivial
        case Cons(_, t) => appendLast(t, e)
      }
    }
  }.holds

  def reverseHead[T](l: List[T]): Boolean = {
    l.reverse.lastOption == l.headOption because {
      l match {
        case Cons(h, t) =>
          check(l.reverse == t.reverse :+ h)
          appendLast(t.reverse, h) // (t.reverse :+ h).last == h
        case Nil() => trivial
      }
    }
  }.holds

  // Helper functions

  def toListL[T](elems: List[Node[T]], depth: BigInt): List[T] = {
    require(depth >= 0 && elems.forall(_.isWellFormed(depth)))
    elems match {
      case Cons(head, tail) =>
        Utils.reverseConcat(head.toListL(depth), toListL(tail, depth))
        // Utils.associativeConcat(
        //   toListR(tail, depth),
        //   head.toListR(depth),
        // )
        head.toListL(depth) ++ toListL(tail, depth)
      case Nil()            => Nil()
    }
  }.ensuring(res =>
    res.reverse == toListR(elems, depth)
  )

  def toListR[T](elems: List[Node[T]], depth: BigInt): List[T] = {
    require(depth >= 0 && elems.forall(_.isWellFormed(depth)))
    elems match {
      case Cons(head, tail) => toListR(tail, depth) ++ head.toListR(depth)
      case Nil()            => Nil()
    }
  }

  // FingerTree lemmas
  def nodesToListRReverse[T](node: Node[T], depth: BigInt): Boolean = {
    require(depth >= 0 && node.isWellFormed(depth))
    node.toListL(depth) == node.toListR(depth).reverse because reverseSymmetry(node.toListL(depth) )
  }.holds

  def nodeListToListRReverse[T](elems: List[Node[T]], depth: BigInt): Boolean = {
    require(depth >= 0 && elems.forall(_.isWellFormed(depth)))
    toListL(elems, depth) == toListR(elems, depth).reverse because reverseSymmetry(toListL(elems, depth))
  }.holds

  def digitToListRReverse[T](digit: Digit[T], depth: BigInt): Boolean = {
    require(depth >= 0 && digit.isWellFormed(depth))
    digit.toListL(depth) == digit.toListR(depth).reverse because reverseSymmetry(digit.toListL(depth) )
  }.holds

  def treeToListRReverse[T](tree: FingerTree[T], depth: BigInt): Boolean = {
    require(depth >= 0 && tree.isWellFormed(depth))
    tree.toListL(depth) == tree.toListR(depth).reverse because reverseSymmetry(tree.toListL(depth) )
  }.holds

  // FingerTree helper functions

  def toNodes[T](elems: List[Node[T]], depth: BigInt): List[Node[T]] = {
    require(
      depth >= 0
        && elems.size >= 2
        && elems.forall(_.isWellFormed(depth))
    )
    elems match {
      case Nil()                   => ???
      case Cons(a, Nil())          => ???
      case Cons(a, Cons(b, Nil())) => List(Node2(a, b))
      case Cons(a, Cons(b, Cons(c, Nil()))) =>
        associativeConcat(
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth)
        )
        List[Node[T]](Node3(a, b, c))
      case Cons(a, Cons(b, Cons(c, Cons(d, Nil())))) =>
        associativeConcat(
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth),
          d.toListL(depth)
        )
        associativeConcat(
          d.toListR(depth),
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )
        check(
          toListL(Cons(c, Cons(d, Nil())), depth) == c.toListL(depth) ++ d
            .toListL(depth)
        )
        check(
          toListR(Cons(c, Cons(d, Nil())), depth) == d.toListR(depth)
            ++ c.toListR(depth)
        )
        List[Node[T]](Node2(a, b), Node2(c, d))
      case Cons(a, Cons(b, Cons(c, tail))) => {
        associativeConcat(
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth),
          toListL(tail, depth)
        )
        associativeConcat(
          toListR(tail, depth),
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )
        Cons(Node3(a, b, c), toNodes(tail, depth))
      }
    }
  }.ensuring(res =>
    res.forall(_.isWellFormed(depth + 1))
      && toListL(res, depth + 1) == toListL(elems, depth)
      && toListR(res, depth + 1) == toListR(elems, depth)
  )

  def deepL[T](
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
  }.ensuring(res =>
    res.isWellFormed(depth)
      && {
        val prefix = prefixTail match {
          case Some(pref) => pref.toListL(depth)
          case None()     => List()
        }
        res.toListL(depth) == prefix
          ++ spine.toListL(depth + 1)
          ++ suffix.toListL(depth)
      }
  )

  def deepR[T](
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
  }.ensuring(res =>
    res.isWellFormed(depth)
      && {
        val suffix = suffixTail match {
          case Some(suff) => suff.toListR(depth)
          case None()     => List()
        }
        res.toListR(depth) == suffix
          ++ spine.toListR(depth + 1)
          ++ prefix.toListR(depth)
      }
  )
}

final case class Empty[T]() extends FingerTree[T]
final case class Single[T](value: Node[T]) extends FingerTree[T]
final case class Deep[T](
    prefix: Digit[T],
    spine: FingerTree[T],
    suffix: Digit[T]
) extends FingerTree[T]

sealed trait View[T]:
  def isEmpty: Boolean =
    this match {
      case NilV()      => true
      case ConsV(_, _) => false
    }

final case class NilV[T]() extends View[T]
final case class ConsV[T](value: T, rest: FingerTree[T]) extends View[T]
