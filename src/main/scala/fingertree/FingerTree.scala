package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

private sealed trait Node[T]:
  def content(depth: BigInt): Set[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Leaf(a) => Set(a)
      case Node2(left, right) =>
        left.content(depth - 1) ++ right.content(depth - 1)
      case Node3(left, middle, right) =>
        left.content(depth - 1)
          ++ middle.content(depth - 1)
          ++ right.content(depth - 1)
    }
  }.ensuring(!_.isEmpty)

  def toListL(depth: BigInt): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Leaf(a) => List(a)
      case Node2(left, right) =>
        left.toListL(depth - 1) ++ right.toListL(depth - 1)
      case Node3(left, middle, right) =>
        left.toListL(depth - 1)
          ++ middle.toListL(depth - 1)
          ++ right.toListL(depth - 1)
    }
  }.ensuring(_.content == content(depth))

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

  // this is awful but stainless loves it
  def toNodeList(depth: BigInt): List[Node[T]] = {
    require(depth >= 0 && this.isWellFormed(depth))
    decreases(this)
    this.tailL(depth) match {
      case None()     => List(this.headL(depth))
      case Some(tail) => Cons(this.headL(depth), tail.toNodeList(depth))
    }
  }.ensuring(res => !res.isEmpty && res.forall(_.isWellFormed(depth)))

  def content(depth: BigInt): Set[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    decreases(this)
    this.tailL(depth) match {
      case None() => this.headL(depth).content(depth)
      case Some(tail) =>
        this.headL(depth).content(depth)
          ++ tail.content(depth)
    }
  }.ensuring(!_.isEmpty)

  def toListL(depth: BigInt): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    decreases(this)
    this.tailL(depth) match {
      case None() => this.headL(depth).toListL(depth)
      case Some(tail) =>
        this.headL(depth).toListL(depth)
          ++ tail.toListL(depth)
    }
  }.ensuring(_.content == content(depth))

  def toListR(depth: BigInt): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    decreases(this)
    this.tailR(depth) match {
      case None() => this.headR(depth).toListR(depth)
      case Some(tail) =>
        this.headR(depth).toListR(depth)
          ++ tail.toListR(depth)
    }
  }.ensuring(!_.isEmpty)

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

  def toTreeL[T](elems: List[T]): FingerTree[T] = {
    elems match {
      case Nil()      => Empty()
      case Cons(h, t) => toTreeL(t).addL(h)
    }
  }.ensuring(res => 
  res.isWellFormed && res.content() == elems.content)

  def toTreeR[T](elems: List[T]): FingerTree[T] = {
    elems match {
      case Nil()      => Empty()
      case Cons(h, t) => toTreeR(t).addR(h)
    }
  }.ensuring(res => 
  res.isWellFormed && res.content() == elems.content)

  private def content(depth: BigInt): Set[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Empty() => Set.empty
      case Single(a) => a.content(depth)
      case Deep(prefix, spine, suffix) =>
        prefix.content(depth)
          ++ spine.content(depth + 1)
          ++ suffix.content(depth)
    }
  }

  def content(): Set[T] = {
    require(this.isWellFormed)
    this.content(0)
  }

  private def toListL(depth: BigInt): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Empty()   => Nil()
      case Single(a) => a.toListL(depth)
      case Deep(prefix, spine, suffix) =>
        prefix.toListL(depth)
          ++ spine.toListL(depth + 1)
          ++ suffix.toListL(depth)
    }
  }.ensuring(_.content == content(depth))

  def toListL(): List[T] = {
    require(this.isWellFormed)
    this.toListL(0)
  }.ensuring(_.content == content())

  private def toListR(depth: BigInt): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Empty()   => Nil()
      case Single(a) => a.toListR(depth)
      case Deep(prefix, spine, suffix) =>
        suffix.toListR(depth)
          ++ spine.toListR(depth + 1)
          ++ prefix.toListR(depth)
    }
  }.ensuring(_.content == content(depth))

  def toListR(): List[T] = {
    require(this.isWellFormed)
    this.toListR(0)
  }.ensuring(_.content == content())

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
  }.ensuring {
    case NilV()         => true
    case ConsV(_, rest) => rest.isWellFormed
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
    case NilV()         => true
    case ConsV(_, rest) => rest.isWellFormed
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
  }.ensuring(res => 
  res == toListL().headOption)

  def headR: Option[T] = {
    require(this.isWellFormed)
    this match {
      case Empty()         => None()
      case Single(Leaf(e)) => Some(e)
      case Single(_)       => ??? // not supposed to happen I think ?
      case Deep(_, _, suffix) =>
        suffix.headR(0) match {
          case Leaf(value) => Some(value)
          case _           => ??? // not supposed to happen I think ?
        }
    }
  }.ensuring(_ == toListR().headOption)

  def tailL: Option[FingerTree[T]] = {
    require(this.isWellFormed)
    this.viewL match {
      case ConsV(_, rest) => Some(rest)
      case NilV()         => None()
    }
  }.ensuring(_.forall(_.isWellFormed))

  def tailR: Option[FingerTree[T]] = {
    require(this.isWellFormed)
    this.viewR match {
      case ConsV(_, rest) => Some(rest)
      case NilV()         => None()
    }
  }.ensuring(_.forall(_.isWellFormed))

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
        && elems.forall(_.isWellFormed(depth))
    )
    elems match {
      case Nil()                            => ???
      case Cons(a, Nil())                   => ???
      case Cons(a, Cons(b, Nil()))          => List(Node2(a, b))
      case Cons(a, Cons(b, Cons(c, Nil()))) => List(Node3(a, b, c))
      case Cons(a, Cons(b, Cons(c, Cons(d, Nil())))) =>
        List(Node2(a, b), Node2(c, d))
      case Cons(a, Cons(b, Cons(c, tail))) => {
        Cons(Node3(a, b, c), toNodes(tail, depth))
      }
    }
  }.ensuring(_.forall(_.isWellFormed(depth + 1)))

  private def forallConcat[T](
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
    decreases(tree1)
    (tree1, tree2) match {
      case (Empty(), _)   => tree2.addL(elems, depth)
      case (Single(e), _) => tree2.addL(e, depth).addL(elems, depth)
      case (_, Empty())   => tree1.addR(elems, depth)
      case (_, Single(e)) => tree1.addR(e, depth).addR(elems, depth)
      case (Deep(prefix1, spine1, suffix1), Deep(prefix2, spine2, suffix2)) =>
        val elemsTree1 = suffix1.toNodeList(depth)
        val elemsTree2 = prefix1.toNodeList(depth)
        forallConcat(elemsTree1, elems, _.isWellFormed(depth))
        forallConcat(elemsTree1 ++ elems, elemsTree2, _.isWellFormed(depth))
        val elemsRec = elemsTree1 ++ elems ++ elemsTree2
        Deep(
          prefix1,
          concat(spine1, toNodes(elemsRec, depth), spine2, depth + 1),
          suffix2
        )
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

  /// PROPERTIES ///

  // EMPTY //
  def isEmptyL_law(t: FingerTree[T]): Boolean = {
    require(t.isWellFormed)
    t.toListL().isEmpty == t.isEmpty
  }.holds

  def isEmptyR_law(t: FingerTree[T]): Boolean = {
    require(t.isWellFormed)
    t.toListR().isEmpty == t.isEmpty
  }.holds

  def emptyConcatL(t: FingerTree[T]): Boolean = {
    require(t.isWellFormed)
    t.concat(Empty()).toListL() == t.toListL()
  }.holds

  def emptyConcatR(t: FingerTree[T]): Boolean = {
    require(t.isWellFormed)
    Empty().concat(t).toListR() == t.toListR()
  }.holds

  def isEmpty_concat(t1: FingerTree[T], t2: FingerTree[T]): Boolean = {
    require(t1.isWellFormed && t2.isWellFormed)
    t1.concat(t2).isEmpty == (t1.isEmpty && t2.isEmpty)
  }.holds

  // toTree //
  def toTreeLR(l: List[T]): Boolean = {
    check(toTreeL(l).isWellFormed)
    check(toTreeR(l).isWellFormed)
    toTreeL(l).content() == toTreeR(l).content()
  }.holds

  def toTree_toListL(l: List[T]): Boolean = {
    check(toTreeL(l).isWellFormed)
    toTreeL(l).toListL().content == l.content
  }.holds

  def toTree_toListR(l: List[T]): Boolean = {
    check(toTreeR(l).isWellFormed)
    toTreeR(l).toListR().content == l.content
  }.holds

  // toList //
  def toListLR(t: FingerTree[T]): Boolean = {
    require(t.isWellFormed)
    t.toListL().content == t.toListR().content
  }.holds

  // head //
  def toListL_head(t: FingerTree[T]): Boolean = {
    require(t.isWellFormed)
    t.headL == t.toListL().headOption
  }.holds

  def toListLR_head(t: FingerTree[T]): Boolean = {
    require(t.isWellFormed)
    t.toListL().headOption == t.toListR().lastOption
  }.holds

  def headL_ListL_head(t: FingerTree[T]): Boolean = {
    require(t.isWellFormed)
    t.headL == t.toListL().headOption
  }.holds

  def headL_ListR_last(t: FingerTree[T]): Boolean = {
    require(t.isWellFormed)
    toListLR(t)
    t.headL == t.toListR().lastOption
  }.holds

  def headR_ListR_head(t: FingerTree[T]): Boolean = {
    require(t.isWellFormed)
    t.headR == t.toListR().headOption
  }.holds

  def headR_ListL_last(t: FingerTree[T]): Boolean = {
    require(t.isWellFormed)
    t.headR == t.toListL().lastOption
  }.holds

  def concatHeadL(t1: FingerTree[T], t2: FingerTree[T]): Boolean = {
    require(t1.isWellFormed && t2.isWellFormed)
    t1.concat(t2).headL == t1.headL.orElse(t2.headL) because {
      t1 match {
        case Empty() => emptyConcatHeadL(t2)
        case _       => t1.concat(t2).headL == t1.headL
      }
    }
  }.holds

  def concatHeadR(t1: FingerTree[T], t2: FingerTree[T]): Boolean = {
    require(t1.isWellFormed && t2.isWellFormed)
    t1.concat(t2).headR == t2.headR.orElse(t1.headR) because {
      t2 match {
        case Empty() => emptyConcatHeadR(t1)
        case _       => t1.concat(t2).headR == t2.headR
      }
    }
  }.holds

  def emptyConcatHeadL(t: FingerTree[T]): Boolean = {
    require(t.isWellFormed)
    Empty().concat(t).headL == t.headL
  }.holds

  def emptyConcatHeadR(t: FingerTree[T]): Boolean = {
    require(t.isWellFormed)
    t.concat(Empty()).headR == t.headR
  }.holds

  def addLHeadL(t: FingerTree[T], value: T): Boolean = {
    require(t.isWellFormed)
    // not sure, this looks weird but stainless passed
    t.addL(value).headL == List(value).headOption
  }.holds

  def addRHeadR(t: FingerTree[T], value: T): Boolean = {
    require(t.isWellFormed)
    // not passed
    t.addR(value).headR == List(value).headOption
  }.holds

  // tail //
  def tailL_law(t: FingerTree[T]): Boolean = {
    require(t.isWellFormed && !t.isEmpty)
    isEmptyL_law(t)
    check(!t.viewL.isEmpty)
    t.tailL.get.toListL() == t.toListL().tail
  }.holds

  def tailR_law(t: FingerTree[T]): Boolean = {
    require(t.isWellFormed && !t.isEmpty)
    isEmptyR_law(t)
    check(!t.viewR.isEmpty)
    t.tailR.get.toListR() == t.toListR().tail
  }.holds

  // add //
  def addL_law(t: FingerTree[T], value: T): Boolean = {
    require(t.isWellFormed)
    t.addL(value).toListL().head == value
  }.holds

  def addR_law(t: FingerTree[T], value: T): Boolean = {
    require(t.isWellFormed)
    t.addR(value).toListR().head == value
  }.holds

  // concat //
  def concat_listL(t1: FingerTree[T], t2: FingerTree[T]): Boolean = {
    require(t1.isWellFormed && t2.isWellFormed)
    t1.concat(t2).toListL() == t1.toListL() ++ t2.toListL()
  }.holds

  def concat_listR(t1: FingerTree[T], t2: FingerTree[T]): Boolean = {
    require(t1.isWellFormed && t2.isWellFormed)
    t1.concat(t2).toListR() == t2.toListR() ++ t1.toListR()
  }.holds

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
