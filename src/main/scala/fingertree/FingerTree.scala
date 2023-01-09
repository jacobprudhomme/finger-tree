package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

sealed trait FingerTree[T, M]:

  /// INVARIANT FUNCTIONS ///

  def isWellFormed(depth: BigInt)(implicit m: Measure[T, M]): Boolean = {
    require(depth >= 0)
    this match
      case Empty()       => true
      case Single(value) => value.isWellFormed(depth)
      case Deep(prefix, spine, suffix) =>
        prefix.isWellFormed(depth)
        && suffix.isWellFormed(depth)
        && spine.isWellFormed(depth + 1)
  }

  def isWellFormed(implicit m: Measure[T, M]): Boolean =
    this.isWellFormed(0)

  /// CONVERSION FUNCTIONS ///

  def toTreeL[T, M](
      elems: List[T]
  )(implicit m: Measure[T, M]): FingerTree[T, M] = {
    elems match {
      case Nil()      => Empty()
      case Cons(h, t) => toTreeL(t).addL(h)
    }
  }.ensuring(res =>
    res.isWellFormed
      && res.toListL() == elems
  )

  def toTreeR[T, M](
      elems: List[T]
  )(implicit m: Measure[T, M]): FingerTree[T, M] = {
    elems match {
      case Nil()      => Empty()
      case Cons(h, t) => toTreeR(t).addR(h)
    }
  }.ensuring(res =>
    res.isWellFormed
      && res.toListR() == elems
  )

  def toListL(depth: BigInt)(implicit m: Measure[T, M]): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Empty()   => Nil()
      case Single(a) => a.toListL(depth)
      case Deep(prefix, spine, suffix) =>
        ListLemmas.reverseConcat(
          prefix.toListL(depth),
          spine.toListL(depth + 1)
        )
        ListLemmas.reverseConcat(
          prefix.toListL(depth) ++ spine.toListL(depth + 1),
          suffix.toListL(depth)
        )
        ListLemmas.associativeConcat(
          suffix.toListR(depth),
          spine.toListR(depth + 1),
          prefix.toListR(depth)
        )
        prefix.toListL(depth) ++ spine.toListL(depth + 1)
          ++ suffix.toListL(depth)
    }
  }.ensuring(res => res.reverse == this.toListR(depth))

  def toListL()(implicit m: Measure[T, M]): List[T] = {
    require(this.isWellFormed)
    this.toListL(0)
  }.ensuring(res => res.reverse == this.toListR())

  def toListR(depth: BigInt)(implicit m: Measure[T, M]): List[T] = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Empty()   => Nil()
      case Single(a) => a.toListR(depth)
      case Deep(prefix, spine, suffix) =>
        suffix.toListR(depth) ++ spine.toListR(depth + 1)
          ++ prefix.toListR(depth)
    }
  }

  def toListR()(implicit m: Measure[T, M]): List[T] = {
    require(this.isWellFormed)
    this.toListR(0)
  }

  /// 3.2 DEQUE OPERATIONS ///

  private def addL(value: Node[T, M], depth: BigInt)(implicit
      m: Measure[T, M]
  ): FingerTree[T, M] = {
    require(depth >= 0 && this.isWellFormed(depth) && value.isWellFormed(depth))
    this match {
      case Empty() => Single(value)
      case Single(existingValue) =>
        Deep(Digit1(value), Empty(), Digit1(existingValue))
      case Deep(Digit1(a), spine, suffix) =>
        ListLemmas.associativeConcat(
          value.toListL(depth),
          a.toListL(depth),
          spine.toListL(depth + 1),
          suffix.toListL(depth)
        )
        ListLemmas.associativeConcat(
          suffix.toListR(depth) ++ spine.toListR(depth + 1),
          a.toListR(depth),
          value.toListR(depth)
        )
        Deep(Digit2(value, a), spine, suffix)
      case Deep(Digit2(a, b), spine, suffix) =>
        ListLemmas.associativeConcat(
          value.toListL(depth),
          a.toListL(depth),
          b.toListL(depth),
          spine.toListL(depth + 1)
        )
        ListLemmas.associativeConcat(
          value.toListL(depth),
          a.toListL(depth) ++ b.toListL(depth) ++ spine.toListL(depth + 1),
          suffix.toListL(depth)
        )
        ListLemmas.associativeConcat(
          suffix.toListR(depth) ++ spine.toListR(depth + 1),
          b.toListR(depth),
          a.toListR(depth),
          value.toListR(depth)
        )
        Deep(Digit3(value, a, b), spine, suffix)
      case Deep(Digit3(a, b, c), spine, suffix) =>
        ListLemmas.associativeConcat(
          value.toListL(depth),
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth)
        )
        ListLemmas.associativeConcat(
          value.toListL(depth),
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth),
          spine.toListL(depth + 1),
          suffix.toListL(depth)
        )
        ListLemmas.associativeConcat(
          suffix.toListR(depth) ++ spine.toListR(depth + 1),
          c.toListR(depth) ++ b.toListR(depth) ++ a.toListR(depth),
          value.toListR(depth)
        )
        ListLemmas.associativeConcat(
          suffix.toListR(depth) ++ spine.toListR(depth + 1),
          c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth),
          value.toListR(depth)
        )
        Deep(Digit4(value, a, b, c), spine, suffix)
      case Deep(Digit4(a, b, c, d), spine, suffix) =>
        ListLemmas.associativeConcat(
          value.toListL(depth),
          a.toListL(depth) ++ b.toListL(depth)
            ++ c.toListL(depth) ++ d.toListL(depth),
          spine.toListL(depth + 1),
          suffix.toListL(depth)
        )
        ListLemmas.associativeConcat(
          value.toListL(depth),
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth),
          d.toListL(depth),
          spine.toListL(depth + 1)
        )
        ListLemmas.associativeConcat(
          value.toListL(depth),
          a.toListL(depth),
          b.toListL(depth),
          c.toListL(depth)
        )
        ListLemmas.associativeConcat(
          value.toListL(depth) ++ a.toListL(depth),
          b.toListL(depth) ++ c.toListL(depth),
          d.toListL(depth),
          spine.toListL(depth + 1)
        )
        ListLemmas.associativeConcat(
          suffix.toListR(depth),
          spine.toListR(depth + 1),
          d.toListR(depth) ++ c.toListR(depth) ++ b.toListR(depth)
        )
        ListLemmas.associativeConcat(
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
  private def addL(elems: List[Node[T, M]], depth: BigInt)(implicit
      m: Measure[T, M]
  ): FingerTree[T, M] = {
    require(
      depth >= 0
        && this.isWellFormed(depth)
        && elems.forall(_.isWellFormed(depth))
    )
    elems match {
      case Nil() => this
      case Cons(h, t) => {
        ListLemmas.associativeConcat(
          h.toListL(depth),
          Helpers.toListL(t, depth),
          this.toListL(depth)
        )
        ListLemmas.associativeConcat(
          this.toListR(depth),
          Helpers.toListR(t, depth),
          h.toListR(depth)
        )
        this.addL(t, depth).addL(h, depth)
      }
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && res.toListL(depth) ==
      Helpers.toListL(elems, depth) ++ this.toListL(depth)
      && res.toListR(depth) ==
      this.toListR(depth) ++ Helpers.toListR(elems, depth)
  )

  def addL(value: T)(implicit m: Measure[T, M]): FingerTree[T, M] = {
    require(this.isWellFormed)
    this.addL(Leaf(value), 0)
  }.ensuring(res =>
    res.isWellFormed
      && res.toListL(0) == value :: this.toListL(0)
      && res.toListR(0) == this.toListR(0) :+ value
  )

  private def addR(value: Node[T, M], depth: BigInt)(implicit
      m: Measure[T, M]
  ): FingerTree[T, M] = {
    require(depth >= 0 && this.isWellFormed(depth) && value.isWellFormed(depth))
    this match {
      case Empty() => Single(value)
      case Single(existingValue) =>
        Deep(Digit1(existingValue), Empty(), Digit1(value))
      case Deep(prefix, spine, Digit1(a)) =>
        ListLemmas.associativeConcat(
          value.toListR(depth),
          a.toListR(depth),
          spine.toListR(depth + 1),
          prefix.toListR(depth)
        )
        ListLemmas.associativeConcat(
          prefix.toListL(depth) ++ spine.toListL(depth + 1),
          a.toListL(depth),
          value.toListL(depth)
        )
        Deep(prefix, spine, Digit2(a, value))
      case Deep(prefix, spine, Digit2(a, b)) =>
        ListLemmas.associativeConcat(
          value.toListR(depth),
          b.toListR(depth),
          a.toListR(depth),
          spine.toListR(depth + 1)
        )
        ListLemmas.associativeConcat(
          value.toListR(depth),
          b.toListR(depth) ++ a.toListR(depth) ++ spine.toListR(depth + 1),
          prefix.toListR(depth)
        )
        ListLemmas.associativeConcat(
          prefix.toListL(depth) ++ spine.toListL(depth + 1),
          a.toListL(depth),
          b.toListL(depth),
          value.toListL(depth)
        )
        Deep(prefix, spine, Digit3(a, b, value))
      case Deep(prefix, spine, Digit3(a, b, c)) =>
        ListLemmas.associativeConcat(
          value.toListR(depth),
          c.toListR(depth),
          b.toListR(depth),
          a.toListR(depth)
        )
        ListLemmas.associativeConcat(
          value.toListR(depth),
          c.toListR(depth) ++ b.toListR(depth) ++ a.toListR(depth),
          spine.toListR(depth + 1),
          prefix.toListR(depth)
        )
        ListLemmas.associativeConcat(
          prefix.toListL(depth) ++ spine.toListL(depth + 1),
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth),
          value.toListL(depth)
        )
        ListLemmas.associativeConcat(
          prefix.toListL(depth) ++ spine.toListL(depth + 1),
          a.toListL(depth) ++ b.toListL(depth),
          c.toListL(depth),
          value.toListL(depth)
        )
        Deep(prefix, spine, Digit4(a, b, c, value))
      case Deep(prefix, spine, Digit4(a, b, c, d)) =>
        ListLemmas.associativeConcat(
          value.toListR(depth),
          d.toListR(depth) ++ c.toListR(depth)
            ++ b.toListR(depth) ++ a.toListR(depth),
          spine.toListR(depth + 1),
          prefix.toListR(depth)
        )
        ListLemmas.associativeConcat(
          value.toListR(depth),
          d.toListR(depth) ++ c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth),
          spine.toListR(depth + 1)
        )
        ListLemmas.associativeConcat(
          value.toListR(depth),
          d.toListR(depth),
          c.toListR(depth),
          b.toListR(depth)
        )
        ListLemmas.associativeConcat(
          value.toListR(depth) ++ d.toListR(depth),
          c.toListR(depth) ++ b.toListR(depth),
          a.toListR(depth),
          spine.toListR(depth + 1)
        )
        ListLemmas.associativeConcat(
          prefix.toListL(depth),
          spine.toListL(depth + 1),
          a.toListL(depth) ++ b.toListL(depth) ++ c.toListL(depth)
        )
        ListLemmas.associativeConcat(
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
  private def addR(elems: List[Node[T, M]], depth: BigInt)(implicit
      m: Measure[T, M]
  ): FingerTree[T, M] = {
    require(
      depth >= 0
        && this.isWellFormed(depth)
        && elems.forall(_.isWellFormed(depth))
    )
    elems match {
      case Nil() => this
      case Cons(h, t) => {
        ListLemmas.associativeConcat(
          Helpers.toListR(t, depth),
          h.toListR(depth),
          this.toListR(depth)
        )
        ListLemmas.associativeConcat(
          this.toListL(depth),
          h.toListL(depth),
          Helpers.toListL(t, depth)
        )
        this.addR(h, depth).addR(t, depth)
      }
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && res.toListR(depth) ==
      Helpers.toListR(elems, depth) ++ this.toListR(depth)
      && res.toListL(depth) ==
      this.toListL(depth) ++ Helpers.toListL(elems, depth)
  )

  def addR(value: T)(implicit m: Measure[T, M]): FingerTree[T, M] = {
    require(this.isWellFormed)
    this.addR(Leaf(value), 0)
  }.ensuring(res =>
    res.isWellFormed
      && res.toListR(0) == value :: this.toListR(0)
      && res.toListL(0) == this.toListL(0) :+ value
  )

  def viewL(implicit m: Measure[T, M]): View[T, M] = {
    require(this.isWellFormed)
    this match {
      case Empty()             => NilV()
      case Single(Leaf(value)) => ConsV(value, Empty())
      case Single(_)           => ???
      case Deep(prefix, spine, suffix) =>
        prefix.headL(0) match {
          case Leaf(value) =>
            check(this.headL == Some[T](value))
            ListLemmas.tailConcat(prefix.toListL(0), spine.toListL(1))
            ListLemmas.tailConcat(
              prefix.toListL(0) ++ spine.toListL(1),
              suffix.toListL(0)
            )
            ConsV(
              value,
              Helpers.deepL(prefix.tailL(0), spine, suffix, 0)
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
          && Some[T](head) == this.toListL().headOption
          && Some[T](head) == this.toListR().lastOption
          && rest.toListL() == this.toListL().tail
      })
  )

  def viewR(implicit m: Measure[T, M]): View[T, M] = {
    require(this.isWellFormed)
    this match {
      case Empty()             => NilV()
      case Single(Leaf(value)) => ConsV(value, Empty())
      case Single(_)           => ???
      case Deep(prefix, spine, suffix) =>
        suffix.headR(0) match {
          case Leaf(value) =>
            ListLemmas.tailConcat(suffix.toListR(0), spine.toListR(1))
            ListLemmas.tailConcat(
              suffix.toListR(0) ++ spine.toListR(1),
              prefix.toListR(0)
            )
            ConsV(
              this.headR.get,
              Helpers.deepR(prefix, spine, suffix.tailR(0), 0)
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
          && Some[T](head) == this.toListR().headOption
          && Some[T](head) == this.toListL().lastOption
          && rest.toListR() == this.toListR().tail
      })
  )

  def headL(implicit m: Measure[T, M]): Option[T] = {
    require(this.isWellFormed)
    this match {
      case Empty()         => None[T]()
      case Single(Leaf(e)) => Some(e)
      case Single(_)       => ???
      case Deep(prefix, spine, suffix) =>
        prefix.headL(0) match {
          case Leaf(value) =>
            ListLemmas.reverseHead(this.toListL())
            Some(value)
          case _ => ???
        }
    }
  }.ensuring(res =>
    res.isDefined != this.isEmpty
      && res == this.toListL().headOption
      && res == this.toListR().lastOption
  )

  def headR(implicit m: Measure[T, M]): Option[T] = {
    require(this.isWellFormed)
    this match {
      case Empty()         => None()
      case Single(Leaf(e)) => Some(e)
      case Single(_)       => ???
      case Deep(prefix, spine, suffix) =>
        suffix.headR(0) match {
          case Leaf(value) =>
            ListLemmas.reverseHead(this.toListR())
            FingerTreeLemmas.treeToListRReverse(this, 0)
            Some(value)
          case _ => ???
        }
    }
  }.ensuring(res =>
    res.isDefined != this.isEmpty
      && res == this.toListR().headOption
      && res == this.toListL().lastOption
  )

  def tailL(implicit m: Measure[T, M]): Option[FingerTree[T, M]] = {
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

  def tailR(implicit m: Measure[T, M]): Option[FingerTree[T, M]] = {
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

  def isEmpty(depth: BigInt)(implicit m: Measure[T, M]): Boolean = {
    require(depth >= 0 && this.isWellFormed(depth))
    this match {
      case Empty() => true
      case _       => false
    }
  }.ensuring(res =>
    res == this.toListL(depth).isEmpty
      && res == this.toListR(depth).isEmpty
  )

  def isEmpty(implicit m: Measure[T, M]): Boolean = {
    require(this.isWellFormed)
    this.isEmpty(0)
  }.ensuring(res =>
    res == this.toListL().isEmpty
      && res == this.toListR().isEmpty
  )

  /// 3.3 CONCATENATION ///

  private def concat(
      tree1: FingerTree[T, M],
      elems: List[Node[T, M]],
      tree2: FingerTree[T, M],
      depth: BigInt
  )(implicit m: Measure[T, M]): FingerTree[T, M] = {
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
        ListLemmas.associativeConcat(
          tree1.toListL(depth),
          Helpers.toListL(elems, depth),
          tree2.toListL(depth)
        )
        tree2.addL(elems, depth).addL(e, depth)
      case (_, Single(e)) =>
        ListLemmas.associativeConcat(
          tree2.toListR(depth),
          Helpers.toListR(elems, depth),
          tree1.toListR(depth)
        )
        tree1.addR(elems, depth).addR(e, depth)
      case (Deep(prefix1, spine1, suffix1), Deep(prefix2, spine2, suffix2)) =>
        val elemsTree1 = suffix1.toNodeList(depth)
        val elemsTree2 = prefix2.toNodeList(depth)

        ListLemmas.associativeToListL(elemsTree1, elems, depth)
        ListLemmas.associativeToListL(elemsTree1 ++ elems, elemsTree2, depth)
        ListLemmas.associativeConcat(
          prefix1.toListL(depth),
          spine1.toListL(depth + 1),
          suffix1.toListL(depth) ++ Helpers.toListL(elems, depth)
            ++ prefix2.toListL(depth),
          spine2.toListL(depth + 1)
        )
        ListLemmas.associativeConcat(
          prefix1.toListL(depth) ++ spine1.toListL(depth + 1),
          suffix1.toListL(depth),
          Helpers.toListL(elems, depth),
          prefix2.toListL(depth)
        )
        ListLemmas.associativeConcat(
          prefix1.toListL(depth) ++ spine1.toListL(depth + 1)
            ++ suffix1.toListL(depth),
          Helpers.toListL(elems, depth),
          prefix2.toListL(depth),
          spine2.toListL(depth + 1)
        )
        ListLemmas.associativeConcat(
          prefix1.toListL(depth) ++ spine1.toListL(depth + 1)
            ++ suffix1.toListL(depth),
          Helpers.toListL(elems, depth),
          prefix2.toListL(depth) ++ spine2.toListL(depth + 1),
          suffix2.toListL(depth)
        )

        ListLemmas.associativeToListR(elemsTree1, elems, depth)
        ListLemmas.associativeToListR(elemsTree1 ++ elems, elemsTree2, depth)
        ListLemmas.associativeConcat(
          Helpers.toListR(elemsTree2, depth),
          Helpers.toListR(elems, depth),
          Helpers.toListR(elemsTree1, depth)
        )

        ListLemmas.associativeConcat(
          suffix2.toListR(depth),
          spine2.toListR(depth + 1),
          prefix2.toListR(depth) ++ Helpers.toListR(elems, depth)
            ++ suffix1.toListR(depth),
          spine1.toListR(depth + 1)
        )
        ListLemmas.associativeConcat(
          suffix2.toListR(depth) ++ spine2.toListR(depth + 1),
          prefix2.toListR(depth),
          Helpers.toListR(elems, depth),
          suffix1.toListR(depth)
        )
        ListLemmas.associativeConcat(
          suffix2.toListR(depth) ++ spine2.toListR(depth + 1)
            ++ prefix2.toListR(depth),
          Helpers.toListR(elems, depth),
          suffix1.toListR(depth),
          spine1.toListR(depth + 1)
        )
        ListLemmas.associativeConcat(
          suffix2.toListR(depth) ++ spine2.toListR(depth + 1)
            ++ prefix2.toListR(depth),
          Helpers.toListR(elems, depth),
          suffix1.toListR(depth) ++ spine1.toListR(depth + 1),
          prefix1.toListR(depth)
        )

        ListLemmas.forallConcat(elemsTree1, elems, _.isWellFormed(depth))
        ListLemmas.forallConcat(
          elemsTree1 ++ elems,
          elemsTree2,
          _.isWellFormed(depth)
        )
        val elemsRec = elemsTree1 ++ elems ++ elemsTree2
        val newElems = Helpers.toNodes(elemsRec, depth)
        Deep(prefix1, concat(spine1, newElems, spine2, depth + 1), suffix2)
    }
  }.ensuring(res =>
    res.isWellFormed(depth)
      && res.toListL(depth) == tree1.toListL(depth)
      ++ Helpers.toListL(elems, depth)
      ++ tree2.toListL(depth)
      && res.toListR(depth) == tree2.toListR(depth)
      ++ Helpers.toListR(elems, depth)
      ++ tree1.toListR(depth)
  )

  def ++[T, M](tree1: FingerTree[T, M], tree2: FingerTree[T, M])(implicit
      m: Measure[T, M]
  ): FingerTree[T, M] = {
    require(tree1.isWellFormed && tree2.isWellFormed)
    tree1.concat(tree2)
  }.ensuring(res =>
    res.isWellFormed
      && res.toListL() == tree1.toListL() ++ tree2.toListL()
      && res.toListR() == tree2.toListR() ++ tree1.toListR()
  )

  def concat(
      tree: FingerTree[T, M]
  )(implicit m: Measure[T, M]): FingerTree[T, M] = {
    require(this.isWellFormed && tree.isWellFormed)
    concat(this, Nil(), tree, 0)
  }.ensuring(res =>
    res.isWellFormed
      && res.toListL() == this.toListL() ++ tree.toListL()
      && res.toListR() == tree.toListR() ++ this.toListR()
  )

final case class Empty[T, M]() extends FingerTree[T, M]
final case class Single[T, M](value: Node[T, M]) extends FingerTree[T, M]
final case class Deep[T, M](
    prefix: Digit[T, M],
    spine: FingerTree[T, M],
    suffix: Digit[T, M]
) extends FingerTree[T, M]
