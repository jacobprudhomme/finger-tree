package fingertree

import stainless.lang._
import stainless.collection._
import stainless.proof._

/// This file contains various lemmas used in proofs in the other files.
/// It is split in two different objets:
/// - ListLemmas contains lemmas which are strictly related to stainless'
///   List type
/// - FingerTreeLemmas contains lemmas about the custom types defined in the
///   other files

object ListLemmas {
  /// Proves the associativity of List's concat operation on 3 elements
  def associativeConcat[T](
      l1: List[T],
      l2: List[T],
      l3: List[T]
  ): Boolean = {
    (l1 ++ l2) ++ l3 == l1 ++ (l2 ++ l3) because {
      l1 match {
        case Nil()      => trivial
        case Cons(h, t) => associativeConcat(t, l2, l3)
      }
    }
  }.holds

  /// Proves the associativity of List's concat operation on 4 elements
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

  /// Proves that if two lists verify a predicate for all elements then
  /// their concatenation also does
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

  /// Proves that the last element of the concatenation of a List with a
  /// non-empty List is the last element of the second List
  def lastConcat[T](l1: List[T], l2: List[T]): Boolean = {
    require(!l2.isEmpty)
    (l1 ++ l2).lastOption == l2.lastOption because {
      l1 match {
        case Nil()      => l1 ++ l2 == l2
        case Cons(h, t) => lastConcat(t, l2)
      }
    }
  }.holds

  /// Proves that the first element of the concatenation of a non-empty List
  /// with a List is the first element of the first List
  def headConcat[T](l1: List[T], l2: List[T]): Boolean = {
    require(!l1.isEmpty)
    (l1 ++ l2).head == l1.head
  }.holds

  /// Proves that the tail of the concatenation of a non-empty List with a List
  /// is the concatenation of the tail of the first List with the second List
  def tailConcat[T](l1: List[T], l2: List[T]): Boolean = {
    require(!l1.isEmpty)
    (l1 ++ l2).tail == l1.tail ++ l2
  }.holds

  /// Proves that appending to the concatenation of two Lists is equivalent to
  /// appending to the second List and then concatenating both Lists
  def appendConcat[T](l1: List[T], l2: List[T], e: T): Boolean = {
    l1 ++ (l2 :+ e) == (l1 ++ l2) :+ e because {
      l1 match {
        case Cons(h, t) => appendConcat(t, l2, e)
        case Nil()      => trivial
      }
    }
  }.holds

  /// Proves that appending an element to a List and then reversing is
  /// equivalent to preprending to the reverse of the List
  def reverseAppend[T](l1: List[T], e: T): Boolean = {
    (l1 :+ e).reverse == e :: l1.reverse because {
      l1 match {
        case Cons(h, t) => reverseAppend(t, e)
        case Nil()      => trivial
      }
    }
  }.holds

  /// Proves that reverse is a symmetrical operation
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

  /// Proves that reversing the concatenation of two Lists is equivalent to
  /// concatenating the reverse of the second List with the reverse of the
  /// first
  def reverseConcat[T](l1: List[T], l2: List[T]): Boolean = {
    (l1 ++ l2).reverse == l2.reverse ++ l1.reverse because {
      l1 match {
        case Cons(h, t) =>
          appendConcat(l2.reverse, t.reverse, h)
          reverseConcat(t, l2)
        case Nil() => trivial
      }
    }
  }.holds

  /// Proves that the last element of a List to which we appended an element
  /// is the appended element.
  def appendLast[T](l: List[T], e: T): Boolean = {
    (l :+ e).lastOption == Some[T](e) because {
      l match {
        case Nil()      => trivial
        case Cons(_, t) => appendLast(t, e)
      }
    }
  }.holds

  /// Proves that the last element of a reversed List is the first element of
  /// the initial List
  def reverseHead[T](l: List[T]): Boolean = {
    l.reverse.lastOption == l.headOption because {
      l match {
        case Cons(h, t) =>
          check(l.reverse == t.reverse :+ h)
          appendLast(t.reverse, h)
        case Nil() => trivial
      }
    }
  }.holds
}

object FingerTreeLemmas {
  /// Proves that the Helper.toListL operation distributes with the
  /// List concatenation
  def distributeToListLConcat[T](
      l1: List[Node[T]],
      l2: List[Node[T]],
      depth: BigInt
  ): Boolean = {
    require(
      depth >= 0
        && l1.forall(_.isWellFormed(depth))
        && l2.forall(_.isWellFormed(depth))
    )
    ListLemmas.forallConcat(l1, l2, _.isWellFormed(depth))
    Helpers.toListL(l1 ++ l2, depth) ==
      Helpers.toListL(l1, depth) ++ Helpers.toListL(l2, depth) because {
        l1 match {
          case Cons(h, t) =>
            distributeToListLConcat(t, l2, depth)
            ListLemmas.associativeConcat(
              h.toListL(depth),
              Helpers.toListL(t, depth),
              Helpers.toListL(l2, depth)
            )
          case Nil() => Helpers.toListL(l1, depth) == Nil[T]()
        }
      }
  }.holds

  /// Proves that the Helper.toListR operation distributes with the
  /// List concatenation
  def distributeToListRConcat[T](
      l1: List[Node[T]],
      l2: List[Node[T]],
      depth: BigInt
  ): Boolean = {
    require(
      depth >= 0
        && l1.forall(_.isWellFormed(depth))
        && l2.forall(_.isWellFormed(depth))
    )
    ListLemmas.forallConcat(l1, l2, _.isWellFormed(depth))
    Helpers.toListR(l1 ++ l2, depth) ==
      Helpers.toListR(l2, depth) ++ Helpers.toListR(l1, depth) because {
        l1 match {
          case Cons(h, t) =>
            distributeToListRConcat(t, l2, depth)
            ListLemmas.associativeConcat(
              Helpers.toListR(l2, depth),
              Helpers.toListR(t, depth),
              h.toListR(depth)
            )
          case Nil() => Helpers.toListR(l1, depth) == Nil[T]()
        }
      }
  }.holds

  /// Proves that Node.toListL is equivalent to the reverse of Node.toListR
  def nodesToListRReverse[T](node: Node[T], depth: BigInt): Boolean = {
    require(depth >= 0 && node.isWellFormed(depth))
    node.toListL(depth) == node.toListR(depth).reverse because
      ListLemmas.reverseSymmetry(node.toListL(depth))
  }.holds

  /// Proves that Helpers.toListL is equivalent to the reverse
  /// of Helpers.toListR
  def nodeListToListRReverse[T](
      elems: List[Node[T]],
      depth: BigInt
  ): Boolean = {
    require(depth >= 0 && elems.forall(_.isWellFormed(depth)))
    Helpers.toListL(elems, depth) ==
      Helpers.toListR(elems, depth).reverse because
      ListLemmas.reverseSymmetry(Helpers.toListL(elems, depth))
  }.holds

  /// Proves that Digit.toListL is equivalent to the reverse of Digit.toListR
  def digitToListRReverse[T](digit: Digit[T], depth: BigInt): Boolean = {
    require(depth >= 0 && digit.isWellFormed(depth))
    digit.toListL(depth) == digit.toListR(depth).reverse because
      ListLemmas.reverseSymmetry(digit.toListL(depth))
  }.holds

  /// Proves that FingerTree.toListL is equivalent to the reverse of
  /// FingerTree.toListR
  def treeToListRReverse[T](tree: FingerTree[T], depth: BigInt): Boolean = {
    require(depth >= 0 && tree.isWellFormed(depth))
    tree.toListL(depth) == tree.toListR(depth).reverse because
      ListLemmas.reverseSymmetry(tree.toListL(depth))
  }.holds

  /// Proves that concatenating Digit.headL.toListL and Digit.tailL.toListL
  /// is equivalent to Digit.toListL
  def headTailConcatL[T](digit: Digit[T], depth: BigInt): Boolean = {
    require(depth >= 0 && digit.isWellFormed(depth))
    val tailList = digit.tailL(depth) match {
      case Some(tail) => tail.toListL(depth)
      case None()     => List()
    }
    digit.toListL(depth) ==
      digit.headL(depth).toListL(depth) ++ tailList because {
        digit match {
          case Digit1(a)    => trivial
          case Digit2(a, b) => trivial
          case Digit3(a, b, c) =>
            ListLemmas.associativeConcat(
              a.toListL(depth),
              b.toListL(depth),
              c.toListL(depth)
            )
          case Digit4(a, b, c, d) =>
            ListLemmas.associativeConcat(
              a.toListL(depth),
              b.toListL(depth),
              c.toListL(depth),
              d.toListL(depth)
            )
        }
      }
  }.holds

  /// Proves that concatenating Digit.headR.toListR and Digit.tailR.toListR
  /// is equivalent to Digit.toListR
  def headTailConcatR[T](digit: Digit[T], depth: BigInt): Boolean = {
    require(depth >= 0 && digit.isWellFormed(depth))
    val tailList = digit.tailR(depth) match {
      case Some(tail) => tail.toListR(depth)
      case None()     => List()
    }
    digit.toListR(depth) ==
      digit.headR(depth).toListR(depth) ++ tailList because {
        digit match {
          case Digit1(a)    => trivial
          case Digit2(a, b) => trivial
          case Digit3(a, b, c) =>
            ListLemmas.associativeConcat(
              c.toListR(depth),
              b.toListR(depth),
              a.toListR(depth)
            )
          case Digit4(a, b, c, d) =>
            ListLemmas.associativeConcat(
              d.toListR(depth),
              c.toListR(depth),
              b.toListR(depth),
              a.toListR(depth)
            )
        }
      }
  }.holds
}
