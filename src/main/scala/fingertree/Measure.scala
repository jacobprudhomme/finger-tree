package fingertree

trait Measure[T, M] {
  def zero: M

  def apply(c: T): M

  def |+|(a: M, b: M): M

  final def |+|(elems: M*): M = elems.foldLeft(zero)(|+|)
}
