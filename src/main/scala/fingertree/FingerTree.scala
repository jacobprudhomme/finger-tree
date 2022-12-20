import stainless.lang._
import stainless.collection._
import stainless.proof._

def f(e: BigInt): BigInt = {
  require(e >= 0)
  e + 1
}

def g(o: Option[BigInt]): Boolean = {
  require(o.forall(_ >= 0))
  // complains that the precondition of f isn't checked
  // and generate a counter example which is obviously
  // incorrect
  o.map(f)
  true
}.holds
