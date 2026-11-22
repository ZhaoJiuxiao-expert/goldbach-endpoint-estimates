import Std

namespace Goldbach.EndpointMajorant

/-- Binomial coefficients defined by Pascal's recurrence, vanishing for k > n. -/
def binom : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => binom n k + binom n (k + 1)

private theorem binom_one (n : Nat) : binom n 1 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [binom, ih, Nat.add_comm]

/-- Two Pascal steps give the exact nonnegative slack in the majorant. -/
theorem endpoint_surplus (n : Nat) :
    binom n 3 + 3 * binom n 5 =
      (n - 2) + 2 * binom n 4 + 4 * binom (n - 2) 4 + 3 * binom (n - 2) 5 := by
  match n with
  | 0 => decide
  | 1 => decide
  | m + 2 =>
    simp only [Nat.add_sub_cancel, binom, Nat.reduceAdd, binom_one]
    omega

/-- The binomial expression uses signed subtraction. Its lower bound is the
    positive part of n - 2, given by truncated subtraction on `Nat`. -/
theorem endpoint_majorant (n : Nat) :
    ((n - 2 : Nat) : Int) ≤
      (binom n 3 : Int) - 2 * (binom n 4 : Int) + 3 * (binom n 5 : Int) := by
  have h := endpoint_surplus n
  omega

#print axioms Goldbach.EndpointMajorant.endpoint_surplus
#print axioms Goldbach.EndpointMajorant.endpoint_majorant

end Goldbach.EndpointMajorant
