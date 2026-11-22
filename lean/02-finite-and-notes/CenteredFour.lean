import Std

namespace Goldbach.CenteredFour

/-- The signed sum over all subsets of `xs` of the positive part of
    `t - 2 * (subset sum)`. The recursion distinguishes omission and inclusion. -/
def doubledCutoff : List Int → Int → Int
  | [], t => max t 0
  | x :: xs, t => doubledCutoff xs t - doubledCutoff xs (t - 2 * x)

/-- At half the total of four ordered nonnegative integer weights, the
    alternating cutoff has a closed form. Doubling the cutoff preserves
    half-integral centers exactly, including when the total is odd. -/
theorem centered_four (a b c d : Int)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    doubledCutoff [a, b, c, d] (a + b + c + d) =
      -(2 * min (2 * a) (max (a + b + c - d) 0)) := by
  -- The three regions are separated by d = a+b+c and a+d = b+c.
  by_cases hlarge : a + b + c ≤ d
  · simp (disch := omega) only [doubledCutoff, Int.max_eq_left,
      Int.max_eq_right, Int.min_eq_left, Int.min_eq_right]
    omega
  · by_cases hpair : a + d ≤ b + c
    all_goals
      simp (disch := omega) only [doubledCutoff, Int.max_eq_left,
        Int.max_eq_right, Int.min_eq_left, Int.min_eq_right]
      omega

#print axioms Goldbach.CenteredFour.centered_four

end Goldbach.CenteredFour
