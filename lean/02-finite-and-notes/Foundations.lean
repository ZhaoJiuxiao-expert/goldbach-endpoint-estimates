import Std

namespace Goldbach

/-- The usual elementary definition of primality, stated without a library dependency. -/
def Prime (n : Nat) : Prop :=
  2 ≤ n ∧ ∀ a b : Nat, a * b = n → a = 1 ∨ b = 1

def HasPair (n : Nat) : Prop :=
  ∃ p q : Nat, Prime p ∧ Prime q ∧ p + q = n

def StrongGoldbach : Prop :=
  ∀ n : Nat, 4 ≤ n → n % 2 = 0 → HasPair n

def factorial : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factorial k

theorem divisor_of_factorial {a k : Nat} (ha : 0 < a) (hak : a ≤ k) :
    a ∣ factorial k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases h : a = k + 1
    · subst a
      exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_trans (ih (by omega)) (Nat.dvd_mul_left _ _)

/-- A small, kernel-computable primality certificate. The gcd is taken only
    after bounding the smaller factor of any nontrivial factorization. -/
theorem prime_of_gcd_certificate {n k : Nat} (hn : 2 ≤ n)
    (hsize : n < (k + 1) * (k + 1)) (hc : Nat.gcd n (factorial k) = 1) :
    Prime n := by
  refine ⟨hn, ?_⟩
  intro a b hab
  apply Classical.byContradiction
  intro nontrivial
  have ha : a ≠ 1 := fun h => nontrivial (Or.inl h)
  have hb : b ≠ 1 := fun h => nontrivial (Or.inr h)
  have ha0 : a ≠ 0 := by intro h; simp [h] at hab; omega
  have hb0 : b ≠ 0 := by intro h; simp [h] at hab; omega
  have rule : ∀ d, 0 < d → d ≤ k → d ∣ n → d = 1 := by
    intro d hd hdk hdn
    have hdg := Nat.dvd_gcd hdn (divisor_of_factorial hd hdk)
    rw [hc] at hdg
    exact Nat.eq_one_of_dvd_one hdg
  by_cases h : a ≤ k
  · exact ha (rule a (by omega) h ⟨b, hab.symm⟩)
  · by_cases h' : b ≤ k
    · exact hb (rule b (by omega) h' ⟨a, by simpa [Nat.mul_comm] using hab.symm⟩)
    · have hab' : (k + 1) * (k + 1) ≤ a * b :=
        Nat.mul_le_mul (by omega) (by omega)
      omega

end Goldbach
