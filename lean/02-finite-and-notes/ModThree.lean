import Foundations

namespace Goldbach.ModThree

private theorem prime_nonzero_mod_three {p : Nat} (hp : Prime p) (hne : p ≠ 3) :
    p % 3 ≠ 0 := by
  intro h
  obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero h
  rcases hp.2 3 t ht.symm with h | h
  · omega
  · simp [h] at ht
    exact hne ht

private theorem power_nonzero_mod_three {q : Nat} (hq : q % 3 ≠ 0) (j : Nat) :
    q ^ j % 3 ≠ 0 := by
  have table : ∀ a b : Fin 3, a.val ≠ 0 → b.val ≠ 0 → (a.val * b.val) % 3 ≠ 0 := by decide
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    exact table ⟨q ^ j % 3, Nat.mod_lt _ (by decide)⟩ ⟨q % 3, Nat.mod_lt _ (by decide)⟩ ih hq

private theorem square_mod_three {x : Nat} (hx : x % 3 ≠ 0) : x ^ 2 % 3 = 1 := by
  have table : ∀ a : Fin 3, a.val ≠ 0 → (a.val * a.val) % 3 = 1 := by decide
  rw [Nat.pow_two, Nat.mul_mod]
  exact table ⟨x % 3, Nat.mod_lt _ (by decide)⟩ hx

/-- On the class 4 modulo 6, an even exponent on one side forces the base
on the other side to equal three whenever the first base differs from three. -/
theorem other_base_eq_three {n p q k j : Nat} (hn : n % 6 = 4) (hp : Prime p) (hq : Prime q)
    (hsum : p ^ (2 * k) + q ^ j = n) (hpne : p ≠ 3) : q = 3 := by
  have hn3 : n % 3 = 1 := by
    rw [← Nat.mod_mod_of_dvd n (by decide : 3 ∣ 6), hn]
  have hsq : p ^ (2 * k) % 3 = 1 := by
    rw [Nat.mul_comm 2 k, Nat.pow_mul]
    exact square_mod_three (power_nonzero_mod_three (prime_nonzero_mod_three hp hpne) k)
  have hm : (p ^ (2 * k) % 3 + q ^ j % 3) % 3 = 1 := by
    rw [← Nat.add_mod, hsum, hn3]
  have hzero : q ^ j % 3 = 0 := by omega
  by_cases h : q = 3
  · exact h
  · exact (power_nonzero_mod_three (prime_nonzero_mod_three hq h) j hzero).elim

theorem even_exponent_forces_three {n p q k j : Nat} (hn : n % 6 = 4) (hp : Prime p) (hq : Prime q)
    (hsum : p ^ (2 * k) + q ^ j = n) : p = 3 ∨ q = 3 := by
  by_cases h : p = 3
  · exact Or.inl h
  · exact Or.inr (other_base_eq_three hn hp hq hsum h)

private theorem no_gap {n a b : Nat} (hlo : n ≤ 3 * 3 ^ a) (hhi : 3 * 3 ^ b ≤ 2 * n)
    (hlt : a < b) : False := by
  have hpow := Nat.pow_le_pow_of_le_right (by decide : 0 < 3) (show a + 1 ≤ b by omega)
  rw [Nat.pow_succ] at hpow
  have hpos : 0 < 3 ^ a := Nat.pow_pos (by decide)
  omega

/-- Two powers of three in the closed interval [n/3,2n/3] have the same exponent.
Multiplying the endpoint comparisons by three avoids rounding endpoints. -/
theorem unique_three_power_in_middle_third {n a b : Nat}
    (ha₁ : n ≤ 3 * 3 ^ a) (ha₂ : 3 * 3 ^ a ≤ 2 * n)
    (hb₁ : n ≤ 3 * 3 ^ b) (hb₂ : 3 * 3 ^ b ≤ 2 * n) : a = b := by
  have hab : ¬ a < b := no_gap ha₁ hb₂
  have hba : ¬ b < a := no_gap hb₁ ha₂
  omega

/-- Orient the pair by placing a term with even exponent first. Either term
can be the smaller summand. The sum and the first term's endpoint bounds also
place the second term in the closed middle third. -/
def BalancedEvenExponentSum (n x y : Nat) : Prop :=
  x + y = n ∧ n ≤ 3 * x ∧ 3 * x ≤ 2 * n ∧
  ∃ p q k j : Nat, Prime p ∧ Prime q ∧ x = p ^ (2 * k) ∧ y = q ^ j

private theorem has_three_power_marker {n x y : Nat} (hn : n % 6 = 4)
    (h : BalancedEvenExponentSum n x y) :
    ∃ a : Nat, (x = 3 ^ a ∨ y = 3 ^ a) ∧ n ≤ 3 * 3 ^ a ∧ 3 * 3 ^ a ≤ 2 * n := by
  obtain ⟨hsum, hlo, hhi, p, q, k, j, hp, hq, hx, hy⟩ := h
  have hpow : p ^ (2 * k) + q ^ j = n := by simpa only [← hx, ← hy] using hsum
  rcases even_exponent_forces_three hn hp hq hpow with h | h
  · subst p
    exact ⟨2 * k, Or.inl hx, by omega, by omega⟩
  · subst q
    exact ⟨j, Or.inr hy, by omega, by omega⟩

/-- For n = 4 mod 6 there is at most one balanced unordered pair of prime
powers having an even exponent. Equal summands are included. -/
theorem unique_unordered_even_exponent_pair {n x y u v : Nat} (hn : n % 6 = 4)
    (hxy : BalancedEvenExponentSum n x y) (huv : BalancedEvenExponentSum n u v) :
    (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by
  obtain ⟨a, ha, alo, ahi⟩ := has_three_power_marker hn hxy
  obtain ⟨b, hb, blo, bhi⟩ := has_three_power_marker hn huv
  have heq := unique_three_power_in_middle_third alo ahi blo bhi
  subst b
  have hxysum := hxy.1
  have huvsum := huv.1
  rcases ha with hx | hy <;> rcases hb with hu | hv <;> omega

end Goldbach.ModThree
