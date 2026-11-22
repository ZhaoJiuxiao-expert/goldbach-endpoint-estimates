import Std

/-!
Arithmetic of the modulus-72 filter. The witnesses in `even_local_pair`
represent residue classes. Primality is a separate condition.
-/

namespace GoldbachFilter

/-- The filter used on each individual summand. -/
def Allowed (n : Nat) : Prop :=
  n % 8 ∈ [3, 5, 7] ∧ n % 9 ∈ [2, 4, 5, 7]

instance (n : Nat) : Decidable (Allowed n) := by
  unfold Allowed
  infer_instance

/-- All representatives in the range from 0 through 71. -/
def allowedResidues : List Nat := [5, 7, 11, 13, 23, 29, 31, 43, 47, 59, 61, 67]

theorem allowed_mod72 (n : Nat) : Allowed (n % 72) ↔ Allowed n := by
  simp only [Allowed, Nat.mod_mod_of_dvd n (by decide : 8 ∣ 72),
    Nat.mod_mod_of_dvd n (by decide : 9 ∣ 72)]

theorem allowed_iff_residue (n : Nat) : Allowed n ↔ n % 72 ∈ allowedResidues := by
  have table : ∀ r : Fin 72, Allowed r.val ↔ r.val ∈ allowedResidues := by decide
  exact (allowed_mod72 n).symm.trans (table ⟨n % 72, Nat.mod_lt _ (by decide)⟩)

private def complement (r a : Nat) : Nat := (r + 72 - a) % 72

/-- Ordered local pairs are indexed by the representative of the first summand. -/
def firstSummands (n : Nat) : List Nat :=
  allowedResidues.filter (fun a => decide (Allowed (complement (n % 72) a)))

private def localPair (r : Nat) : Nat × Nat :=
  let a := (firstSummands r).head?.getD 0
  (a, complement r a)

private theorem localTable : ∀ r : Fin 72, r.val % 2 = 0 →
    let pair := localPair r.val
    pair.1 < 72 ∧ pair.2 < 72 ∧ Allowed pair.1 ∧ Allowed pair.2 ∧
      (pair.1 + pair.2) % 72 = r.val := by
  decide

/-- Every even natural number has a local pair modulo 72. -/
theorem even_local_pair (n : Nat) (heven : n % 2 = 0) :
    ∃ a b : Nat, a < 72 ∧ b < 72 ∧ Allowed a ∧ Allowed b ∧
      (a + b) % 72 = n % 72 := by
  let r : Fin 72 := ⟨n % 72, Nat.mod_lt _ (by decide)⟩
  have hr : r.val % 2 = 0 := (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 72)).trans heven
  exact ⟨(localPair r.val).1, (localPair r.val).2, localTable r hr⟩

theorem even_local_count_bounds (n : Nat) (heven : n % 2 = 0) :
    2 ≤ (firstSummands n).length ∧ (firstSummands n).length ≤ 12 := by
  have table : ∀ r : Fin 72, r.val % 2 = 0 →
      2 ≤ (firstSummands r.val).length ∧ (firstSummands r.val).length ≤ 12 := by decide
  have hr := (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 72)).trans heven
  simpa only [firstSummands, Nat.mod_mod_of_dvd n (Nat.dvd_refl 72)] using
    table ⟨n % 72, Nat.mod_lt _ (by decide)⟩ hr

private theorem reducePower (x k d : Nat) : x ^ k % d = (x % d) ^ k % d := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.pow_succ, Nat.pow_succ, Nat.mul_mod (x ^ k) x d,
      Nat.mul_mod ((x % d) ^ k) (x % d) d, ih, Nat.mod_mod]

theorem square_not_allowed (x : Nat) : ¬ Allowed (x ^ 2) := by
  have table : ∀ r : Fin 8, (r.val ^ 2) % 8 ∉ [3, 5, 7] := by decide
  intro h
  apply table ⟨x % 8, Nat.mod_lt _ (by decide)⟩
  change (x % 8) ^ 2 % 8 ∈ [3, 5, 7]
  rw [← reducePower]
  exact h.1

theorem cube_not_allowed (x : Nat) : ¬ Allowed (x ^ 3) := by
  have table : ∀ r : Fin 9, (r.val ^ 3) % 9 ∉ [2, 4, 5, 7] := by decide
  intro h
  apply table ⟨x % 9, Nat.mod_lt _ (by decide)⟩
  change (x % 9) ^ 3 % 9 ∈ [2, 4, 5, 7]
  rw [← reducePower]
  exact h.2

/-- A power that survives has exponent divisible by neither two nor three. -/
theorem exponent_not_divisible {p k : Nat} (h : Allowed (p ^ k)) :
    ¬ 2 ∣ k ∧ ¬ 3 ∣ k := by
  constructor
  · rintro ⟨t, rfl⟩
    rw [Nat.mul_comm 2 t, Nat.pow_mul] at h
    exact square_not_allowed (p ^ t) h
  · rintro ⟨t, rfl⟩
    rw [Nat.mul_comm 3 t, Nat.pow_mul] at h
    exact cube_not_allowed (p ^ t) h

/-- In particular a proper prime power in the filter has exponent at least five.
The conclusion holds even when the base is composite. -/
theorem allowed_power_exponent_ge_five {m p k : Nat} (hm : Allowed m)
    (heq : m = p ^ k) (hk : 2 ≤ k) : 5 ≤ k := by
  subst m
  obtain ⟨h₂, h₃⟩ := exponent_not_divisible hm
  have casesK : k = 2 ∨ k = 3 ∨ k = 4 ∨ 5 ≤ k := by omega
  rcases casesK with rfl | rfl | rfl | h
  · exact (h₂ (by decide)).elim
  · exact (h₃ (by decide)).elim
  · exact (h₂ (by decide)).elim
  · exact h

end GoldbachFilter
