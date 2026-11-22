import Certificates

namespace Goldbach.Finite

open GoldbachFilter (Allowed)

private theorem first_class {p q : Nat} (hadd : p + q = 6254)
    (hp : Allowed p) (hq : Allowed q) : p % 36 = 31 := by
  have table : ∀ a : Fin 72, Allowed a.val → ∀ b : Fin 72, Allowed b.val →
      (a.val + b.val) % 72 = 62 → a.val % 36 = 31 := by decide
  have hmod : (p % 72 + q % 72) % 72 = 62 := by
    rw [← Nat.add_mod, hadd]
  have h := table ⟨p % 72, Nat.mod_lt _ (by decide)⟩ ((GoldbachFilter.allowed_mod72 p).mpr hp)
    ⟨q % 72, Nat.mod_lt _ (by decide)⟩ ((GoldbachFilter.allowed_mod72 q).mpr hq) hmod
  exact (Nat.mod_mod_of_dvd p (by decide : 36 ∣ 72)).symm.trans h

private theorem not_prime_of_small_divisor {p d : Nat}
    (hd : 1 < d) (hsmall : d < p) (hdiv : d ∣ p) : ¬ Prime p := by
  intro hp
  obtain ⟨b, hprod⟩ := hdiv
  rcases hp.2 d b hprod.symm with h | h
  · omega
  · simp [h] at hprod
    omega

private def obstructingFactor (p : Nat) : Nat :=
  ((List.range 54).find? (fun d => decide (1 < d ∧ (d ∣ p ∨ d ∣ 6254 - p)))).getD 0

/-- Each of the 29 residue-compatible first summands has an explicit small
factor in either itself or its complement. -/
private theorem obstruction_table : ∀ i : Fin 29,
    let p := 2119 + 36 * i.val
    ∃ d : Fin 54, 1 < d.val ∧ (d.val ∣ p ∨ d.val ∣ 6254 - p) := by
  have checked : ∀ i : Fin 29, let p := 2119 + 36 * i.val
      let d := obstructingFactor p
      1 < d ∧ d < 54 ∧ (d ∣ p ∨ d ∣ 6254 - p) := by decide
  intro i
  obtain ⟨hlo, hhi, hdiv⟩ := checked i
  exact ⟨⟨_, hhi⟩, hlo, hdiv⟩

theorem not_balanced_filtered_6254 : ¬ BalancedFiltered 6254 := by
  rintro ⟨p, q, hp, hq, hadd, horder, hbalance, ha, hb⟩
  have hclass := first_class hadd ha hb
  let i : Fin 29 := ⟨p / 36 - 58, by omega⟩
  have heq : 2119 + 36 * i.val = p := by dsimp [i]; omega
  have h := obstruction_table i
  change ∃ d : Fin 54, 1 < d.val ∧ (d.val ∣ 2119 + 36 * i.val ∨ d.val ∣ 6254 - (2119 + 36 * i.val)) at h
  rw [heq, show 6254 - p = q by omega] at h
  obtain ⟨d, hd, hdiv | hdiv⟩ := h
  · exact not_prime_of_small_divisor hd (by have := d.isLt; omega) hdiv hp
  · exact not_prime_of_small_divisor hd (by have := d.isLt; omega) hdiv hq

/-- An ordinary balanced pair at the same even number. -/
theorem ordinary_pair_6254 : Prime 2143 ∧ Prime 4111 ∧ 2143 + 4111 = 6254 := by
  refine ⟨prime_of_gcd_certificate (k := 46) (by decide) (by decide) (by decide),
    prime_of_gcd_certificate (k := 64) (by decide) (by decide) (by decide), rfl⟩

theorem hasPair_6254 : HasPair 6254 :=
  ⟨2143, 4111, ordinary_pair_6254⟩

end Goldbach.Finite
