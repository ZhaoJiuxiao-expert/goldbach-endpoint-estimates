import RoughParity

namespace Goldbach

/-- Count a divisor on the smaller side of a factorization; equality includes squares. -/
def SmallPrimeIncidence (m r : Nat) : Prop := Prime r ∧ r ∣ m ∧ r * r ≤ m

private theorem primes_equal_of_dvd {r p : Nat} (hr : Prime r) (hp : Prime p)
    (h : r ∣ p) : r = p := by
  obtain ⟨a, ha⟩ := h
  rcases hp.2 r a ha.symm with h | h
  · have := hr.1
    omega
  · simpa [h] using ha.symm

/-- Euclid's lemma in the form needed to count a semiprime once. -/
theorem prime_divisor_of_two_primes {r a b : Nat}
    (hr : Prime r) (ha : Prime a) (hb : Prime b) (h : r ∣ a * b) :
    r = a ∨ r = b := by
  obtain ⟨⟨⟨u, hu⟩, ⟨v, hv⟩⟩, huv⟩ := Nat.prod_dvd_and_dvd_of_dvd_prod h
  rcases hr.2 u v huv.symm with h | h
  · right
    apply primes_equal_of_dvd hr hb
    have heq : r = v := by simpa [h] using huv
    simpa [heq] using hv
  · left
    apply primes_equal_of_dvd hr ha
    have heq : r = u := by simpa [h] using huv
    simpa [heq] using hu

private theorem smallPrimeIncidence_iff_first {a b r : Nat}
    (ha : Prime a) (hb : Prime b) (hab : a ≤ b) :
    SmallPrimeIncidence (a * b) r ↔ r = a := by
  constructor
  · rintro ⟨hr, hd, hs⟩
    rcases prime_divisor_of_two_primes hr ha hb hd with h | h
    · exact h
    · subst r
      by_cases h : b = a
      · exact h
      · have hbpos : 0 < b := Nat.lt_of_lt_of_le (by decide : 0 < 2) hb.1
        have hlt : a * b < b * b := Nat.mul_lt_mul_of_pos_right (by omega) hbpos
        omega
  · intro h
    subst r
    exact ⟨ha, Nat.dvd_mul_right a b, Nat.mul_le_mul_left a hab⟩

/-- In the cube-root range each rough composite has a unique smaller prime
    divisor. The other factor is prime, and an equal pair contributes once. -/
theorem unique_small_prime_of_rough_composite {m B : Nat} (hm : 2 ≤ m) (hB : 2 ≤ B)
    (hr : IsRough m B) (hsize : m < B ^ 3) (hc : ¬ Prime m) :
    ∃ r q, Prime r ∧ Prime q ∧ B ≤ r ∧ r ≤ q ∧ r * q = m ∧
      ∀ s, SmallPrimeIncidence m s ↔ s = r := by
  rcases prime_or_semiprime_of_rough hm hB hr hsize with h | h
  · exact False.elim (hc h)
  · obtain ⟨a, b, ha, hb, haB, hbB, hab⟩ := h
    by_cases hord : a ≤ b
    · refine ⟨a, b, ha, hb, haB, hord, hab, ?_⟩
      intro s
      rw [← hab]
      exact smallPrimeIncidence_iff_first ha hb hord
    · have hba : b * a = m := by simpa [Nat.mul_comm] using hab
      have hle : b ≤ a := by omega
      refine ⟨b, a, hb, ha, hbB, hle, hba, ?_⟩
      intro s
      rw [← hba]
      exact smallPrimeIncidence_iff_first hb ha hle

theorem no_small_prime_incidence_of_prime {m : Nat} (hm : Prime m) (r : Nat) :
    ¬ SmallPrimeIncidence m r := by
  rintro ⟨hr, hd, hsize⟩
  obtain rfl := primes_equal_of_dvd hr hm hd
  have htwo := hr.1
  have hstrict : r * 1 < r * r :=
    Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  simp at hstrict
  omega

private theorem prime_three_inc : Prime 3 :=
  prime_of_gcd_certificate (k := 1) (by decide) (by decide) (by decide)

private theorem prime_seven_inc : Prime 7 :=
  prime_of_gcd_certificate (k := 2) (by decide) (by decide) (by decide)

/-- The two reflected numbers are divisible by the same admissible r = 7,
    but 63 also has the smaller prime 3 and must fail the initial rough sieve.
    The square 49 passes and contributes its prime 7 exactly once. -/
theorem incidence_example_110 :
    Prime 47 ∧ Prime 61 ∧ Prime 7 ∧
    110 - 47 = 63 ∧ 110 - 61 = 49 ∧
    SmallPrimeIncidence (110 - 47) 7 ∧ SmallPrimeIncidence (110 - 61) 7 ∧
    ¬ IsRough (110 - 47) 5 ∧ IsRough (110 - 61) 5 ∧
    (∀ s, SmallPrimeIncidence (110 - 61) s ↔ s = 7) := by
  refine ⟨prime_of_gcd_certificate (k := 6) (by decide) (by decide) (by decide),
    prime_of_gcd_certificate (k := 7) (by decide) (by decide) (by decide),
    prime_seven_inc, rfl, rfl, ⟨prime_seven_inc, by decide, by decide⟩,
    ⟨prime_seven_inc, by decide, by decide⟩, ?_, ?_, ?_⟩
  · intro h
    have := h 3 prime_three_inc (by decide)
    omega
  · intro s hs hd
    have hor := prime_divisor_of_two_primes hs prime_seven_inc prime_seven_inc
      (show s ∣ 7 * 7 from hd)
    rcases hor with h | h <;> omega
  · intro s
    exact smallPrimeIncidence_iff_first prime_seven_inc prime_seven_inc (by decide)

end Goldbach
