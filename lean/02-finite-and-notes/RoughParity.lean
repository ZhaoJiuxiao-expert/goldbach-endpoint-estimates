import Foundations

namespace Goldbach

/-- Product of the entries of a factor list, with multiplicity. -/
def factorProduct : List Nat → Nat
  | [] => 1
  | a :: rest => a * factorProduct rest

private theorem factorProduct_append (f g : List Nat) :
    factorProduct (f ++ g) = factorProduct f * factorProduct g := by
  induction f with
  | nil => simp [factorProduct]
  | cons a rest ih => simp [factorProduct, ih, Nat.mul_assoc]

private theorem composite_factors {m : Nat} (hm : 2 ≤ m) (hn : ¬ Prime m) :
    ∃ a b, a * b = m ∧ a ≠ 1 ∧ b ≠ 1 := by
  apply Classical.byContradiction
  intro h
  apply hn
  refine ⟨hm, ?_⟩
  intro a b hab
  by_cases ha : a = 1
  · exact Or.inl ha
  · by_cases hb : b = 1
    · exact Or.inr hb
    · exact False.elim (h ⟨a, b, hab, ha, hb⟩)

/-- Existence of a prime factor list for every positive natural number;
    the factor list for 1 is empty. -/
theorem exists_prime_factors (m : Nat) (hm : 0 < m) :
    ∃ f : List Nat, (∀ a ∈ f, Prime a) ∧ factorProduct f = m := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    by_cases hone : m = 1
    · exact ⟨[], by simp, by simp [factorProduct, hone]⟩
    · by_cases hprime : Prime m
      · exact ⟨[m], by simpa using hprime, by simp [factorProduct]⟩
      · obtain ⟨a, b, hab, ha, hb⟩ := composite_factors (by omega) hprime
        have ha0 : a ≠ 0 := by intro h; simp [h] at hab; omega
        have hb0 : b ≠ 0 := by intro h; simp [h] at hab; omega
        have ham : a < m := by
          rw [← hab]
          simpa using (Nat.mul_lt_mul_of_pos_left (show 1 < b by omega) (show 0 < a by omega))
        have hbm : b < m := by
          rw [← hab]
          simpa using (Nat.mul_lt_mul_of_pos_right (show 1 < a by omega) (show 0 < b by omega))
        obtain ⟨f, hf, hfp⟩ := ih a ham (by omega)
        obtain ⟨g, hg, hgp⟩ := ih b hbm (by omega)
        refine ⟨f ++ g, ?_, ?_⟩
        · intro x hx
          rcases List.mem_append.mp hx with h | h
          · exact hf x h
          · exact hg x h
        · rw [factorProduct_append, hfp, hgp, hab]

private theorem member_dvd_factorProduct {a : Nat} {f : List Nat} (ha : a ∈ f) :
    a ∣ factorProduct f := by
  induction f with
  | nil => simp at ha
  | cons b rest ih =>
    rcases List.mem_cons.mp ha with h | h
    · subst b
      exact Nat.dvd_mul_right _ _
    · exact Nat.dvd_trans (ih h) (Nat.dvd_mul_left _ _)

private theorem factorProduct_pos {f : List Nat}
    (h : ∀ a ∈ f, 0 < a) : 0 < factorProduct f := by
  induction f with
  | nil => decide
  | cons a rest ih =>
    exact Nat.mul_pos (h a (by simp))
      (ih (fun x hx => h x (by simp [hx])))

/-- Three factors at least B already contribute B cubed. No primality
    hypothesis is needed for this size bound. -/
theorem rough_length_le_two {f : List Nat} {B : Nat} (hB : 2 ≤ B)
    (hrough : ∀ a ∈ f, B ≤ a) (hsize : factorProduct f < B ^ 3) :
    f.length ≤ 2 := by
  cases f with
  | nil => decide
  | cons a tail =>
    cases tail with
    | nil => simp
    | cons b tail =>
      cases tail with
      | nil => simp
      | cons c rest =>
        have ha : B ≤ a := hrough a (by simp)
        have hb : B ≤ b := hrough b (by simp)
        have hc : B ≤ c := hrough c (by simp)
        have hrest : 1 ≤ factorProduct rest := by
          apply factorProduct_pos
          intro x hx
          have := hrough x (by simp [hx])
          omega
        have hcub : B * (B * (B * 1)) ≤ a * (b * (c * factorProduct rest)) :=
          Nat.mul_le_mul ha (Nat.mul_le_mul hb (Nat.mul_le_mul hc hrest))
        have hlo : B ^ 3 ≤ factorProduct (a :: b :: c :: rest) := by
          simpa [factorProduct, Nat.pow_succ, Nat.mul_assoc] using hcub
        exact False.elim ((Nat.not_lt_of_ge hlo) hsize)

/-- At the cube-root cut, odd multiplicity leaves exactly one prime factor. -/
theorem prime_of_rough_odd_factors {m B : Nat} {f : List Nat}
    (hB : 2 ≤ B) (hprime : ∀ a ∈ f, Prime a)
    (hrough : ∀ a ∈ f, B ≤ a) (hprod : factorProduct f = m)
    (hodd : f.length % 2 = 1) (hsize : m < B ^ 3) : Prime m := by
  have hlen := rough_length_le_two hB hrough (hprod ▸ hsize)
  have hone : f.length = 1 := by omega
  cases f with
  | nil => simp at hone
  | cons a rest =>
    cases rest with
    | nil =>
      have ha : Prime a := hprime a (by simp)
      rw [← hprod]
      simpa [factorProduct] using ha
    | cons b rest => simp at hone

/-- The ordinary sieve condition, expressed using divisors rather than a
    chosen factorization. -/
def IsRough (m B : Nat) : Prop := ∀ a, Prime a → a ∣ m → B ≤ a

/-- For a rough number strictly between 1 and B cubed, the only alternatives
    are a prime or a product of two primes (repeated factors allowed). -/
theorem prime_or_semiprime_of_rough {m B : Nat} (hm : 2 ≤ m) (hB : 2 ≤ B)
    (hr : IsRough m B) (hsize : m < B ^ 3) :
    Prime m ∨ ∃ a b, Prime a ∧ Prime b ∧ B ≤ a ∧ B ≤ b ∧ a * b = m := by
  obtain ⟨f, hf, hprod⟩ := exists_prime_factors m (by omega)
  have hrough : ∀ a ∈ f, B ≤ a := by
    intro a ha
    apply hr a (hf a ha)
    rw [← hprod]
    exact member_dvd_factorProduct ha
  have hlen := rough_length_le_two hB hrough (hprod ▸ hsize)
  cases f with
  | nil => simp [factorProduct] at hprod; omega
  | cons a rest =>
    cases rest with
    | nil =>
      left
      rw [← hprod]
      simpa [factorProduct] using hf a (by simp)
    | cons b rest =>
      cases rest with
      | nil =>
        exact Or.inr ⟨a, b, hf a (by simp), hf b (by simp),
          hrough a (by simp), hrough b (by simp), by simpa [factorProduct] using hprod⟩
      | cons c rest => simp at hlen

/-- A certificate for a prime summand whose reflected value has an odd
    number of prime factors, each at least the sieve cut B. -/
def RoughOddWitness (N B : Nat) : Prop :=
  ∃ (p : Nat) (f : List Nat), Prime p ∧ p ≤ N ∧ 2 ≤ B ∧
    (∀ a ∈ f, Prime a) ∧ (∀ a ∈ f, B ≤ a) ∧
    factorProduct f = N - p ∧ f.length % 2 = 1 ∧ N - p < B ^ 3

theorem hasPair_of_rough_odd {N B : Nat} (h : RoughOddWitness N B) : HasPair N := by
  obtain ⟨p, f, hp, hpN, hB, hprime, hrough, hprod, hodd, hsize⟩ := h
  exact ⟨p, N - p, hp, prime_of_rough_odd_factors hB hprime hrough hprod hodd hsize,
    by omega⟩

/-- For a hypothetical exception, each nontrivial rough reflection of a
    prime in this size range must have exactly two prime factors. -/
theorem semiprime_at_exception {N p B : Nat} (hexc : ¬ HasPair N) (hp : Prime p)
    (hm : 2 ≤ N - p) (hB : 2 ≤ B) (hr : IsRough (N - p) B)
    (hsize : N - p < B ^ 3) :
    ∃ a b, Prime a ∧ Prime b ∧ B ≤ a ∧ B ≤ b ∧ a * b = N - p := by
  rcases prime_or_semiprime_of_rough hm hB hr hsize with h | h
  · exact False.elim (hexc ⟨p, N - p, hp, h, by omega⟩)
  · exact h

/-- The analytic input is a hypothesis for each individual even target
    above T. The finite range below T has its own explicit hypothesis. -/
theorem strongGoldbach_of_rough_odd_above (T : Nat) (cut : Nat → Nat)
    (hsmall : ∀ N, 4 ≤ N → N < T → N % 2 = 0 → HasPair N)
    (hlarge : ∀ N, 4 ≤ N → T ≤ N → N % 2 = 0 → RoughOddWitness N (cut N)) :
    StrongGoldbach := by
  intro N hN heven
  by_cases h : N < T
  · exact hsmall N hN h heven
  · exact hasPair_of_rough_odd (hlarge N hN (by omega) heven)

end Goldbach
