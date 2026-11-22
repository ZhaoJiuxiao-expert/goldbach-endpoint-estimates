import Foundations

namespace Goldbach.MobiusCutoff

/-- Reflecting a factorization across N turns the strict divisor cut into
    a strict endpoint depending on the complementary divisor k. -/
theorem large_divisor_iff_moving_cut {N n m A k d : Nat}
    (hm : m = N - n) (hmpos : 0 < m) (hfactor : m = k * d) (hk : 0 < k) :
    A < d ↔ n + A * k < N := by
  have hsum : n + m = N := by omega
  rw [← hsum, hfactor, Nat.add_lt_add_iff_left, Nat.mul_comm A k]
  exact (Nat.mul_lt_mul_left hk).symm

/-- For positive m the map d ↦ m/d stays among its divisors and is an
    involution there. This gives the inverse for complementary reindexing. -/
theorem complementary_divisor {m d : Nat} (hm : 0 < m) (hd : d ∣ m) :
    0 < m / d ∧ m / d ∣ m ∧ m / (m / d) = d := by
  have hmul := Nat.div_mul_cancel hd
  have hpos : 0 < m / d := by
    apply Nat.pos_of_ne_zero
    intro hz
    simp [hz] at hmul
    omega
  exact ⟨hpos, ⟨d, hmul.symm⟩,
    Nat.div_eq_of_eq_mul_left hpos (Nat.mul_div_cancel' hd).symm⟩

/-- A finite integer sum, retaining list multiplicities. -/
def sumOver {α : Type} : List α → (α → Int) → Int
  | [], _ => 0
  | a :: rest, w => w a + sumOver rest w

private theorem sum_zero {α : Type} (xs : List α) :
    sumOver xs (fun _ => 0) = 0 := by
  induction xs with
  | nil => rfl
  | cons _ xs ih => simp [sumOver, ih]

private theorem sum_add {α : Type} (xs : List α) (f g : α → Int) :
    sumOver xs (fun x => f x + g x) = sumOver xs f + sumOver xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [sumOver, ih]; omega

private theorem sum_congr {α : Type} (xs : List α) (f g : α → Int)
    (h : ∀ x ∈ xs, f x = g x) : sumOver xs f = sumOver xs g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [sumOver, sumOver, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

private theorem sum_swap {α β : Type} (xs : List α) (ys : List β)
    (w : α → β → Int) :
    sumOver xs (fun x => sumOver ys (w x)) =
      sumOver ys (fun y => sumOver xs (fun x => w x y)) := by
  induction xs with
  | nil => exact (sum_zero ys).symm
  | cons x xs ih => simp only [sumOver, sum_add, ih]

private theorem sum_append {α : Type} (xs ys : List α) (w : α → Int) :
    sumOver (xs ++ ys) w = sumOver xs w + sumOver ys w := by
  induction xs with
  | nil => simp [sumOver]
  | cons x xs ih => simp [sumOver, ih, Int.add_assoc]

private theorem sum_range_pick (B t : Nat) (weight : Int) :
    sumOver (List.range B) (fun j => if j = t then weight else 0) =
      (if t < B then weight else 0) := by
  induction B with
  | zero => simp [sumOver]
  | succ B ih =>
    rw [List.range_succ, sum_append, ih]
    by_cases ht : t < B
    · simp [sumOver, ht, show t < B + 1 by omega, show B ≠ t by omega]
    · by_cases he : B = t
      · subst t; simp [sumOver]
      · simp [sumOver, ht, he, show ¬ t < B + 1 by omega]

private theorem expand_divisor (m B i : Nat) (hm : 0 < m) (hmB : m < B)
    (w : Nat → Int) :
    (if i ∣ m then w (m / i) else 0) =
      sumOver (List.range B) (fun j => if j * i = m then w j else 0) := by
  by_cases h : i ∣ m
  · have hi := Nat.pos_of_dvd_of_pos h hm
    have hq := Nat.lt_of_le_of_lt (Nat.div_le_self m i) hmB
    simp only [h, if_true]
    have hpick := sum_range_pick B (m / i) (w (m / i))
    rw [if_pos hq] at hpick
    apply Eq.trans hpick.symm
    apply sum_congr
    intro j _
    by_cases he : j = m / i
    · subst j; simp [Nat.div_mul_cancel h]
    · have hprod : j * i ≠ m := fun e =>
        he (Nat.div_eq_of_eq_mul_left hi e.symm).symm
      simp [he, hprod]
  · simp only [h, if_false]
    apply Eq.trans (sum_zero (List.range B)).symm
    apply sum_congr
    intro j _
    have he : j * i ≠ m := fun e => h ⟨j, e ▸ Nat.mul_comm j i⟩
    simp [he]

/-- Replacing each divisor d by k = m/d preserves any integer sum, with
    the arguments of w kept in their original order. -/
theorem divisor_sum_complement (m B : Nat) (hm : 0 < m) (hmB : m < B)
    (w : Nat → Nat → Int) :
    sumOver (List.range B) (fun d => if d ∣ m then w (m / d) d else 0) =
    sumOver (List.range B) (fun k => if k ∣ m then w k (m / k) else 0) := by
  calc
    _ = sumOver (List.range B) (fun d => sumOver (List.range B)
          (fun k => if k * d = m then w k d else 0)) := by
            apply sum_congr
            intro d _
            exact expand_divisor m B d hm hmB (fun k => w k d)
    _ = sumOver (List.range B) (fun k => sumOver (List.range B)
          (fun d => if k * d = m then w k d else 0)) := by apply sum_swap
    _ = _ := by
      apply sum_congr
      intro k _
      simpa only [Nat.mul_comm k] using (expand_divisor m B k hm hmB (w k)).symm

/-- Exact interchange of the two finite sums over n and k. The weight may
    depend arbitrarily on both entries, and can contain the complementary
    divisor (N-n)/k as well. Taking ns = List.range N enumerates n < N. -/
theorem switched_sum (N A : Nat) (ns ks : List Nat) (w : Nat → Nat → Int)
    (hn : ∀ n ∈ ns, n < N) :
    sumOver ns (fun n => sumOver ks (fun k =>
      if 0 < k ∧ k ∣ N - n ∧ A < (N - n) / k then w n k else 0)) =
    sumOver ks (fun k => sumOver ns (fun n =>
      if 0 < k ∧ k ∣ N - n ∧ n + A * k < N then w n k else 0)) := by
  rw [sum_swap]
  apply sum_congr
  intro k _
  apply sum_congr
  intro n hmem
  by_cases h : 0 < k ∧ k ∣ N - n
  · have he := large_divisor_iff_moving_cut (N := N) (n := n) (A := A)
      rfl (Nat.sub_pos_of_lt (hn n hmem)) (Nat.mul_div_cancel' h.2).symm h.1
    simp only [h.1, h.2, true_and, he]
  · by_cases hk : 0 < k
    · have hd : ¬ k ∣ N - n := fun hd => h ⟨hk, hd⟩
      simp [hd]
    · simp [hk]

/-- Full finite identity: the left side sums over the original divisor d
    above A and the right side over its complement k with the moving cut.
    Every positive divisor is covered because N-n ≤ N. -/
theorem full_divisor_switch (N A : Nat) (w : Nat → Nat → Nat → Int) :
    sumOver (List.range N) (fun n => sumOver (List.range (N + 1)) (fun d =>
      if d ∣ N - n ∧ A < d then w n ((N - n) / d) d else 0)) =
    sumOver (List.range (N + 1)) (fun k => sumOver (List.range N) (fun n =>
      if 0 < k ∧ k ∣ N - n ∧ n + A * k < N then w n k ((N - n) / k) else 0)) := by
  apply Eq.trans _ (switched_sum N A (List.range N) (List.range (N + 1))
    (fun n k => w n k ((N - n) / k)) (fun _ h => List.mem_range.mp h))
  apply sum_congr
  intro n hn
  have hm : 0 < N - n := Nat.sub_pos_of_lt (List.mem_range.mp hn)
  have hs := divisor_sum_complement (N - n) (N + 1) hm (by omega)
    (fun k d => if A < d then w n k d else 0)
  apply Eq.trans _ (Eq.trans hs _)
  · apply sum_congr
    intro d _
    by_cases h : d ∣ N - n <;> simp [h]
  · apply sum_congr
    intro k _
    by_cases h : k ∣ N - n
    · simp [h, Nat.pos_of_dvd_of_pos h hm]
    · simp [h]

/-- At N = 64, A = sqrt N = 8, the outer cut k < N/A and the fixed
    endpoint accept k = 3, n = 43. The exact moving endpoint excludes it.
    The reflected number is 3*7, with distinct primes coprime to N. -/
theorem wide_endpoint_example :
    64 = 8 * 8 ∧ 3 < 64 / 8 ∧ 43 < 64 ∧ 64 - 43 = 3 * 7 ∧
    7 < 8 ∧ ¬ (43 + 8 * 3 < 64) ∧
    Nat.gcd 3 64 = 1 ∧ Nat.gcd 3 7 = 1 ∧ 3 ≠ 7 ∧
    Prime 3 ∧ Prime 7 ∧ Prime 43 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_, ?_, ?_⟩
  · exact prime_of_gcd_certificate (k := 1) (by decide) (by decide) (by decide)
  · exact prime_of_gcd_certificate (k := 2) (by decide) (by decide) (by decide)
  · exact prime_of_gcd_certificate (k := 6) (by decide) (by decide) (by decide)

/-- The usual two elementary Möbius identities force the reflected
    coefficient in the example to be +1. -/
theorem example_mobius_value (mu : Nat → Int)
    (mu_prime : ∀ p, Prime p → mu p = -1)
    (mu_coprime : ∀ a b, Nat.gcd a b = 1 → mu (a * b) = mu a * mu b) :
    mu (64 - 43) = 1 := by
  obtain ⟨_, _, _, hfactor, _, _, _, hcop, _, h3, h7, _⟩ := wide_endpoint_example
  rw [hfactor, mu_coprime 3 7 hcop, mu_prime 3 h3, mu_prime 7 h7]
  decide

/-- The arithmetic Möbius function, defined by divisor inversion. -/
def arithmeticMobius (n : Nat) : Int :=
  if 1 < n then
    -sumOver (List.range n) (fun d =>
      if _hd : d < n then (if d ∣ n then arithmeticMobius d else 0) else 0)
  else if n = 1 then 1 else 0
termination_by n

/-- The complete divisor sum vanishes at every integer greater than one. -/
theorem arithmeticMobius_divisor_sum {n : Nat} (hn : 1 < n) :
    sumOver (List.range (n + 1)) (fun d =>
      if d ∣ n then arithmeticMobius d else 0) = 0 := by
  rw [List.range_succ, sum_append]
  simp only [sumOver, Nat.dvd_refl, if_true, Int.add_zero]
  conv => lhs; rhs; rw [arithmeticMobius]
  simp only [if_pos hn]
  have he := sum_congr (List.range n) (fun d =>
    if _h : d < n then (if d ∣ n then arithmeticMobius d else 0) else 0)
    (fun d => if d ∣ n then arithmeticMobius d else 0)
    (fun d hd => by simp [List.mem_range.mp hd])
  rw [he]
  omega

private theorem sum_range_stable (w : Nat → Int) {a b : Nat} (hab : a ≤ b)
    (hz : ∀ d, a ≤ d → w d = 0) :
    sumOver (List.range b) w = sumOver (List.range a) w := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    rw [ha]
  | succ b ih =>
    by_cases he : a = b + 1
    · rw [he]
    · have ha : a ≤ b := by omega
      rw [List.range_succ, sum_append, ih ha]
      simp [sumOver, hz b ha]

/-- A divisor of q*r either divides r or is a multiple of the prime q. -/
private theorem prime_factor_split {q r d : Nat} (hq : Prime q) (hd : d ∣ q * r) :
    d ∣ r ∨ q ∣ d := by
  obtain ⟨⟨⟨u, hu⟩, ⟨v, hv⟩⟩, he⟩ := Nat.prod_dvd_and_dvd_of_dvd_prod hd
  obtain ⟨k, hk⟩ := hu
  rcases hq.2 u k hk.symm with hu | hk1
  · left
    simpa [he, hu] using hv
  · have hu : q = u := by simpa [hk1] using hk
    right
    exact ⟨v, by simpa only [hu] using he⟩

/-- With a dominant prime q, the divisors up to any cutoff in [r,q)
    are exactly the divisors of r. -/
theorem dominant_prime_divisor_cut {q r t d : Nat} (hq : Prime q)
    (hr : 0 < r) (hrt : r ≤ t) (htq : t < q) :
    (d ∣ q * r ∧ d ≤ t) ↔ d ∣ r := by
  constructor
  · intro ⟨hd, hdt⟩
    rcases prime_factor_split hq hd with h | h
    · exact h
    · have hpos := Nat.pos_of_dvd_of_pos hd (Nat.mul_pos (by have := hq.1; omega) hr)
      have := Nat.le_of_dvd hpos h
      omega
  · intro hd
    exact ⟨Nat.dvd_trans hd (Nat.dvd_mul_left r q), Nat.le_trans (Nat.le_of_dvd hr hd) hrt⟩

private theorem mobius_sum_to_larger_bound {r b : Nat} (hr : 1 < r) (hb : r < b) :
    sumOver (List.range b) (fun d => if d ∣ r then arithmeticMobius d else 0) = 0 := by
  rw [sum_range_stable _ (show r + 1 ≤ b by omega) (by
    intro d hd
    have hnd : ¬ d ∣ r := fun h => by have := Nat.le_of_dvd (by omega : 0 < r) h; omega
    simp [hnd])]
  exact arithmeticMobius_divisor_sum hr

/-- The actual Möbius sum vanishes separately for every q*r with q prime,
    1 < r ≤ t < q. No squarefreeness assumption on r is needed. -/
theorem dominant_prime_mobius_cut_zero {q r t : Nat} (hq : Prime q)
    (hr : 1 < r) (hrt : r ≤ t) (htq : t < q) :
    sumOver (List.range (q * r + 1)) (fun d =>
      if d ∣ q * r ∧ d ≤ t then arithmeticMobius d else 0) = 0 := by
  have hbound : r ≤ q * r := by
    have h := Nat.mul_le_mul_right r (show 1 ≤ q by have := hq.1; omega)
    simpa using h
  apply Eq.trans _ (mobius_sum_to_larger_bound hr (show r < q * r + 1 by omega))
  apply sum_congr
  intro d _
  simp only [dominant_prime_divisor_cut (d := d) hq (show 0 < r by omega) hrt htq]

/-- The strict upper tail used in the cutoff C(t) vanishes on the same
    interval, including its lower endpoint t = r. -/
theorem dominant_prime_mobius_tail_zero {q r t : Nat} (hq : Prime q)
    (hr : 1 < r) (hrt : r ≤ t) (htq : t < q) :
    sumOver (List.range (q * r + 1)) (fun d =>
      if d ∣ q * r ∧ t < d then arithmeticMobius d else 0) = 0 := by
  have hbound : 1 < q * r := by
    have h := Nat.mul_le_mul_right r (show 1 ≤ q by have := hq.1; omega)
    simp only [Nat.one_mul] at h
    omega
  have hfull := arithmeticMobius_divisor_sum hbound
  have hparts := sum_add (List.range (q * r + 1))
    (fun d => if d ∣ q * r ∧ d ≤ t then arithmeticMobius d else 0)
    (fun d => if d ∣ q * r ∧ t < d then arithmeticMobius d else 0)
  rw [dominant_prime_mobius_cut_zero hq hr hrt htq, Int.zero_add] at hparts
  exact hparts.symm.trans (Eq.trans (by
    apply sum_congr
    intro d _
    by_cases hd : d ∣ q * r
    · by_cases ht : d ≤ t
      · simp [hd, ht, show ¬ t < d by omega]
      · simp [hd, ht, show t < d by omega]
    · simp [hd]) hfull)

/-- When q > r, comparing a divisor with the exact square root of q*r
    detects precisely the divisors of r. Equality cannot occur. -/
theorem dominant_prime_square_cut {q r d : Nat} (hq : Prime q)
    (hr : 0 < r) (hrq : r < q) (hd : d ∣ q * r) :
    (d * d < q * r ↔ d ∣ r) ∧ (d * d ≤ q * r ↔ d ∣ r) := by
  have hqpos : 0 < q := by omega
  have hsmall : d ∣ r → d * d < q * r := by
    intro h
    have hdr := Nat.le_of_dvd hr h
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul hdr hdr) ((Nat.mul_lt_mul_right hr).2 hrq)
  have hlarge : d * d ≤ q * r → d ∣ r := by
    intro h
    rcases prime_factor_split hq hd with hdiv | hdiv
    · exact hdiv
    · have hqd := Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hd (Nat.mul_pos hqpos hr)) hdiv
      have h1 := (Nat.mul_lt_mul_left hqpos).2 hrq
      have h2 := Nat.mul_le_mul hqd hqd
      omega
  exact ⟨⟨fun h => hlarge (Nat.le_of_lt h), hsmall⟩, ⟨hlarge, fun h => Nat.le_of_lt (hsmall h)⟩⟩

/-- For each q*r with 1 < r < q prime, the strict square-root Möbius
    cutoff is zero, and using a closed square-root cutoff gives the same sum. -/
theorem dominant_prime_mobius_square_zero {q r : Nat} (hq : Prime q)
    (hr : 1 < r) (hrq : r < q) :
    (sumOver (List.range (q * r + 1)) (fun d =>
      if d ∣ q * r ∧ d * d < q * r then arithmeticMobius d else 0) = 0) ∧
    (sumOver (List.range (q * r + 1)) (fun d =>
      if d ∣ q * r ∧ d * d ≤ q * r then arithmeticMobius d else 0) = 0) := by
  have hu := dominant_prime_mobius_cut_zero hq hr (Nat.le_refl r) hrq
  constructor <;> apply Eq.trans _ hu <;> apply sum_congr <;> intro d _
  all_goals
    by_cases hd : d ∣ q * r
    · have hh := dominant_prime_square_cut hq (show 0 < r by omega) hrq hd
      have hshort := dominant_prime_divisor_cut (d := d) hq (show 0 < r by omega) (Nat.le_refl r) hrq
      simp only [hd, true_and] at hshort
      simp [hd, hh.1, hh.2, hshort]
    · simp [hd]

end Goldbach.MobiusCutoff

#print axioms Goldbach.MobiusCutoff.large_divisor_iff_moving_cut
#print axioms Goldbach.MobiusCutoff.complementary_divisor
#print axioms Goldbach.MobiusCutoff.divisor_sum_complement
#print axioms Goldbach.MobiusCutoff.switched_sum
#print axioms Goldbach.MobiusCutoff.full_divisor_switch
#print axioms Goldbach.MobiusCutoff.wide_endpoint_example
#print axioms Goldbach.MobiusCutoff.example_mobius_value
#print axioms Goldbach.MobiusCutoff.arithmeticMobius_divisor_sum
#print axioms Goldbach.MobiusCutoff.dominant_prime_divisor_cut
#print axioms Goldbach.MobiusCutoff.dominant_prime_mobius_cut_zero
#print axioms Goldbach.MobiusCutoff.dominant_prime_mobius_tail_zero
#print axioms Goldbach.MobiusCutoff.dominant_prime_square_cut
#print axioms Goldbach.MobiusCutoff.dominant_prime_mobius_square_zero
