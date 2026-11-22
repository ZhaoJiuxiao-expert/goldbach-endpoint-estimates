import Foundations

namespace Goldbach.SpectralGapEnergy

/-- Sum of squares over sample indices 0 through w, including both endpoints. -/
def windowEnergy (s : Nat → Int) : Nat → Int
  | 0 => s 0 * s 0
  | w + 1 => windowEnergy s w + s (w + 1) * s (w + 1)

/-- The integer to compare against twelve times the measured energy. -/
def cubicFloor (d : Int) (w : Nat) : Int :=
  d * d * (w : Int) * ((w : Int) + 1) * ((w : Int) + 2)

private theorem twice (x : Int) : 2*x = x+x := by omega
private theorem thrice (x : Int) : 3*x = x+x+x := by omega
private theorem twelve (x : Int) : 12*x = 3*(2*(2*x)) := by omega
private theorem twiceRight (x : Int) : x*2 = x+x := by omega

/-- Polynomial identity for adjoining the next endpoint. -/
private theorem adjoin_endpoint (w x d : Int) :
    d*d*w*(w+1)*(w+2) + 3*(w+1)*(2*x-w*d)*(2*x-w*d) +
        12*(x-(w+1)*d)*(x-(w+1)*d)
    = d*d*(w+1)*((w+1)+1)*((w+1)+2) +
        3*((w+1)+1)*(2*x-(w+1)*d)*(2*x-(w+1)*d) := by
  simp only [twelve, twice, thrice, twiceRight, Int.sub_eq_add_neg, Int.add_mul,
    Int.mul_add, Int.neg_add, Int.neg_neg, Int.neg_mul, Int.mul_neg, Int.mul_one, Int.one_mul]
  simp only [Int.mul_assoc, Int.mul_comm, Int.mul_left_comm]
  omega

private theorem endpoint_of_descent {s : Nat → Int} {d : Int} {w : Nat}
    (hs : ∀ i < w, s (i + 1) = s i - d) : s w = s 0 - (w : Int) * d := by
  induction w with
  | zero => simp
  | succ w ih =>
    rw [hs w (by omega), ih (fun i hi => hs i (by omega))]
    simp only [Int.ofNat_succ, Int.add_mul, Int.one_mul]
    omega

/-- Exact sum of squares for a descent of w steps. The last term is the
square measuring displacement of the midpoint of the sequence from zero. -/
theorem descent_energy_identity {s : Nat → Int} {d : Int} {w : Nat}
    (hs : ∀ i < w, s (i + 1) = s i - d) :
    12 * windowEnergy s w = cubicFloor d w +
      3 * ((w : Int) + 1) * (2 * s 0 - (w : Int) * d) * (2 * s 0 - (w : Int) * d) := by
  induction w with
  | zero =>
    simp only [windowEnergy, cubicFloor, Int.ofNat_zero, Int.mul_zero, Int.zero_mul,
      Int.zero_add, Int.sub_zero, Int.mul_one]
    simp only [twelve, thrice, twice, Int.add_mul, Int.mul_add]
  | succ w ih =>
    have hprev := ih (fun i hi => hs i (by omega))
    have hend := endpoint_of_descent hs
    rw [windowEnergy, Int.mul_add, hprev, hend]
    simp only [cubicFloor, Int.ofNat_succ]
    simpa only [Int.mul_assoc] using adjoin_endpoint (w : Int) (s 0) d

private theorem square_nonneg (x : Int) : 0 ≤ x*x := by
  by_cases h : 0 ≤ x
  · exact Int.mul_nonneg h h
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

/-- Cubic obstruction to a witness-free interval, with arbitrary signed starting value. -/
theorem descent_energy_lower_bound {s : Nat → Int} {d : Int} {w : Nat}
    (hs : ∀ i < w, s (i + 1) = s i - d) :
    cubicFloor d w ≤ 12 * windowEnergy s w := by
  rw [descent_energy_identity hs]
  let x := 2 * s 0 - (w : Int) * d
  have h := Int.mul_nonneg (show 0 ≤ 3 * ((w : Int) + 1) by omega) (square_nonneg x)
  change cubicFloor d w ≤ cubicFloor d w + (3 * ((w : Int) + 1) * x) * x
  rw [Int.mul_assoc (3 * ((w : Int) + 1)) x x]
  omega

/-- The threshold is attained for every w by an integral descent with step two. -/
theorem centered_descent_attains_bound (w : Nat) :
    12 * windowEnergy (fun i => (w : Int) - 2 * (i : Int)) w = cubicFloor 2 w := by
  have hs : ∀ i < w, (w : Int) - 2 * ((i + 1 : Nat) : Int) = (w : Int) - 2 * (i : Int) - 2 := by
    intro i _
    omega
  have h := @descent_energy_identity (fun i => (w : Int) - 2 * (i : Int)) 2 w hs
  have hmid : 2 * ((w : Int) - 2 * ((0 : Nat) : Int)) - (w : Int) * 2 = 0 := by omega
  simpa only [hmid, Int.mul_zero, Int.add_zero] using h

/-- For Q > 0 this is Q times the discrepancy from the rational baseline d/Q.
The update at index i records the nonnegative weight c(i). -/
def scaledPrefix (c : Nat → Nat) (Q : Nat) (d : Int) : Nat → Int
  | 0 => 0
  | i + 1 => scaledPrefix c Q d i + (Q : Int) * (c i : Int) - d

theorem positive_weight_of_energy_gap {c : Nat → Nat} {Q a w : Nat} {d : Int}
    (hgap : 12 * windowEnergy (fun i => scaledPrefix c Q d (a + i)) w < cubicFloor d w) :
    ∃ i : Nat, i < w ∧ 0 < c (a + i) := by
  apply Classical.byContradiction
  intro hnone
  have hstep : ∀ i < w, scaledPrefix c Q d (a + (i + 1)) = scaledPrefix c Q d (a + i) - d := by
    intro i hi
    have hz : c (a + i) = 0 := by
      by_cases h : 0 < c (a + i)
      · exact (hnone ⟨i, hi, h⟩).elim
      · omega
    rw [show a + (i + 1) = (a + i) + 1 by omega, scaledPrefix, hz]
    simp
  have hle := @descent_energy_lower_bound (fun i => scaledPrefix c Q d (a + i)) d w hstep
  omega

private def primeTest (p : Nat) : Bool :=
  decide (2 ≤ p) && (List.range p).all (fun a => decide (a < 2 ∨ ¬ a ∣ p))

private theorem primeTest_iff (p : Nat) : primeTest p = true ↔ Prime p := by
  simp only [primeTest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hp, htest⟩
    refine ⟨hp, ?_⟩
    intro a b hab
    by_cases ha : a = 1
    · exact Or.inl ha
    by_cases hb : b = 1
    · exact Or.inr hb
    have ha0 : a ≠ 0 := by intro h; simp [h] at hab; omega
    have hb0 : b ≠ 0 := by intro h; simp [h] at hab; omega
    have hlt : a < p := by
      have := Nat.mul_lt_mul_of_pos_left (by omega : 1 < b) (by omega : 0 < a)
      simpa [hab] using this
    rcases htest a hlt with hl | hnd
    · omega
    · exact (hnd ⟨b, hab.symm⟩).elim
  · intro hp
    refine ⟨hp.1, ?_⟩
    intro a ha
    by_cases h : a < 2
    · exact Or.inl h
    right
    rintro ⟨b, hb⟩
    rcases hp.2 a b hb.symm with hu | hu
    · omega
    · simp [hu] at hb
      omega

/-- Computable indicator of a genuine ordered prime pair for the fixed target n. -/
def pairWeight (n p : Nat) : Nat :=
  if decide (p ≤ n) && primeTest p && primeTest (n - p) then 1 else 0

theorem pairWeight_positive_iff (n p : Nat) :
    0 < pairWeight n p ↔ p ≤ n ∧ Prime p ∧ Prime (n - p) := by
  unfold pairWeight
  split <;> rename_i h
  · have hw : p ≤ n ∧ Prime p ∧ Prime (n - p) := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq, primeTest_iff, and_assoc] using h
    exact ⟨fun _ => hw, fun _ => by decide⟩
  · constructor
    · intro hfalse
      omega
    · intro hw
      exact (h (by simpa only [Bool.and_eq_true, decide_eq_true_eq, primeTest_iff, and_assoc] using hw)).elim

/-- Index the possible smaller summand in the closed interval [ceil(n/3),floor(n/2)]. -/
def centralStart (n : Nat) := (n + 2) / 3
def centralSteps (n : Nat) := n / 2 + 1 - centralStart n

/-- A strict energy gap yields a prime pair for this exact target, with p ≤ q ≤ 2p. -/
theorem balanced_pair_of_central_energy_gap (n Q : Nat) (d : Int)
    (hgap : 12 * windowEnergy
      (fun i => scaledPrefix (pairWeight n) Q d (centralStart n + i)) (centralSteps n) <
        cubicFloor d (centralSteps n)) :
    ∃ p q : Nat, Prime p ∧ Prime q ∧ p + q = n ∧ p ≤ q ∧ q ≤ 2 * p := by
  obtain ⟨i, hi, hw⟩ := positive_weight_of_energy_gap hgap
  let p := centralStart n + i
  have hpq := (pairWeight_positive_iff n p).mp hw
  obtain ⟨hle, hp, hq⟩ := hpq
  refine ⟨p, n - p, hp, hq, by omega, ?_, ?_⟩ <;>
    dsimp [p, centralSteps, centralStart] at hi ⊢ <;> omega

theorem hasPair_of_central_energy_gap (n Q : Nat) (d : Int)
    (hgap : 12 * windowEnergy
      (fun i => scaledPrefix (pairWeight n) Q d (centralStart n + i)) (centralSteps n) <
        cubicFloor d (centralSteps n)) : HasPair n := by
  obtain ⟨p, q, hp, hq, hsum, _⟩ := balanced_pair_of_central_energy_gap n Q d hgap
  exact ⟨p, q, hp, hq, hsum⟩

/-- Centered, integer-valued local discrepancy. Subtracting the prefix at a
cancels all contributions strictly before the window. -/
def localCentered (c : Nat → Nat) (Q : Nat) (d : Int) (a w i : Nat) : Int :=
  d * (w : Int) + 2 * (scaledPrefix c Q d (a + i) - scaledPrefix c Q d a)

private theorem local_zero (c : Nat → Nat) (Q : Nat) (d : Int) (a w : Nat) :
    localCentered c Q d a w 0 = d * (w : Int) := by simp [localCentered]

private theorem local_step (c : Nat → Nat) (Q : Nat) (d : Int) (a w i : Nat) :
    localCentered c Q d a w (i + 1) = localCentered c Q d a w i +
      2 * ((Q : Int) * (c (a + i) : Int) - d) := by
  unfold localCentered
  rw [show a + (i + 1) = (a + i) + 1 by omega, scaledPrefix]
  omega

/-- Identical weights on the w increments give identical samples through w,
even when every weight outside the window is changed. -/
theorem local_samples_depend_only_on_window {c₁ c₂ : Nat → Nat} {Q a w : Nat} {d : Int}
    (hmatch : ∀ j < w, c₁ (a + j) = c₂ (a + j)) :
    ∀ i ≤ w, localCentered c₁ Q d a w i = localCentered c₂ Q d a w i := by
  intro i
  induction i with
  | zero => intro _; rw [local_zero, local_zero]
  | succ i ih =>
    intro hi
    rw [local_step, local_step, ih (by omega), hmatch i (by omega)]

private theorem cubicFloor_double (d : Int) (w : Nat) : cubicFloor (2*d) w = 4 * cubicFloor d w := by
  have four (x : Int) : 4*x = 2*(2*x) := by omega
  simp only [cubicFloor, four, twice, Int.add_mul, Int.mul_add]

/-- In a window without hits, the centered samples trace exactly d(w-2i);
their energy meets the cubic threshold, including the endpoint samples. -/
theorem empty_window_centered_energy {c : Nat → Nat} {Q a w : Nat} {d : Int}
    (hempty : ∀ i < w, c (a + i) = 0) :
    3 * windowEnergy (localCentered c Q d a w) w = cubicFloor d w := by
  have hsteps : ∀ i < w, localCentered c Q d a w (i + 1) = localCentered c Q d a w i - 2*d := by
    intro i hi
    rw [local_step, hempty i hi]
    simp
    omega
  have h := descent_energy_identity hsteps
  have hmid : 2 * localCentered c Q d a w 0 - (w : Int) * (2*d) = 0 := by
    rw [local_zero]
    simp only [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc, Int.sub_self]
  rw [hmid, cubicFloor_double] at h
  simp only [Int.mul_zero, Int.add_zero] at h
  omega

theorem positive_weight_of_local_gap {c : Nat → Nat} {Q a w : Nat} {d : Int}
    (hgap : 3 * windowEnergy (localCentered c Q d a w) w < cubicFloor d w) :
    ∃ i : Nat, i < w ∧ 0 < c (a + i) := by
  apply Classical.byContradiction
  intro hnone
  have hempty : ∀ i < w, c (a + i) = 0 := by
    intro i hi
    by_cases hz : 0 < c (a + i)
    · exact (hnone ⟨i, hi, hz⟩).elim
    · omega
  exact (Int.ne_of_lt hgap) (empty_window_centered_energy hempty)

/-- Central local energy below its no-hit threshold gives a balanced prime
pair for n independently of all prefix values before ceil(n/3). -/
theorem balanced_pair_of_central_local_gap (n Q : Nat) (d : Int)
    (hgap : 3 * windowEnergy (localCentered (pairWeight n) Q d (centralStart n) (centralSteps n))
      (centralSteps n) < cubicFloor d (centralSteps n)) :
    ∃ p q : Nat, Prime p ∧ Prime q ∧ p + q = n ∧ p ≤ q ∧ q ≤ 2 * p := by
  obtain ⟨i, hi, hw⟩ := positive_weight_of_local_gap hgap
  let p := centralStart n + i
  obtain ⟨hle, hp, hq⟩ := (pairWeight_positive_iff n p).mp hw
  refine ⟨p, n - p, hp, hq, by omega, ?_, ?_⟩ <;>
    dsimp [p, centralSteps, centralStart] at hi ⊢ <;> omega

theorem hasPair_of_central_local_gap (n Q : Nat) (d : Int)
    (hgap : 3 * windowEnergy (localCentered (pairWeight n) Q d (centralStart n) (centralSteps n))
      (centralSteps n) < cubicFloor d (centralSteps n)) : HasPair n := by
  obtain ⟨p, q, hp, hq, hsum, _⟩ := balanced_pair_of_central_local_gap n Q d hgap
  exact ⟨p, q, hp, hq, hsum⟩

/-- A verified initial interval can be combined with a separate analytic
strict-gap hypothesis above its endpoint. The latter may choose a different
positive rational baseline d/Q at each n. -/
theorem strongGoldbach_of_checked_range_and_local_tail (B : Nat)
    (hchecked : ∀ n : Nat, 4 ≤ n → n ≤ B → n % 2 = 0 → HasPair n)
    (htail : ∀ n : Nat, 4 ≤ n → B < n → n % 2 = 0 →
      ∃ Q : Nat, ∃ d : Int, 0 < Q ∧ 0 < d ∧
        3 * windowEnergy (localCentered (pairWeight n) Q d (centralStart n) (centralSteps n))
          (centralSteps n) < cubicFloor d (centralSteps n)) : StrongGoldbach := by
  intro n hn heven
  by_cases h : n ≤ B
  · exact hchecked n hn h heven
  · obtain ⟨Q, d, _, _, hgap⟩ := htail n hn (by omega) heven
    exact hasPair_of_central_local_gap n Q d hgap

end Goldbach.SpectralGapEnergy
