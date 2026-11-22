import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Tactic
import PrimeEndpoint

open scoped BigOperators
open Finset
namespace Goldbach.SieveWeight

/-- The strict Möbius tail used in Section 5, before applying its outer support mask. -/
def tail (m t : ℕ) : ℤ :=
  ∑ d ∈ m.divisors, if t < d then ArithmeticFunction.moebius d else 0

private def value (s : Finset ℕ) := ∏ p ∈ s, p
private def parity (s : Finset ℕ) := (-1 : ℤ) ^ s.card

private theorem tail_as_subsets {m : ℕ} (hm : m ≠ 0) (t : ℕ) :
    tail m t = ∑ s ∈ m.primeFactors.powerset, if t < value s then parity s else 0 := by
  classical
  let f : ℕ → ℤ := fun d => if t < d then ArithmeticFunction.moebius d else 0
  have hremove : ∑ d ∈ m.divisors.filter Squarefree, f d = tail m t := by
    apply Finset.sum_subset (Finset.filter_subset ..)
    intro d hd hnot
    have hn : ¬ Squarefree d := fun h => hnot (Finset.mem_filter.mpr ⟨hd,h⟩)
    simp [f, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
  rw [← hremove, Nat.sum_divisors_filter_squarefree hm, Nat.factors_eq]
  change (∑ s ∈ m.primeFactors.powerset, f s.val.prod) = _
  apply Finset.sum_congr rfl
  intro s hs
  have hprod : ArithmeticFunction.moebius (value s) = parity s := by
    rw [value, ArithmeticFunction.isMultiplicative_moebius.map_prod_of_subset_primeFactors m s (mem_powerset.mp hs)]
    calc
      _ = ∏ _p ∈ s, (-1 : ℤ) := Finset.prod_congr rfl (fun p hp =>
        ArithmeticFunction.moebius_apply_prime (Nat.prime_of_mem_primeFactors (mem_powerset.mp hs hp)))
      _ = _ := by simp [parity]
  have hv : s.val.prod = value s := s.prod_val
  simp only [f,hv,hprod]

private def fringe (R : Finset ℕ) (p t : ℕ) :=
  R.powerset.filter (fun s => value s ≤ t ∧ t < p * value s)

/-- Pair each squarefree divisor not containing p with its partner obtained
    by adjoining p. Only subsets whose product crosses the cut survive. -/
private theorem tail_fringe {m p : ℕ} (hm : m ≠ 0) (hp : p ∈ m.primeFactors) (t : ℕ) :
    tail m t = -∑ s ∈ fringe (m.primeFactors.erase p) p t, parity s := by
  classical
  let R := m.primeFactors.erase p
  have hnot : p ∉ R := Finset.not_mem_erase _ _
  have hpos : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
  rw [tail_as_subsets hm, ← Finset.insert_erase hp, Finset.sum_powerset_insert hnot,
    ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
  unfold fringe
  rw [Finset.sum_filter, Finset.erase_insert (Finset.not_mem_erase _ _)]
  apply Finset.sum_congr rfl
  intro s hs
  have hps : p ∉ s := fun h => hnot (mem_powerset.mp hs h)
  have hmul : value (insert p s) = p * value s := by simp [value,hps]
  have hpar : parity (insert p s) = -parity s := by simp [parity,hps,pow_succ]
  rw [hmul,hpar]
  have hle : value s ≤ p * value s := by simpa using Nat.mul_le_mul_right (value s) hpos
  split_ifs <;> omega

private theorem fringe_antichain {R : Finset ℕ} {p t : ℕ} (hp : 1 ≤ p)
    (hsmall : ∀ a ∈ R, p ≤ a) :
    IsAntichain (· ⊆ ·) (fringe R p t : Set (Finset ℕ)) := by
  classical
  intro A hA B hB hne hAB
  obtain ⟨_, _, ha'⟩ := mem_filter.mp hA
  obtain ⟨hBR, hb, _⟩ := mem_filter.mp hB
  have hnd : ¬ B ⊆ A := fun h => hne (Finset.Subset.antisymm hAB h)
  obtain ⟨r,hrB,hrA⟩ := Finset.not_subset.mp hnd
  have hr : r ∈ B \ A := mem_sdiff.mpr ⟨hrB,hrA⟩
  have hpr := hsmall r (mem_powerset.mp hBR hrB)
  have hpos : 0 < value (B \ A) := Finset.prod_pos (fun i hi =>
    by have := hsmall i (mem_powerset.mp hBR (mem_sdiff.mp hi).1); omega)
  have hdvd : r ∣ value (B \ A) := Finset.dvd_prod_of_mem (fun n : ℕ => n) hr
  have hle : p ≤ value (B \ A) := hpr.trans (Nat.le_of_dvd hpos hdvd)
  have hproduct : value (B \ A) * value A = value B := Finset.prod_sdiff hAB
  exact (not_lt_of_ge (Nat.mul_le_mul_right (value A) hle)) (by rw [hproduct]; exact hb.trans_lt ha')

private theorem relative_sperner {R : Finset ℕ} {F : Finset (Finset ℕ)}
    (hR : ∀ s ∈ F, s ⊆ R) (hF : IsAntichain (· ⊆ ·) (F : Set (Finset ℕ))) :
    F.card ≤ R.card.choose (R.card / 2) := by
  classical
  let lift := fun s : Finset ℕ => s.subtype (· ∈ R)
  have hinv (s : Finset ℕ) (hs : s ∈ F) :
      (lift s).map (Function.Embedding.subtype _) = s :=
    Finset.subtype_map_of_mem (hR s hs)
  have hinj : Set.InjOn lift (F : Set (Finset ℕ)) := by
    intro s hs u hu e
    rw [← hinv s hs, ← hinv u hu, e]
  have ha : IsAntichain (· ⊆ ·) ((F.image lift : Finset (Finset R)) : Set (Finset R)) := by
    intro A hA B hB hne hsub
    obtain ⟨s,hs,rfl⟩ := mem_image.mp hA
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hB
    apply hF hs hu (fun h => hne (congrArg lift h))
    simpa only [hinv s hs, hinv u hu] using (Finset.map_subset_map.mpr hsub :
      (lift s).map (Function.Embedding.subtype _) ⊆ (lift u).map (Function.Embedding.subtype _))
  simpa [Finset.card_image_of_injOn hinj] using (Finset.IsAntichain.sperner ha)

/-- Uniform on every positive integer m ≥ 2 and every integer cut. The factors
    are counted without multiplicity, including for non-squarefree m. -/
theorem abs_tail_le_central_choose {m : ℕ} (hm : 2 ≤ m) (t : ℕ) :
    |tail m t| ≤ ((m.primeFactors.card - 1).choose ((m.primeFactors.card - 1) / 2) : ℤ) := by
  classical
  let p := m.minFac
  let R := m.primeFactors.erase p
  let F := fringe R p t
  have hpPrime : p.Prime := Nat.minFac_prime (by omega)
  have hp : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hpPrime, Nat.minFac_dvd m, by omega⟩
  have ha := fringe_antichain (p := p) (t := t) (R := R) hpPrime.one_lt.le (by
    intro a ha
    have hd := Nat.dvd_of_mem_primeFactors (Finset.mem_erase.mp ha).2
    have hprim := Nat.prime_of_mem_primeFactors (Finset.mem_erase.mp ha).2
    exact Nat.minFac_le_of_dvd hprim.two_le hd)
  have hcard : F.card ≤ R.card.choose (R.card / 2) :=
    relative_sperner (fun s hs => mem_powerset.mp (mem_filter.mp hs).1) ha
  have hRcard : R.card = m.primeFactors.card - 1 := Finset.card_erase_of_mem hp
  rw [tail_fringe (by omega) hp, abs_neg]
  change |∑ s ∈ F, parity s| ≤ _
  calc
    _ ≤ ∑ s ∈ F, |parity s| := Finset.abs_sum_le_sum_abs _ _
    _ = (F.card : ℤ) := by simp [parity, abs_pow]
    _ ≤ _ := by rw [← hRcard]; exact_mod_cast hcard


/-- Only primes at most the cutoff can enter the complementary low-divisor sum. -/
def smallPrimes (m t : ℕ) := m.primeFactors.filter (· ≤ t)

/-- Product of the distinct primes dividing m which do not exceed the cutoff. -/
def smallRadical (m t : ℕ) := value (smallPrimes m t)

private theorem tail_as_low {m : ℕ} (hm : 2 ≤ m) (t : ℕ) :
    tail m t = -(∑ s ∈ (smallPrimes m t).powerset, if value s ≤ t then parity s else 0) := by
  classical
  have hp : m.minFac ∈ m.primeFactors := Nat.mem_primeFactors.mpr
    ⟨Nat.minFac_prime (by omega), Nat.minFac_dvd m, by omega⟩
  have hz : (∑ s ∈ m.primeFactors.powerset, parity s) = 0 :=
    Finset.sum_powerset_neg_one_pow_card_of_nonempty ⟨_,hp⟩
  have hdecomp :
      (∑ s ∈ m.primeFactors.powerset, if t < value s then parity s else 0) +
      (∑ s ∈ m.primeFactors.powerset, if value s ≤ t then parity s else 0) = 0 := by
    rw [← Finset.sum_add_distrib, ← hz]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> omega
  have heq :
      (∑ s ∈ (smallPrimes m t).powerset, if value s ≤ t then parity s else 0) =
      ∑ s ∈ m.primeFactors.powerset, if value s ≤ t then parity s else 0 := by
    apply Finset.sum_subset (Finset.powerset_mono.mpr (Finset.filter_subset ..))
    intro s hs hnot
    have hbig : ¬ value s ≤ t := by
      intro hle
      apply hnot
      apply mem_powerset.mpr
      intro a ha
      have hpos : 0 < value s :=
        Finset.prod_pos (fun b hb => (Nat.prime_of_mem_primeFactors (mem_powerset.mp hs hb)).pos)
      exact mem_filter.mpr ⟨mem_powerset.mp hs ha, (Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem (fun n : ℕ => n) ha)).trans hle⟩
    simp [hbig]
  rw [tail_as_subsets (by omega), heq]
  omega

private theorem factors_smallRadical (m t : ℕ) :
    (smallRadical m t).primeFactors = smallPrimes m t :=
  Nat.primeFactors_prod (fun _ h => Nat.prime_of_mem_primeFactors (mem_filter.mp h).1)

private theorem smallRadical_two_le {m t : ℕ} (hn : (smallPrimes m t).Nonempty) :
    2 ≤ smallRadical m t := by
  obtain ⟨p,hp⟩ := hn
  rw [← factors_smallRadical] at hp
  exact (Nat.prime_of_mem_primeFactors hp).two_le.trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (Nat.mem_primeFactors.mp hp).2.2)
      (Nat.dvd_of_mem_primeFactors hp))

/-- Exact reduction of the paper's tail to the radical below its own cutoff.
    No assumption of squarefreeness of the original complementary integer. -/
theorem tail_smallRadical {m t : ℕ} (hm : 2 ≤ m) (hn : (smallPrimes m t).Nonempty) :
    tail m t = tail (smallRadical m t) t := by
  rw [tail_as_low hm, tail_as_low (smallRadical_two_le hn)]
  have heq : smallPrimes (smallRadical m t) t = smallPrimes m t := by
    unfold smallPrimes
    rw [factors_smallRadical]
    ext p
    simp [smallPrimes, and_assoc]
  rw [heq]

theorem tail_minus_one_when_rough {m t : ℕ} (hm : 2 ≤ m) (ht : 1 ≤ t)
    (he : smallPrimes m t = ∅) : tail m t = -1 := by
  rw [tail_as_low hm, he]
  simp [value, parity, ht]

theorem tail_zero_when_smallRadical_le {m t : ℕ} (hm : 2 ≤ m)
    (hn : (smallPrimes m t).Nonempty) (hle : smallRadical m t ≤ t) : tail m t = 0 := by
  rw [tail_smallRadical hm hn]
  apply Finset.sum_eq_zero
  intro d hd
  have had := (Nat.le_of_dvd (by have := smallRadical_two_le hn; omega) (Nat.dvd_of_mem_divisors hd)).trans hle
  simp [Nat.not_lt.mpr had]

/-- One-sided envelope for the dangerous positive contribution. -/
def positiveEnvelope (m t : ℕ) : ℕ :=
  if smallRadical m t ≤ t then 0 else
    ((smallPrimes m t).card - 1).choose (((smallPrimes m t).card - 1) / 2)

theorem tail_le_envelope {m t : ℕ} (hm : 2 ≤ m) (ht : 1 ≤ t) :
    tail m t ≤ (positiveEnvelope m t : ℤ) := by
  classical
  by_cases hn : (smallPrimes m t).Nonempty
  · by_cases hle : smallRadical m t ≤ t
    · simp [positiveEnvelope, hle, tail_zero_when_smallRadical_le hm hn hle]
    · calc
        tail m t = tail (smallRadical m t) t := tail_smallRadical hm hn
        _ ≤ |tail (smallRadical m t) t| := le_abs_self _
        _ ≤ _ := by
          simpa only [positiveEnvelope, if_neg hle, factors_smallRadical] using
            (abs_tail_le_central_choose (smallRadical_two_le hn) t)
  · rw [tail_minus_one_when_rough hm ht (Finset.not_nonempty_iff_eq_empty.mp hn)]
    omega

open FourierWindow PrimeCharacter PrimeEndpoint

attribute [local instance] allCharacters

/-- Pointwise in the target N, the actual corrected analytic endpoint from
    the published paper is bounded by the truncated-radical envelope. The
    input S may impose all of the original coprimality and roughness masks. -/
theorem corrected_endpoint_le {N q X t : ℕ} [Fact q.Prime]
    (S : Finset ℕ) (c : ℝ) (linear : DirichletCharacter ℂ q → ℝ)
    (hX : 2 ≤ X) (hq : X * X < q) (hc : 0 < c) (ht : 1 ≤ t)
    (hRange : ∀ n ∈ S, 2 ≤ n ∧ n ≤ X)
    (hRatio : ∀ n ∈ S, ∀ m ∈ S, n < 2 * m)
    (hComp : ∀ n ∈ S, 2 ≤ N - n) :
    let w := fun n => (tail (N - n) t : ℝ)
    let coeff := dirichletCoeff S c ((q - 1 : ℕ) : ℝ) w (id : DirichletCharacter ℂ q → _)
    PaperFourier.endpoint X (centeredSpectralRamp q X ArithmeticFunction.vonMangoldt coeff linear) +
      coeff 1 * (X : ℝ) * ((X : ℝ) + 1) * Real.log (1 + 1 / (X : ℝ)) ≤
        ∑ n ∈ S, ArithmeticFunction.vonMangoldt n * (positiveEnvelope (N - n) t : ℝ) := by
  dsimp only
  rw [← vonMangoldt_endpoint S c (fun n => (tail (N - n) t : ℝ)) linear hX hq hc hRange hRatio]
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
  exact_mod_cast tail_le_envelope (hComp n hn) ht

/-- An actual prime input in the balanced window realizes the sharp Sperner
    coefficient for four distinct complementary primes: 1155=3*5*7*11. -/
theorem attained_at_prime_input :
    Nat.Prime 1151 ∧ Nat.Coprime 1151 2306 ∧ 2306 ≤ 3 * 1151 ∧ 3 * 1151 < 2 * 2306 ∧
    (2306 - 1151 : ℕ).minFac = 3 ∧ tail (2306 - 1151) 11 = 3 := by
  refine ⟨by norm_num, by decide, by decide, by decide, by norm_num, ?_⟩
  rw [tail_as_subsets (by decide)]
  change (∑ s ∈ (1155 : ℕ).primeFactors.powerset, if 11 < value s then parity s else 0) = 3
  have hs : ∀ p ∈ ({3,5,7,11} : Finset ℕ), p.Prime := by
    intro n hn
    simp only [mem_insert, mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl <;> norm_num
  have hv : (∏ a ∈ ({3,5,7,11} : Finset ℕ), a) = 1155 := by norm_num
  rw [← hv, Nat.primeFactors_prod hs]
  decide

#print axioms abs_tail_le_central_choose
#print axioms tail_smallRadical
#print axioms tail_le_envelope
#print axioms corrected_endpoint_le
#print axioms attained_at_prime_input
end Goldbach.SieveWeight
