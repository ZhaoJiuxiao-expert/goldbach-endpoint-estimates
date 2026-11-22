import PrimeEndpoint
import Mathlib.Data.Nat.Squarefree
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Finset.Powerset

open scoped BigOperators
namespace FixedEven.Cubic
open ArithmeticFunction
noncomputable section

def Rough (y m : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ m → y < p

def tail (m t : ℕ) : ℤ :=
  ∑ d ∈ m.divisors.filter (t < ·), moebius d

/-- Once the complementary quotient is smaller than any prime factor,
the only surviving large divisor is the full integer. -/
theorem tail_eq_mu {y m t N : ℕ} (hm : 0 < m) (hmN : m ≤ N) (htm : t < m)
    (hcut : N / (y+1) ≤ t) (hr : Rough y m) : tail m t = moebius m := by
  unfold tail
  have hset : m.divisors.filter (t < ·) = {m} := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨⟨k,hk⟩,_⟩, hd⟩
      by_contra hne
      have hk1 : k ≠ 1 := by rintro rfl; simp_all
      obtain ⟨p,hp,hpk⟩ := Nat.exists_prime_and_dvd hk1
      have hkpos : 0 < k := by by_contra! hh; simp_all
      have hpm : p ∣ m := hpk.trans ⟨d, by simpa [Nat.mul_comm] using hk⟩
      have hyk : y+1 ≤ k := (hr p hp hpm).trans_le (Nat.le_of_dvd hkpos hpk)
      have hdN : d ≤ N / (y+1) := (Nat.le_div_iff_mul_le (by omega)).2
        ((Nat.mul_le_mul_left d hyk).trans (hk ▸ hmN))
      omega
    · rintro rfl
      exact ⟨⟨dvd_rfl,hm.ne'⟩,htm⟩
  simp [hset]

def pool (y B : ℕ) : Finset ℕ := (Finset.Ioc y B).filter Nat.Prime

private theorem prod_lower (s : Finset ℕ) (z : ℕ) (hs : ∀ a ∈ s, z ≤ a) :
    z ^ s.card ≤ ∏ p ∈ s, p := by
  simpa using (Finset.prod_le_prod' (s := s) (f := fun _ => z) (g := fun n => n) hs)

/-- Each spurious negative sign identifies three different primes in a
short list; the prime product uniquely recovers the reflected integer. -/
theorem triple_signature {y m N : ℕ} (_hm : 1 < m) (hmN : m ≤ N)
    (hsize : N < (y+1)^5) (hr : Rough y m) (hmu : moebius m = -1)
    (hcomp : ¬m.Prime) :
    m.primeFactors ∈ (pool y (N / (y+1)^2)).powersetCard 3 ∧
    (∏ p ∈ m.primeFactors, p) = m := by
  have hsf : Squarefree m := moebius_ne_zero_iff_squarefree.mp (by omega)
  have hprod := Nat.prod_primeFactors_of_squarefree hsf
  have hmin (p : ℕ) (hp : p ∈ m.primeFactors) : y+1 ≤ p :=
    hr p (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)
  have hc : m.primeFactors.card = cardFactors m := by
    rw [← Nat.toFinset_factors, List.toFinset_card_of_nodup hsf.nodup_primeFactorsList]
    rfl
  have hlt : m.primeFactors.card < 5 := by
    by_contra! hg
    have hpow := Nat.pow_le_pow_right (by omega : 0 < y+1) hg
    have hl := prod_lower m.primeFactors (y+1) hmin
    omega
  have h3 : m.primeFactors.card = 3 := by
    rw [moebius_apply_of_squarefree hsf, ← hc] at hmu
    have hone : m.primeFactors.card ≠ 1 := fun hh =>
      hcomp (cardFactors_eq_one_iff_prime.mp (hc ▸ hh))
    interval_cases m.primeFactors.card <;> norm_num at *
  refine ⟨Finset.mem_powersetCard.mpr ⟨?_, h3⟩,hprod⟩
  intro p hp
  refine Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hmin p hp, ?_⟩,
    Nat.prime_of_mem_primeFactors hp⟩
  have hrest := prod_lower (m.primeFactors.erase p) (y+1)
    (fun a ha => hmin a (Finset.mem_of_mem_erase ha))
  rw [Finset.card_erase_of_mem hp, h3] at hrest
  have hmul := Nat.mul_le_mul_left p hrest
  rw [Finset.mul_prod_erase m.primeFactors (fun n => n) hp, hprod] at hmul
  exact (Nat.le_div_iff_mul_le (by positivity)).2 (hmul.trans hmN)

def detected (S : Finset ℕ) (N t : ℕ) :=
  S.filter fun n => n.Prime ∧ tail (N-n) t = -1

def genuine (S : Finset ℕ) (N : ℕ) :=
  S.filter fun n => n.Prime ∧ (N-n).Prime

/-- A uniform finite error bound at the cubic roughness scale. The error
is at most the number of unordered triples of different small primes. -/
theorem count_error (S : Finset ℕ) {N y t : ℕ}
    (hcut : N / (y+1) ≤ t) (hsize : N < (y+1)^5)
    (hs : ∀ n ∈ S, 1 < N-n ∧ t < N-n ∧ Rough y (N-n)) :
    (genuine S N).card ≤ (detected S N t).card ∧
    (detected S N t).card ≤ (genuine S N).card +
      (pool y (N / (y+1)^2)).card.choose 3 := by
  classical
  have heval (n : ℕ) (hn : n ∈ S) : tail (N-n) t = moebius (N-n) := by
    obtain ⟨h1, h2, h3⟩ := hs n hn
    exact tail_eq_mu (by omega) (Nat.sub_le ..) h2 hcut h3
  have hsub : genuine S N ⊆ detected S N t := by
    intro n hn
    obtain ⟨hn,hpr,hq⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hn,hpr,by rw [heval n hn, moebius_apply_prime hq]⟩
  have hkey (n : ℕ) (hn : n ∈ detected S N t \ genuine S N) :
      (N-n).primeFactors ∈ (pool y (N/(y+1)^2)).powersetCard 3 ∧
      (∏ p ∈ (N-n).primeFactors, p) = N-n := by
    obtain ⟨hd,hg⟩ := Finset.mem_sdiff.mp hn
    obtain ⟨hm,hp,hv⟩ := Finset.mem_filter.mp hd
    have hc : ¬(N-n).Prime := fun h => hg (Finset.mem_filter.mpr ⟨hm,hp,h⟩)
    exact triple_signature (hs n hm).1 (Nat.sub_le ..) hsize (hs n hm).2.2
      ((heval n hm).symm.trans hv) hc
  have hinj : ((detected S N t \ genuine S N : Finset ℕ) : Set ℕ).InjOn
      (fun n => (N-n).primeFactors) := by
    intro n hn k hk heq
    have hn' := (hkey n hn).2
    have hk' := (hkey k hk).2
    dsimp only at heq
    rw [heq] at hn'
    have hns := (hs n (Finset.mem_filter.mp (Finset.mem_sdiff.mp hn).1).1).1
    omega
  have hcard := Finset.card_le_card_of_injOn (fun n => (N-n).primeFactors)
     (fun n hn => (hkey n hn).1) hinj
  rw [Finset.card_sdiff hsub,Finset.card_powersetCard] at hcard
  exact ⟨Finset.card_le_card hsub,by omega⟩

def primeIndicator (n : ℕ) : ℝ := if n.Prime then 1 else 0

def corrected {q : ℕ} [Fact q.Prime] (X : ℕ) (S : Finset ℕ) (c : ℝ)
    (w : ℕ → ℝ) (linear : DirichletCharacter ℂ q → ℝ) : ℝ :=
  let b := Goldbach.FourierWindow.dirichletCoeff S c ((q-1 : ℕ) : ℝ) w
    (id : DirichletCharacter ℂ q → _)
  PaperFourier.endpoint X (Goldbach.PrimeEndpoint.centeredSpectralRamp q X primeIndicator b linear) +
    b 1 * (X : ℝ) * ((X : ℝ)+1) * Real.log (1 + 1 / (X : ℝ))

private theorem corrected_eq {q X : ℕ} [Fact q.Prime] (S : Finset ℕ) (c : ℝ)
    (w : ℕ → ℝ) (linear : DirichletCharacter ℂ q → ℝ)
    (hX : 2 ≤ X) (hq : X*X < q) (hc : 0 < c)
    (hr : ∀ n ∈ S, 2 ≤ n ∧ n ≤ X) (hRatio : ∀ n ∈ S, ∀ m ∈ S, n < 2*m) :
    corrected X S c w linear = ∑ n ∈ S, primeIndicator n * w n :=
  (Goldbach.PrimeEndpoint.weighted_endpoint S c w primeIndicator linear hX hq hc
    (by simp [primeIndicator, Nat.not_prime_one]) hr hRatio).symm

/-- Subtract the two corrected endpoints before dividing by two. The original
sieve weight is squared pointwise before constructing the second endpoint. -/
theorem two_endpoints {q X N y t : ℕ} [Fact q.Prime] (S : Finset ℕ) (c : ℝ)
    (linear : DirichletCharacter ℂ q → ℝ)
    (hX : 2 ≤ X) (hq : X*X < q) (hc : 0 < c)
    (hr : ∀ n ∈ S, 2 ≤ n ∧ n ≤ X) (hRatio : ∀ n ∈ S, ∀ m ∈ S, n < 2*m)
    (hcut : N / (y+1) ≤ t)
    (hs : ∀ n ∈ S, 1 < N-n ∧ t < N-n ∧ Rough y (N-n)) :
    let w := fun n : ℕ => (tail (N-n) t : ℝ)
    (corrected X S c (fun n => w n ^ 2) linear - corrected X S c w linear) / 2 =
      ((detected S N t).card : ℝ) := by
  dsimp only
  rw [corrected_eq S c _ linear hX hq hc hr hRatio,
    corrected_eq S c _ linear hX hq hc hr hRatio, ← Finset.sum_sub_distrib]
  apply (div_eq_iff (by norm_num : (2:ℝ) ≠ 0)).mpr
  have hcount : ((detected S N t).card : ℝ) =
      ∑ n ∈ S, if n.Prime ∧ tail (N-n) t = -1 then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp [detected]
  rw [hcount, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨h1,h2,h3⟩ := hs n hn
  rw [tail_eq_mu (by omega) (Nat.sub_le N n) h2 hcut h3]
  rcases moebius_eq_or (N-n) with hm|hm|hm <;>
    by_cases hp : n.Prime <;> norm_num [primeIndicator,hp,hm]

#print axioms tail_eq_mu
#print axioms triple_signature
#print axioms count_error
#print axioms two_endpoints
end
end FixedEven.Cubic
