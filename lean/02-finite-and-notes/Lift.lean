import Residues

namespace GoldbachFilter

/-- Any 72 consecutive integers below N contain a first summand that passes
    the filter together with its exact complement. -/
theorem allowed_pair_in_window (N L : Nat) (heven : N % 2 = 0)
    (hroom : L + 71 ≤ N) :
    ∃ m : Nat, L ≤ m ∧ m ≤ L + 71 ∧ Allowed m ∧ Allowed (N - m) := by
  obtain ⟨a, b, ha, hb, hA, hB, hcong⟩ := even_local_pair N heven
  let m := a + 72 * ((L + 71 - a) / 72)
  have hbounds : L ≤ m ∧ m ≤ L + 71 := by dsimp [m]; omega
  have hm : m % 72 = a := by dsimp [m]; omega
  have hn : (N - m) % 72 = b := by omega
  refine ⟨m, hbounds.1, hbounds.2, (allowed_mod72 _).mp ?_, (allowed_mod72 _).mp ?_⟩
  · rwa [hm]
  · rwa [hn]

/-- The smaller summands form an arithmetic progression of length at least
    floor(N / 432). Their complements give distinct unordered balanced pairs. -/
theorem balanced_allowed_progression (N : Nat) (heven : N % 2 = 0)
    (hlarge : 432 ≤ N) :
    ∃ a : Nat, ∀ t : Nat, t < N / 432 →
      let m := a + 72 * t
      let n := N - m
      m + n = N ∧ N ≤ 3 * m ∧ m ≤ n ∧ 3 * n ≤ 2 * N ∧
        Allowed m ∧ Allowed n := by
  obtain ⟨a, hlo, hhi, ha, hb⟩ :=
    allowed_pair_in_window N ((N + 2) / 3) heven (by omega)
  refine ⟨a, ?_⟩
  intro t ht
  dsimp only
  have hsmall : 2 * (a + 72 * t) ≤ N := by omega
  have hm : (a + 72 * t) % 72 = a % 72 := by omega
  have hn : (N - (a + 72 * t)) % 72 = (N - a) % 72 := by omega
  refine ⟨by omega, by omega, by omega, by omega, (allowed_mod72 _).mp ?_,
    (allowed_mod72 _).mp ?_⟩
  · rw [hm]
    exact (allowed_mod72 _).mpr ha
  · rw [hn]
    exact (allowed_mod72 _).mpr hb

/-- In particular each even N ≥ 432 has a balanced pair of actual integers
    satisfying both residue filters. -/
theorem balanced_allowed_pair (N : Nat) (heven : N % 2 = 0) (hlarge : 432 ≤ N) :
    ∃ m n : Nat, m + n = N ∧ N ≤ 3 * m ∧ m ≤ n ∧ 3 * n ≤ 2 * N ∧
      Allowed m ∧ Allowed n := by
  obtain ⟨a, h⟩ := balanced_allowed_progression N heven hlarge
  exact ⟨a, N - a, by simpa using h 0 (by omega)⟩

end GoldbachFilter
