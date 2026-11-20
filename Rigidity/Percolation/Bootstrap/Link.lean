import Rigidity.Percolation.Bootstrap.Iteration

/-!
# Connection of seeds at all large scales

Above criticality, for every `ε > 0` there is a seed radius `u` such that, at arbitrarily large
scales `m`, every left seed and every right seed of scale `m` are joined inside `Q_{6m}` with
probability at least `1 - ε`. This is Theorem 2.1.2 of D. Contreras, *Percolation on graphs of
polynomial growth*, ETH Zürich dissertation (2022), proved by the repaired bootstrap: the levels
`p_s < p₀ < p = p₀ + δ` are fixed, the conditioning is at level `p₀` at every scale and every
bond is sprinkled at most once, so the number of scales is unrestricted.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

variable {d : ℕ}

/-- **Seeds are joined at all large scales.** -/
theorem exists_seed_link [NeZero d] {a b : Fin d} (hab : a ≠ b) {p : unitInterval}
    (hp : criticalProbability d < (p : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℕ, ∀ N : ℕ, ∃ m : ℕ, N ≤ m ∧ u + 1 ≤ m / 8 ∧
      ∀ S T : Finset (Vertex d), LeftSeed a u m S → LeftSeed a u m (T.image (flipA a)) →
        1 - ε ≤ (latticeBondLaw d p).real {η | ConnectsRegions η (cubeAt 0 (6 * m)) S T} := by
  obtain ⟨p_s, hθ, hps⟩ := (criticalProbability_lt_iff (d := d) (p : ℝ)).1 hp
  set δ : ℝ := ((p : ℝ) - p_s) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set p₀ : unitInterval := ⟨((p_s : ℝ) + p) / 2, by
    constructor <;> linarith [p_s.property.1, p.property.2]⟩ with hp₀def
  have hp₀δ : (p₀ : ℝ) + δ = p := by
    simp only [hp₀def, hδdef]
    ring
  have hδ1 : (p₀ : ℝ) + δ ≤ 1 := by rw [hp₀δ]; exact p.property.2
  have hp₀1 : (p₀ : ℝ) < 1 := by
    simp only [hp₀def]
    linarith [p.property.2]
  have hps₀ : (p_s : ℝ) < p₀ := by
    simp only [hp₀def]
    linarith
  have hq : raisedLevel p₀ δ hδ.le hδ1 = p := Subtype.ext hp₀δ
  set e₀ : ℝ := min (ε / 3) (1 / 4) with he₀def
  have he₀ : 0 < e₀ := lt_min (by positivity) (by norm_num)
  have hδ1' : δ ≤ 1 := by linarith [p₀.property.1]
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (1 - δ) ^ K < e₀ / 8 :=
    exists_pow_lt_of_lt_one (by positivity) (by linarith)
  have hpK : 0 < (1 - (p₀ : ℝ)) ^ K := pow_pos (by linarith) _
  set η : ℝ := e₀ / 8 * (1 - (p₀ : ℝ)) ^ K with hηdef
  have hη : 0 < η := by positivity
  set ε₁ : ℝ := η / (1 - (p₀ : ℝ)) ^ K + (1 - δ) ^ K with hε₁def
  have hε₁ : ε₁ ≤ e₀ / 4 := by
    have : η / (1 - (p₀ : ℝ)) ^ K = e₀ / 8 := by
      rw [hηdef]
      field_simp
    rw [hε₁def, this]
    linarith
  have hε₁pos : 0 < ε₁ :=
    add_pos_of_pos_of_nonneg (div_pos hη hpK) (pow_nonneg (by linarith) _)
  set e : ℝ := 4 * ε₁ with hedef
  have he0 : 0 < e := by positivity
  have he : e ≤ 1 / 4 := by
    have : e₀ ≤ 1 / 4 := min_le_right _ _
    linarith
  have heε : 3 * e ≤ ε := by
    have : e₀ ≤ ε / 3 := min_le_left _ _
    linarith
  obtain ⟨u, mF, hF⟩ := exists_leftSeed_anchor_prob hab hθ hps₀ hp₀1 hη
  set m₀ := mF + 8 * (u + 2) with hm₀
  set π₀ : ℝ := δ ^ (cubeFinset (0 : Vertex d) (6 * m₀)).card with hπ₀def
  have hπ₀ : 0 < π₀ := pow_pos hδ _
  have hπ₀1 : π₀ ≤ 1 := pow_le_one₀ hδ.le hδ1'
  have hscale : ∀ r : ℕ, m₀ ≤ 3 ^ r * m₀ := fun r =>
    Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) r)
  have hgood : ∀ r : ℕ, BootGood a u (3 ^ r * m₀) p₀ (raisedLevel p₀ δ hδ.le hδ1)
      ((bootMap e)^[r] π₀) := by
    intro r
    induction r with
    | zero =>
      have h := bootGood_base a u m₀ (p₀ := p₀) (q := raisedLevel p₀ δ hδ.le hδ1)
        (by change (p₀ : ℝ) ≤ (p₀ : ℝ) + δ; linarith)
      have hsub : ((raisedLevel p₀ δ hδ.le hδ1 : unitInterval) : ℝ) - p₀ = δ := by
        change (p₀ : ℝ) + δ - p₀ = δ
        ring
      rw [hsub] at h
      simpa using h
    | succ r ih =>
      have hmem := iterate_bootMap_mem he0.le (by linarith) hπ₀.le hπ₀1 r
      have hm1 : 1 ≤ 3 ^ r * m₀ := le_trans (by omega) (hscale r)
      have hu : u + 1 ≤ 3 ^ r * m₀ / 8 := by
        have := hscale r
        omega
      have hstep := bootGood_step hab hm1 hu p₀ hp₀1 δ hδ hδ1 K hmem.1 hmem.2
        (fun k S hS => hF (3 ^ r * m₀) (le_trans (by omega) (hscale r)) (sgOf k) S hS) ih
      rw [Function.iterate_succ_apply', pow_succ, mul_comm (3 ^ r) 3, mul_assoc]
      exact hstep
  obtain ⟨R, hR⟩ := exists_iterate_bootMap he0 he hπ₀ hπ₀1
  refine ⟨u, fun N => ⟨3 ^ (R + N) * m₀, ?_, ?_, fun S T hS hT => ?_⟩⟩
  · have h1 : N < 3 ^ (R + N) :=
      lt_of_lt_of_le (Nat.lt_pow_self (by norm_num)) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : 1 ≤ m₀ := by omega
    nlinarith
  · have := hscale (R + N)
    omega
  · have h1 := (hgood (R + N)).le_connect hp₀1 hS hT
    have h2 := hR (R + N) (by omega)
    rw [hq] at h1
    linarith

end Rigidity.Percolation
