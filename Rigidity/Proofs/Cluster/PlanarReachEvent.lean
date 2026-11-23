import Rigidity.Proofs.Cluster.PlanarMinimalScales
import Rigidity.Proofs.Percolation.PlanarNuSubadditiveMoments

/-!
# The event that the reach of the planar partition is small on a cube

`PlanarReachLe ω U ℓ` is the event that the planar partition exists and its reach is at most `3^ℓ`
at every vertex of the triadic cube `U`. Its complement has probability at most
`|U| · 2 exp(-3^ℓ/θ)` (`exists_measure_not_planarReachLe_le`): the reach is at most the size of
the partition into coarsely good cubes, which has an exponential moment (Proposition 2.1 of
Armstrong and Dario). On the event, every partition cube meeting `U` has scale at most `ℓ`, so every
triadic cube of scale at least `ℓ` inside `U` is resolved (`planarResolved_of_planarReachLe`), and
the reach sums are at most `121 (ℓ + 1) 3^{kℓ}` (`reachSum_le_of_planarReach_le`). These are the
deterministic inputs of the stochastic bounds of Section 5 in dimension two.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

/-- The planar partition exists and its reach is at most `3^ℓ` on `U`. -/
def PlanarReachLe (ω : Configuration 2) (U : TriadicCube 2) (ℓ : ℕ) : Prop :=
  PlanarPartitionEvent ω ∧ ∀ a ∈ U.toIntegerCube.vertices, planarReach ω a ≤ 3 ^ ℓ

theorem ennreal_three_pow_le_iff {a b : ℕ} : (3 : ℝ≥0∞) ^ a ≤ 3 ^ b ↔ a ≤ b := by
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by norm_num, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_le_ofReal_iff (by positivity)]
  exact pow_le_pow_iff_right₀ (by norm_num)

/-- A partition cube whose square of side `9s` contains `a` has scale at most `ℓ` when the reach at
`a` is at most `3^ℓ`. -/
theorem scale_le_of_planarReach_le {a : Vertex 2} {ℓ : ℕ} (h : planarReach ω a ≤ 3 ^ ℓ)
    {Q : TriadicCube 2} (hQ : Q.IsMaximalStopping (planarGoodCubes ω))
    (ha : a ∈ (↑Q.ninefold.vertices : Set (Vertex 2))) : Q.scale ≤ ℓ := by
  have h1 : (3 : ℝ≥0∞) ^ Q.scale ≤ planarReach ω a := by
    unfold planarReach
    exact le_iSup₂_of_le Q ⟨hQ, ha⟩ le_rfl
  exact ennreal_three_pow_le_iff.1 (h1.trans h)

theorem partCube_scale_le_of_planarReach_le (hP : PlanarPartitionEvent ω) {a : Vertex 2} {ℓ : ℕ}
    (h : planarReach ω a ≤ 3 ^ ℓ) : (planarPartCube ω a).scale ≤ ℓ := by
  have hx : a ∈ (planarPartCube ω a).ninefold.vertices :=
    TriadicCube.subset_ninefold_of_mem_planarSquares
      (planarPartCube ω a).toIntegerCube_mem_planarSquares
      (((planarPartCube ω a).mem_toIntegerCube_vertices a).2 (planarPartCube_spec hP a).1)
  exact scale_le_of_planarReach_le h (planarPartCube_spec hP a).2 (Finset.mem_coe.2 hx)

theorem partSide_le_of_planarReach_le (hP : PlanarPartitionEvent ω) {a : Vertex 2} {ℓ : ℕ}
    (h : planarReach ω a ≤ 3 ^ ℓ) : partSide ω a ≤ 3 ^ ℓ :=
  pow_le_pow_right₀ (by norm_num) (partCube_scale_le_of_planarReach_le hP h)

/-- On the event, every triadic cube of scale at least `ℓ` inside `U` is resolved. -/
theorem planarResolved_of_planarReachLe {U V : TriadicCube 2} {ℓ : ℕ}
    (h : PlanarReachLe ω U ℓ) (hV : V.vertices ⊆ U.vertices) (hℓ : ℓ ≤ V.scale) :
    PlanarResolved ω V := fun z hz =>
  (partCube_scale_le_of_planarReach_le h.1
    (h.2 z ((U.mem_toIntegerCube_vertices z).2 (hV hz)))).trans hℓ

/-- **The reach sums on the event.** -/
theorem reachSum_le_of_planarReach_le {a : Vertex 2} {ℓ : ℕ} (h : planarReach ω a ≤ 3 ^ ℓ)
    (k : ℕ) : reachSum ω k a ≤ 121 * (ℓ + 1) * 3 ^ (k * ℓ) := by
  set b : ℝ≥0∞ := 3 ^ (k * ℓ) with hb
  have hterm : ∀ Q : TriadicCube 2,
      (if Q.IsMaximalStopping (planarGoodCubes ω) ∧
        a ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) then (3 : ℝ≥0∞) ^ (k * Q.scale) else 0) ≤
      if a ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) ∧ Q.scale ≤ ℓ then b else 0 := by
    intro Q
    split_ifs with h1 h2 h2
    · exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left k h2.2)
    · exact absurd ⟨h1.2, scale_le_of_planarReach_le h h1.1 h1.2⟩ h2
    · exact zero_le
    · exact le_rfl
  let e : ℕ × (Fin 2 → ℤ) ≃ TriadicCube 2 :=
    { toFun := fun q => ⟨q.1, q.2⟩
      invFun := fun Q => (Q.scale, Q.index)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hzero : ∀ s ∉ Finset.range (ℓ + 1), ∑' idx : Fin 2 → ℤ,
      (if a ∈ (↑(TriadicCube.ninefold ⟨s, idx⟩).vertices : Set (Vertex 2)) ∧ s ≤ ℓ then b
        else 0) = 0 := by
    intro s hs
    have hs' : ¬ s ≤ ℓ := by
      rw [Finset.mem_range] at hs
      omega
    simp [hs']
  unfold reachSum
  calc ∑' Q : TriadicCube 2, (if Q.IsMaximalStopping (planarGoodCubes ω) ∧
        a ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) then (3 : ℝ≥0∞) ^ (k * Q.scale) else 0)
      ≤ ∑' Q : TriadicCube 2,
          (if a ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) ∧ Q.scale ≤ ℓ then b else 0) :=
        ENNReal.tsum_le_tsum hterm
    _ = ∑' q : ℕ × (Fin 2 → ℤ),
          (if a ∈ (↑(TriadicCube.ninefold ⟨q.1, q.2⟩).vertices : Set (Vertex 2)) ∧ q.1 ≤ ℓ
            then b else 0) :=
        (e.tsum_eq (fun Q =>
          if a ∈ (↑Q.ninefold.vertices : Set (Vertex 2)) ∧ Q.scale ≤ ℓ then b else 0)).symm
    _ = ∑' s : ℕ, ∑' idx : Fin 2 → ℤ,
          (if a ∈ (↑(TriadicCube.ninefold ⟨s, idx⟩).vertices : Set (Vertex 2)) ∧ s ≤ ℓ then b
            else 0) :=
        ENNReal.tsum_prod (f := fun s idx =>
          if a ∈ (↑(TriadicCube.ninefold ⟨s, idx⟩).vertices : Set (Vertex 2)) ∧ s ≤ ℓ then b
            else 0)
    _ = ∑ s ∈ Finset.range (ℓ + 1), ∑' idx : Fin 2 → ℤ,
          (if a ∈ (↑(TriadicCube.ninefold ⟨s, idx⟩).vertices : Set (Vertex 2)) ∧ s ≤ ℓ then b
            else 0) := tsum_eq_sum hzero
    _ ≤ ∑ _s ∈ Finset.range (ℓ + 1), 121 * b := by
        refine Finset.sum_le_sum fun s _ => ?_
        refine (ENNReal.tsum_le_tsum fun idx => ?_).trans (tsum_ninefold_indicator_le a s b)
        split_ifs with h1 h2 h2
        · exact le_rfl
        · exact absurd h1.1 h2
        · exact zero_le
        · exact le_rfl
    _ = 121 * (ℓ + 1) * b := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- **The reach is small on a cube, with exponentially high probability.** -/
theorem exists_measure_not_planarReachLe_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ (U : TriadicCube 2) (ℓ : ℕ),
      latticeBondLaw 2 p {ω | ¬ PlanarReachLe ω U ℓ} ≤
        ENNReal.ofReal ((9 : ℝ) ^ U.scale * (2 * Real.exp (-((3 : ℝ) ^ ℓ / θ)))) := by
  set μ := latticeBondLaw 2 p with hμ
  obtain ⟨C₀, hC₀, c₀, hc₀, hq₀⟩ := exists_measure_not_mem_planarCoarseGood_le hpc
  obtain ⟨hH, ⟨θ, hθ, hmom⟩, -⟩ := partition_estimates_general (d := 2) (by norm_num) μ
    planarCoarseGood measurableSet_mem_planarCoarseGood hC₀ hc₀ one_pos hq₀
  refine ⟨θ, hθ, fun U ℓ => ?_⟩
  set N₀ := {ω : Configuration 2 | ¬ (PlanarPartitionEvent ω ∧ ∀ x : Vertex 2,
    ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarCoarseGood ω))} with hN₀
  have hN₀0 : μ N₀ = 0 := by
    have h := (ae_planarPartitionEvent hpc).and hH
    exact ae_iff.1 h
  have hsub : {ω | ¬ PlanarReachLe ω U ℓ} ⊆ N₀ ∪ ⋃ a ∈ U.toIntegerCube.vertices,
      {ω | (3 : ℝ) ^ ℓ < TriadicCube.stoppingSize (planarCoarseGood ω) a} := by
    intro ω hω
    by_cases hg : PlanarPartitionEvent ω ∧ ∀ x : Vertex 2,
        ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarCoarseGood ω)
    · right
      have hω' : ¬ ∀ a ∈ U.toIntegerCube.vertices, planarReach ω a ≤ 3 ^ ℓ :=
        fun h => hω ⟨hg.1, h⟩
      push Not at hω'
      obtain ⟨a, ha, hlt⟩ := hω'
      refine Set.mem_biUnion ha ?_
      change (3 : ℝ) ^ ℓ < TriadicCube.stoppingSize (planarCoarseGood ω) a
      by_contra hle
      push Not at hle
      refine hlt.not_ge ((planarReach_le_stoppingSize hg.2 a).trans ?_)
      rw [show (3 : ℝ≥0∞) ^ ℓ = ENNReal.ofReal ((3 : ℝ) ^ ℓ) by
        rw [ENNReal.ofReal_pow (by norm_num)]; norm_num]
      exact ENNReal.ofReal_le_ofReal hle
    · left
      exact hg
  have ha : ∀ a, μ {ω | (3 : ℝ) ^ ℓ < TriadicCube.stoppingSize (planarCoarseGood ω) a} ≤
      ENNReal.ofReal (2 * Real.exp (-((3 : ℝ) ^ ℓ / θ))) := by
    intro a
    have h := measure_lt_le_of_exp_rpow_moment μ hθ one_pos (hmom a).1 (hmom a).2
      (t := (3 : ℝ) ^ ℓ) (by positivity)
    simpa only [Real.rpow_one] using h
  calc μ {ω | ¬ PlanarReachLe ω U ℓ}
      ≤ μ N₀ + ∑ a ∈ U.toIntegerCube.vertices,
          μ {ω | (3 : ℝ) ^ ℓ < TriadicCube.stoppingSize (planarCoarseGood ω) a} :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans
          (add_le_add le_rfl (measure_biUnion_finset_le _ _)))
    _ ≤ 0 + ∑ _a ∈ U.toIntegerCube.vertices,
          ENNReal.ofReal (2 * Real.exp (-((3 : ℝ) ^ ℓ / θ))) := by
        rw [hN₀0]
        exact add_le_add le_rfl (Finset.sum_le_sum fun a _ => ha a)
    _ = _ := by
        rw [zero_add, Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), card_toIntegerCube_vertices_eq]

end Rigidity.Proofs.Cluster
