import Rigidity.Proofs.Regularity.PlanarOrderZero
import Rigidity.External.PlanarInputs
import Rigidity.Proofs.Percolation.BondUniqueness
import Rigidity.Proofs.Percolation.SupercriticalUniqueness

/-!
# The planar order-zero regularity input from Lemma 7.1

`armstrongDarioOrderZeroTwo_of_planarHarmonicApproximation` proves the planar order-zero input
`Rigidity.External.ArmstrongDarioOrderZeroTwo` (Armstrong–Dario, arXiv:1609.09431v2, Theorem 2 (iii)
for `k = 0`, in dimension two) from Lemma 7.1 in the form `PlanarHarmonicApproximationTwo`. The
other ingredients are proved: the almost sure uniqueness of the infinite cluster
(`Rigidity.Percolation.supercritical_bond_uniqueness`), the density of the infinite cluster in
triadic cubes (Dario–Gu, Proposition A.1, `Rigidity.Proofs.S2.cluster_density_concentration`), which
gives `|𝒞_∞ ∩ B_s| ≥ (θ(p) / 162) s²` above a minimal scale (`card_ball_ge_of_clusterCubeDensity`),
the decay with constants of `exists_planarOrderZeroDecay`, and the Liouville argument
`orderZero_regularity_of_decay`. The minimal scale is
`A² max(𝒳, 18 max(𝓜, 1), c₁) ≤ O_s(θ)` by the stability of `O_s` under maxima and multiples.
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

/-- **Density of the cluster balls** from the density in cubes: if every triadic cube of size
`3^m ≥ ℓ` inside `B_{9 · 3^m}` carries `κ 3^{2m}` vertices of `C`, then
`|C ∩ B_s| ≥ (κ / 81) s²` for `s ≥ 18 max(ℓ, 1)`. -/
theorem card_ball_ge_of_clusterCubeDensity {ω : Configuration 2} (C : OpenComponent ω)
    {ℓ κ : ℝ} (hκ : 0 ≤ κ) (hcube : ClusterCubeDensity C 0 9 ℓ κ) {s : ℝ}
    (hs : 18 * max ℓ 1 ≤ s) : κ / 81 * s ^ 2 ≤ (componentEuclideanBall C 0 s).card := by
  classical
  have h1 : 1 ≤ s / 18 := by
    rw [le_div_iff₀ (by norm_num)]; have := le_max_right ℓ 1; linarith
  obtain ⟨m, hm1, hm2⟩ := exists_three_pow_near h1
  have hℓ : ℓ ≤ 3 ^ m := by
    have := le_max_left ℓ 1; linarith
  have hsq : Real.sqrt ((2 : ℕ) : ℝ) < 3 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h3 : (0 : ℝ) < 3 ^ m := by positivity
  have hw : dist (latticeEuclideanEmbedding (0 : Vertex 2)) (latticeEuclideanEmbedding 0) +
      Real.sqrt ((2 : ℕ) : ℝ) * 3 ^ m < s := by
    rw [dist_self, zero_add]
    calc Real.sqrt ((2 : ℕ) : ℝ) * 3 ^ m < 3 * 3 ^ m := by gcongr
      _ ≤ s := by linarith
  have hρ : s ≤ 9 * 3 ^ m := by linarith
  have h := le_card_filter_of_clusterCubeDensity C 0 hcube hℓ hw hρ (fun _ => True)
    fun _ _ => trivial
  rw [filter_true_of_mem fun _ _ => trivial] at h
  have hm : (3 : ℝ) ^ (2 * m) = (3 ^ m) ^ 2 := by rw [pow_mul']
  rw [hm] at h
  have hs9 : s / 9 ≤ 3 ^ m := by linarith
  have hs0 : 0 ≤ s / 9 := by linarith
  calc κ / 81 * s ^ 2 = κ * (s / 9) ^ 2 := by ring
    _ ≤ κ * (3 ^ m) ^ 2 := by gcongr
    _ ≤ _ := h

/-- **The planar order-zero regularity input** (`ArmstrongDarioOrderZeroTwo`, Armstrong–Dario,
Theorem 2 (iii) for `k = 0` in dimension two) from Lemma 7.1 in the form
`PlanarHarmonicApproximationTwo`. -/
theorem armstrongDarioOrderZeroTwo_of_planarHarmonicApproximation
    (hHA : PlanarHarmonicApproximationTwo) : ArmstrongDarioOrderZeroTwo := by
  intro p hpc hp1
  obtain ⟨s₁, θ₁, A, α, K, hs₁, hθ₁, hA, hα, hK, X, hXm, hX1, hXos, hae⟩ := hHA p hpc hp1
  have hθp : 0 < theta 2 p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  obtain ⟨s₂, C₂, hs₂, hC₂, hcube⟩ := exists_clusterCubeDensity_of_concentration (d := 2) le_rfl p
    (cluster_density_concentration 2 le_rfl p hpc hp1) 9
  obtain ⟨M, hMm, hM0, hMos, hMae⟩ := hcube 0
  have hκ : 0 < theta 2 p / 2 / 81 := by positivity
  obtain ⟨c₁, K', hc₁, hK', hdecay⟩ := exists_planarOrderZeroDecay hA hα hK hκ
  have hA0 : 0 < A := by linarith
  have hc₁0 : 0 < c₁ := lt_of_lt_of_le one_pos hc₁
  -- the minimal scale and its stretched exponential moment
  set s := min s₁ s₂ with hsdef
  have hs : 0 < s := lt_min hs₁ hs₂
  have h1 := IsOsBond.mono_exponent hs (by rw [hsdef]; exact min_le_left _ _) hXm hXos
  have hM1 := IsOsBond.max hs₂ hC₂ (by positivity) hMm measurable_const hMos
    (isOsBond_const (p := p) (d := 2) one_pos hs₂)
  have hM18 := IsOsBond.const_mul (by norm_num : (0 : ℝ) < 18) hM1
  have hM18m : Measurable fun ω => 18 * max (M ω) 1 := (hMm.max measurable_const).const_mul 18
  have h2 := IsOsBond.mono_exponent hs (by rw [hsdef]; exact min_le_right _ _) hM18m hM18
  have h12 := IsOsBond.max hs (by positivity) (by positivity) hXm hM18m h1 h2
  have h3 := isOsBond_const (p := p) (d := 2) hc₁0 hs
  have h12m : Measurable fun ω => max (X ω) (18 * max (M ω) 1) := hXm.max hM18m
  have h123 := IsOsBond.max hs (by positivity) (by positivity) h12m measurable_const h12 h3
  have hY := IsOsBond.const_mul (by positivity : (0 : ℝ) < A ^ 2) h123
  set Y : Configuration 2 → ℝ := fun ω => A ^ 2 * max (max (X ω) (18 * max (M ω) 1)) c₁
    with hYdef
  have hYm : Measurable Y := (h12m.max measurable_const).const_mul _
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => by
    simp only [hYdef]
    exact mul_nonneg (sq_nonneg _) (hc₁0.le.trans (le_max_right _ _))
  obtain ⟨θY, hθY, hint, hle⟩ : ∃ θ : ℝ, 0 < θ ∧ IsOsBond 2 p Y s θ := ⟨_, by positivity, hY⟩
  have e : (fun ω => Real.exp (Real.rpow (max (Y ω / θY) 0) s)) =
      fun ω => Real.exp (Real.rpow (Y ω / θY) s) := by
    funext ω
    rw [max_eq_left (div_nonneg (hY0 ω) hθY.le)]
  refine ⟨s, θY, K', hs, hθY, hK', Y, hYm, hY0, by rw [← e]; exact hint, by rw [← e]; exact hle,
    ?_⟩
  -- almost surely
  have hUae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ uniqueInfiniteComponentEvent 2 :=
    (ae_iff_measure_eq (measurableSet_uniqueInfiniteComponentEvent 2).nullMeasurableSet).2
      (by rw [measure_univ]
          exact Rigidity.Percolation.supercritical_bond_uniqueness.2 2 le_rfl p hpc hp1)
  filter_upwards [hUae, hae, hMae] with ω hU hω₁ hω₂
  refine ⟨hU, fun h' => ?_⟩
  haveI : Nonempty (uniqueInfiniteComponent h') :=
    (uniqueInfiniteComponent_infinite h').nonempty.to_subtype
  have hdens : ∀ t : ℝ, 18 * max (M ω) 1 ≤ t →
      theta 2 p / 2 / 81 * t ^ 2 ≤ (componentEuclideanBall (uniqueInfiniteComponent h') 0 t).card :=
    fun t ht => card_ball_ge_of_clusterCubeDensity _ (by positivity) (hω₂ h') ht
  exact orderZero_regularity_of_decay (uniqueInfiniteComponent h')
    (hdecay (uniqueInfiniteComponent h') (X ω) (18 * max (M ω) 1) (hX1 ω) (hω₁ h') hdens)

end Rigidity.Proofs.Regularity
