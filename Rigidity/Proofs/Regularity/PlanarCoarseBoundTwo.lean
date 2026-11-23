import Rigidity.Proofs.Regularity.PlanarCoarseBound

/-!
# Step 2 of Lemma 7.1 on planar squares, almost surely above a minimal scale

`planarCoarseBoundTwo_of_minimalScales` proves Step 2 of the proof of Armstrong–Dario, Lemma 7.1
(arXiv:1609.09431v2), with `w = a` a constant, on the squares of the plane, almost surely above a
minimal scale `𝒳 ≤ O_s(θ)`: `‖[u]_𝒫 - a‖_{L̲²(□_j)} ≤ K ‖u - a‖_{L̲²(C_*(□_{j+3}))}` for the
functions harmonic on `𝒞_∞ ∩ B_R`, `2 · 3^{j+3} ≤ R`. The inputs are the minimal scales of
Proposition 2.4 (`PlanarMinimalScalesTwo p`), the density of the infinite cluster, the planar
Meyers estimate and the comparison (7.8) (`planarCoarseComparisonTwo_of_minimalScales`).
-/

namespace Rigidity.Proofs.Regularity

open Finset MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Percolation
open Rigidity.Proofs.S2 Rigidity.Proofs.Cluster
open scoped Classical ENNReal

/-- The maximum of two minimal scales with `O_s` bounds of exponents `s, s'` has an `O_s` bound
of exponent `min s s'`. -/
theorem exists_isOsBond_max {p : unitInterval} {X Y : Configuration 2 → ℝ} {s s' θ θ' : ℝ}
    (hs : 0 < s) (hs' : 0 < s') (hθ : 0 < θ) (hθ' : 0 < θ') (hX : Measurable X)
    (hY : Measurable Y) (h : IsOsBond 2 p X s θ) (h' : IsOsBond 2 p Y s' θ') :
    ∃ θ'' : ℝ, 0 < θ'' ∧ IsOsBond 2 p (fun ω => max (X ω) (Y ω)) (min s s') θ'' := by
  have hm : 0 < min s s' := lt_min hs hs'
  have h1 := IsOsBond.mono_exponent hm (min_le_left _ _) hX h
  have h2 := IsOsBond.mono_exponent hm (min_le_right _ _) hY h'
  exact ⟨_, by positivity, IsOsBond.max hm (by positivity) (by positivity) hX hY h1 h2⟩

/-- Step 2 of the proof of Armstrong–Dario, Lemma 7.1, with `w = a`, in `L²` on the squares
`□_j` of the plane, almost surely on the infinite cluster above a minimal scale `𝒳 ≤ O_s(θ)`, for
the functions harmonic on `𝒞_∞ ∩ B_R`, `2 · 3^{j+3} ≤ R`. -/
def PlanarCoarseBoundTwo (p : unitInterval) : Prop :=
  ∃ s θ K₃ : ℝ, 0 < s ∧ 0 < θ ∧ 0 ≤ K₃ ∧
    ∃ X : Configuration 2 → ℝ, Measurable X ∧ (∀ ω, 0 ≤ X ω) ∧ IsOsBond 2 p X s θ ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ∀ R : ℝ, ∀ u : uniqueInfiniteComponent h → ℝ,
          IsHarmonicInBall (uniqueInfiniteComponent h) R u →
          ∀ j : ℕ, X ω ≤ 3 ^ j → 2 * 3 ^ (j + 3) ≤ R → ∀ a : ℝ,
            squareL2 j (fun y => planarCoarse (uniqueInfiniteComponent h) u y - a) ≤
              K₃ * clusterSquareL2 ω (j + 3)
                (fun x => Rigidity.Section3.extend (uniqueInfiniteComponent h) u x - a)

/-- **Step 2 on planar squares almost surely**, from the minimal scales of Proposition 2.4. -/
theorem planarCoarseBoundTwo_of_minimalScales {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hM5 : PlanarMinimalScalesTwo p) :
    PlanarCoarseBoundTwo p := by
  obtain ⟨s₀, θ₀, K₂, hs₀, hθ₀, hK₂, X₀, hX₀m, hX₀0, hX₀os, hX₀ae⟩ :=
    planarCoarseComparisonTwo_of_minimalScales hpc hp1 hM5
  obtain ⟨s₃, θ₃, hs₃, hθ₃, M₃, hM₃m, hM₃0, hM₃os, hM₃ae⟩ :=
    planarPartitionSizeScale_of_minimalScales hM5
  obtain ⟨A₀, sc, hcellae, hmoms⟩ := hM5
  obtain ⟨ε, hε, t, ht, hMK⟩ := planar_meyers_rh_uniform A₀
  have hq : 1 < 1 + ε / 2 := by linarith
  obtain ⟨K₁, r₁, θ₁, hK₁, hr₁, hθ₁, M₁, hM₁m, hM₁0, hM₁os, hM₁ae⟩ :=
    hmoms t ht (1 / 2) (by norm_num)
  obtain ⟨CM, hCM, hMey⟩ := hMK K₁ hK₁
  have hpq := Real.HolderConjugate.conjExponent hq
  have hτ : 0 < 3 * Real.conjExponent (1 + ε / 2) := by have := hpq.symm.pos; positivity
  obtain ⟨Kr, r₂, θ₂, hKr, hr₂, hθ₂, M₂, hM₂m, hM₂0, hM₂os, hM₂ae⟩ :=
    hmoms (3 * Real.conjExponent (1 + ε / 2)) hτ (1 / 2) (by norm_num)
  have hθp : 0 < theta 2 p := Rigidity.Percolation.theta_pos_of_criticalProbability_lt 2 p hpc
  obtain ⟨s₄, θ₄, hs₄, hθ₄, hcube⟩ := exists_clusterCubeDensity_of_concentration (d := 2) le_rfl p
    (cluster_density_concentration 2 le_rfl p hpc hp1) 1
  obtain ⟨M₄, hM₄m, hM₄0, hM₄os, hM₄ae⟩ := hcube 0
  -- the minimal scale
  obtain ⟨θ₁₂, hθ₁₂, h12⟩ := exists_isOsBond_max hr₁ hr₂ hθ₁ hθ₂ hM₁m hM₂m hM₁os hM₂os
  obtain ⟨θ₃₄, hθ₃₄, h34⟩ := exists_isOsBond_max hs₃ hs₄ hθ₃ hθ₄ hM₃m hM₄m hM₃os hM₄os
  obtain ⟨θY, hθY, hY⟩ := exists_isOsBond_max (lt_min hr₁ hr₂) (lt_min hs₃ hs₄) hθ₁₂ hθ₃₄
    (hM₁m.max hM₂m) (hM₃m.max hM₄m) h12 h34
  have hrY : 0 < min (min r₁ r₂) (min s₃ s₄) := lt_min (lt_min hr₁ hr₂) (lt_min hs₃ hs₄)
  have hYm : Measurable fun ω => max (max (M₁ ω) (M₂ ω)) (max (M₃ ω) (M₄ ω)) :=
    (hM₁m.max hM₂m).max (hM₃m.max hM₄m)
  have hY1 := IsOsBond.max hrY hθY (by positivity) hYm measurable_const hY
    (isOsBond_const (p := p) (d := 2) (by norm_num : (0 : ℝ) < 1) hrY)
  have hY3 := IsOsBond.const_mul (by norm_num : (0 : ℝ) < 3) hY1
  have hY3m : Measurable fun ω => 3 * max (max (max (M₁ ω) (M₂ ω)) (max (M₃ ω) (M₄ ω))) 1 :=
    (hYm.max measurable_const).const_mul 3
  obtain ⟨θX, hθX, hXos⟩ := exists_isOsBond_max hs₀ hrY hθ₀ (by positivity) hX₀m hY3m hX₀os hY3
  -- the constant
  have hκ : 0 < theta 2 p / 2 := by positivity
  have hκ' : 0 < theta 2 p / 2 / 9 := by positivity
  obtain ⟨K₁', hK₁'def⟩ : ∃ K : ℝ, K = 128 / 81 * (4 * planarCoarseConst) ^ 2 *
      (CM ^ (1 / (1 + ε / 2)) * Kr ^ (1 / Real.conjExponent (1 + ε / 2))) := ⟨_, rfl⟩
  have hK₁'0 : 0 ≤ K₁' := by rw [hK₁'def]; positivity
  refine ⟨_, θX, 27 * Real.sqrt (2 * K₁' + 6 * (K₁' + K₂ ^ 2 + 1) / (theta 2 p / 2 / 9)),
    lt_min hs₀ hrY, hθX, by positivity, _, hX₀m.max hY3m,
    fun ω => (hX₀0 ω).trans (le_max_left _ _), hXos, ?_⟩
  filter_upwards [hcellae, hM₁ae, hM₂ae, hM₃ae, hM₄ae, hX₀ae, ae_planarPartitionEvent hpc] with
    ω hcells hω₁ hω₂ hω₃ hω₄ hω₀ hP h R u hu j hj hjR a
  obtain ⟨hcell, hnb, hrh⟩ := hcells
  have hinf := uniqueInfiniteComponent_infinite h
  have hjX₀ : X₀ ω ≤ 3 ^ j := (le_max_left _ _).trans hj
  have hjY : 3 * max (max (max (M₁ ω) (M₂ ω)) (max (M₃ ω) (M₄ ω))) 1 ≤ 3 ^ j :=
    (le_max_right _ _).trans hj
  have hj1 : 1 ≤ j := by
    have h31 : (3 : ℝ) ^ 1 ≤ 3 ^ j := by
      have := le_max_right (max (max (M₁ ω) (M₂ ω)) (max (M₃ ω) (M₄ ω))) 1
      rw [pow_one]; linarith
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 h31
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hiY : max (max (M₁ ω) (M₂ ω)) (max (M₃ ω) (M₄ ω)) ≤ 3 ^ i := by
    rw [pow_succ] at hjY
    have := le_max_left (max (max (M₁ ω) (M₂ ω)) (max (M₃ ω) (M₄ ω))) 1
    linarith
  have hle : ∀ m, i ≤ m → (3 : ℝ) ^ i ≤ 3 ^ m := fun m hm => pow_le_pow_right₀ (by norm_num) hm
  have hi1 : M₁ ω ≤ 3 ^ i := ((le_max_left _ _).trans (le_max_left _ _)).trans hiY
  have hi2 : M₂ ω ≤ 3 ^ i := ((le_max_right _ _).trans (le_max_left _ _)).trans hiY
  have hi3 : M₃ ω ≤ 3 ^ i := ((le_max_left _ _).trans (le_max_right _ _)).trans hiY
  have hi4 : M₄ ω ≤ 3 ^ i := ((le_max_right _ _).trans (le_max_right _ _)).trans hiY
  have hres : ∀ m, i ≤ m → PlanarResolved ω ⟨m, 0⟩ := by
    intro m hm z hz
    have hz' : z ∈ triadicCubeFinset 2 m 0 := mem_square_iff_int.2 (mem_triadicCube_zero_iff.1 hz)
    have := hω₃ m (hi3.trans (hle m hm)) z hz'
    show (planarPartCube ω z).scale ≤ m
    omega
  have hsub : ∀ m, i ≤ m → ∀ x ∈ clusterVertices ω ⟨m, 0⟩,
      x ∈ (uniqueInfiniteComponent h).supp := by
    intro m hm x hx
    obtain ⟨x₀, hx₀⟩ := exists_mem_square_of_clusterCubeDensity (uniqueInfiniteComponent h) hκ
      (hω₄ h) (hi4.trans (hle m hm))
    exact mem_supp_of_mem_clusterVertices hP (hres m hm) _ hinf
      (mem_triadicCube_zero_iff.2 (mem_square_iff_int.1 hx₀)) x₀.2 hx
  have hsucc : ∀ m, i ≤ m → ∀ x ∈ triadicCubeFinset 2 m 0, x ∈ (uniqueInfiniteComponent h).supp →
      x ∈ clusterVertices ω ⟨m + 1, 0⟩ := fun m hm x hx hxC =>
    mem_clusterVertices_succ hP _ hinf (hω₃ m (hi3.trans (hle m hm))) hx hxC
  have hincl : ∀ m n, i ≤ m → m < n → clusterVertices ω ⟨m, 0⟩ ⊆ clusterVertices ω ⟨n, 0⟩ := by
    intro m n hm hmn x hx
    have hxC := hsub m hm x hx
    have hx1 : x ∈ triadicCubeFinset 2 (n - 1) 0 := by
      have := mem_square_of_mem_clusterVertices hx
      rw [mem_square_iff_int] at this ⊢
      intro k
      have h := this k
      have h3 : (3 : ℤ) ^ m ≤ 3 ^ (n - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    have := hsucc (n - 1) (by omega) x hx1 hxC
    rwa [show n - 1 + 1 = n by omega] at this
  have hharm := harm_on_square_of_isHarmonicInBall hu hjR
  -- the Meyers estimate
  have hω₁' := hω₁ (i + 1 + 1) (hi1.trans (hle _ (by omega)))
  have hsize : ∀ z ∈ cube (i + 1 + 1) (0 : Vertex 2), sc ω z ≤ i + 1 + 1 := fun z hz => by
    have := two_mul_le_of_three_pow_le_rpow_half (hω₁'.2.1 z hz)
    omega
  have hMeyj := meyers_on_square hMey hP (uniqueInfiniteComponent h) u
    (hres (i + 1 + 2) (by omega)) (hsub (i + 1 + 2) (by omega)) hharm (sc ω) hcell hnb hrh hsize
    (hω₁ (i + 1) (hi1.trans (hle _ (by omega)))).1
  -- the moments of the pair reach scales
  have hω₂j := hω₂ (i + 1) (hi2.trans (hle _ (by omega)))
  have hfin : ∀ x ∈ cube (i + 1) (0 : Vertex 2), planarReach ω x ≠ ⊤ := fun x hx =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hω₂j.2.2.2.2.2 x hx)
  have hpair := sum_rpow_le_of_le_planarReach (j := i + 1)
    (fun z => (planarCoarseData hP ⟨i + 1, 0⟩ (hres (i + 1) (by omega))).pairReachScale z)
    (three_pow_pairReachScale_le_planarReach hP (hres (i + 1) (by omega))) hτ hKr hfin hω₂j.2.2.2.2.1
  have hpair' : ∑ z ∈ clusterVertices ω ⟨i + 1, 0⟩,
      (((3 : ℝ) ^ (planarCoarseData hP ⟨i + 1, 0⟩ (hres (i + 1) (by omega))).pairReachScale z) ^
        (3 : ℝ)) ^ Real.conjExponent (1 + ε / 2) ≤ Kr * 9 ^ (i + 1) := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun z _ => ?_)) hpair
    rw [← Real.rpow_mul (by positivity)]
  have hPo := sum_sq_coarse_sub_mean_le hP (uniqueInfiniteComponent h) u
    (hres (i + 1) (by omega)) (hincl _ _ (by omega) (by omega)) (hsub (i + 1 + 2) (by omega))
    (hsucc (i + 1 + 2) (by omega)) hharm hq hCM hKr hMeyj hpair' a
  rw [← hK₁'def] at hPo
  -- the comparison (7.8)
  have h74 := hω₀ h R u hu (i + 1) hjX₀ hjR
  have h74' := h74.trans (mul_le_mul_of_nonneg_left
    (clusterSquareOsc_le_clusterSquareL2 (uniqueInfiniteComponent h) u (i + 1 + 3) a)
    (by positivity))
  have hL := sum_sq_le_of_clusterSquareL2_le h74'
  -- the density of the cluster
  have hcard := card_clusterVertices_succ_ge (uniqueInfiniteComponent h) (hω₄ h) hi4
    (hsucc i le_rfl)
  exact squareL2_coarse_sub_le (uniqueInfiniteComponent h) u a _ hK₁'0 (sq_nonneg K₂) hκ' hPo hL
    (hincl _ _ (by omega) (by omega)) hcard

end Rigidity.Proofs.Regularity
