import Rigidity.Proofs.Green.DarioGuFluxTranslate
import Rigidity.Proofs.Green.DarioGuTwoScaleInitial

/-!
# Remark B.3 of Dario–Gu in dimension two

Remark B.3 of Dario–Gu (lines 3165-3186 of the source): for every `α > 0` and every radius
`r ≥ M_flux,α(y)`, `‖g̃*_{e_k}‖_{H̲^{-1}(𝒞_∞ ∩ B_r(y))} ≤ C r^α`, where `g̃*_{e_k}` is the translated
flux of (4.26). The source leaves the proof to the reader ("identical to the proof of
Proposition B.1"). Here it is deduced from Proposition 2.13 (`DarioGuFluxWeakNormTwo`) and the
quantitative corrector estimate (`CorrectorQuantitativeInputTwo`, which bounds the increments of
the corrector along the open edges of `B_{2r}(y)` by `C r^α`) through
`weakNormLe_translatedFlux`; the minimal radius is `max(M_flux,α(y), M_corr,α(y), 1)`.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Green

/-- **Dario–Gu, Remark B.3**, in dimension two, on the event `{y ∈ 𝒞_∞}`: the translated flux
`g̃*_{e_k}` of (4.26) satisfies `‖[g̃*_{e_k}]_i‖_{H̲^{-1}(𝒞_∞ ∩ B_r(y))} ≤ C r^α` for `r ≥ M(y)`,
`M(y) ≤ O_s(C)`. -/
def DarioGuTranslatedFluxTwo (p : unitInterval) (σ : ℝ) : Prop :=
  ∀ α : ℝ, 0 < α → ∃ C s : ℝ, 0 < C ∧ 0 < s ∧ ∀ y : Vertex 2,
    ∃ M : Configuration 2 → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond 2 p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        y ∈ (uniqueInfiniteComponent h).supp → ∀ χ : Fin 2 → Vertex 2 → ℝ,
          IsDGCorrector (uniqueInfiniteComponent h) y χ → ∀ r : ℝ, M ω ≤ r → ∀ k i : Fin 2,
            WeakNormLe ω (clusterBall (uniqueInfiniteComponent h) y r)
              (translatedFlux ω σ χ k i) (C * r ^ α)

/-- A lattice neighbour of a point of a component along an open edge lies in the component. -/
theorem mem_supp_of_openAdj {ω : Configuration 2} {K : OpenComponent ω} {x z : Vertex 2}
    (hx : x ∈ K.supp) (hadj : (openGraph ω).Adj x z) : z ∈ K.supp := by
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
  rw [← hx]
  exact SimpleGraph.ConnectedComponent.sound hadj.symm.reachable

/-- **Dario–Gu, Remark B.3** from Proposition 2.13 and the quantitative corrector estimate. -/
theorem darioGuTranslatedFluxTwo_of_inputs (hR5 : CorrectorQuantitativeInputTwo)
    {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) {σ : ℝ}
    (hflux : DarioGuFluxWeakNormTwo p σ) : DarioGuTranslatedFluxTwo p σ := by
  intro α hα
  obtain ⟨C₁, s₁, hC₁, hs₁, h1⟩ := hflux α hα
  obtain ⟨s₂, C₂, hs₂, hC₂, h2⟩ := hR5 p hpc hp1 α hα
  choose M₁ hM1m hM10 hM1os hM1ae using h1
  choose M₂ hM2m hM20 hM2os hM2ae using h2
  set s := min s₁ s₂ with hs
  have hs0 : 0 < s := lt_min hs₁ hs₂
  set θ1 := C₁ * (6 : ℝ) ^ (1 / s) with hθ1
  set θ2 := C₂ * (6 : ℝ) ^ (1 / s) with hθ2
  set θ3 := (1 : ℝ) * (3 : ℝ) ^ (1 / s) with hθ3
  set θM := max (max θ1 θ2 * (4 : ℝ) ^ (1 / s)) θ3 * (4 : ℝ) ^ (1 / s) with hθM
  set C := max θM (C₁ + 1 + C₂ * 2 ^ α) with hC
  have hθM0 : 0 < θM := by positivity
  have hC0 : 0 < C := lt_max_of_lt_left hθM0
  refine ⟨C, s, hC0, hs0, fun y => ?_⟩
  set M : Configuration 2 → ℝ := fun ω => max (max (M₁ y ω) (M₂ y ω)) 1 with hM
  have hMm : Measurable M := ((hM1m y).max (hM2m y)).max measurable_const
  have hos1 : IsOsBond 2 p (M₁ y) s θ1 :=
    Rigidity.Proofs.S2.IsOsBond.mono_exponent hs0 (min_le_left _ _) (hM1m y) (hM1os y)
  have hos2 : IsOsBond 2 p (M₂ y) s θ2 :=
    Rigidity.Proofs.S2.IsOsBond.mono_exponent hs0 (min_le_right _ _) (hM2m y) (hM2os y)
  have hos12 := Rigidity.Proofs.S2.IsOsBond.max hs0 (by positivity) (by positivity)
    (hM1m y) (hM2m y) hos1 hos2
  have hosM : IsOsBond 2 p M s θM :=
    Rigidity.Proofs.S2.IsOsBond.max hs0 (by positivity) (by positivity)
      ((hM1m y).max (hM2m y)) measurable_const hos12
      (Rigidity.Proofs.S2.isOsBond_const one_pos hs0)
  refine ⟨M, hMm, fun ω => le_max_of_le_right zero_le_one,
    Rigidity.Proofs.S2.IsOsBond.mono_scale hs0 hθM0 (le_max_left _ _) hMm hosM, ?_⟩
  filter_upwards [hM1ae y, hM2ae y] with ω hω1 hω2
  intro h hy χ hχ r hr k i
  set K := uniqueInfiniteComponent h with hK
  have hr1 : 1 ≤ r := (le_max_right _ _).trans hr
  have hrM1 : M₁ y ω ≤ r := (le_max_left _ _).trans ((le_max_left _ _).trans hr)
  have hrM2 : M₂ y ω ≤ 2 * r :=
    ((le_max_right _ _).trans ((le_max_left _ _).trans hr)).trans (by linarith)
  have hW := hω1 h hy χ hχ r hrM1 k i
  have hrα : 1 ≤ r ^ α := Real.one_le_rpow hr1 hα.le
  have h2r : (2 * r) ^ α = 2 ^ α * r ^ α := Real.mul_rpow (by norm_num) (by linarith)
  have hL0 : 0 ≤ 1 + C₂ * (2 * r) ^ α := by positivity
  have hA : ∀ x ∈ clusterBall K y r, |edgeFlux ω χ k i x| ≤ 1 + C₂ * (2 * r) ^ α := by
    intro x hx
    rw [mem_clusterBall] at hx
    by_cases hadj : (openGraph ω).Adj x (x + Pi.single i 1)
    · have hxe : x + Pi.single i 1 ∈ K.supp := mem_supp_of_openAdj hx.1 hadj
      have hd : latticeDist (x + Pi.single i 1) y < 2 * r := by
        have h1 := latticeDist_triangle (x + Pi.single i 1) x y
        have h2 : latticeDist x (x + Pi.single i 1) = 1 := by
          rw [latticeDist_comm]; exact latticeDist_add_single x i
        linarith [hx.2]
      have hd' : latticeDist x y < 2 * r := by linarith [hx.2]
      have key := hω2 h (Pi.single k 1) (fun a => (a.val k : ℝ) + χ k a.val) (hχ k).1 (2 * r)
        hrM2 ⟨x, hx.1⟩ ⟨x, hx.1⟩ ⟨x, hx.1⟩ ⟨x + Pi.single i 1, hxe⟩ hd' hd' hd' hd hadj
      simp only [Rigidity.Corrector.sum_single_mul, Rigidity.Corrector.sum_abs_single,
        mul_one, sub_self, abs_zero, zero_add] at key
      have key' : |χ k (x + Pi.single i 1) - χ k x| ≤ C₂ * (2 * r) ^ α := by
        refine le_trans (le_of_eq ?_) key
        rw [← abs_neg]
        congr 1
        ring
      rw [edgeFlux, if_pos hadj]
      calc |(if i = k then (1 : ℝ) else 0) + (χ k (x + Pi.single i 1) - χ k x)|
          ≤ |(if i = k then (1 : ℝ) else 0)| + |χ k (x + Pi.single i 1) - χ k x| := abs_add_le _ _
        _ ≤ 1 + C₂ * (2 * r) ^ α := by
            have : |(if i = k then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
            linarith [key']
    · rw [edgeFlux, if_neg hadj, abs_zero]
      exact hL0
  refine (weakNormLe_translatedFlux hW hA hL0).mono ?_
  have hθ : C₁ + 1 + C₂ * 2 ^ α ≤ C := le_max_right _ _
  have hr0 : 0 ≤ r ^ α := by positivity
  calc C₁ * r ^ α + (1 + C₂ * (2 * r) ^ α) ≤ (C₁ + 1 + C₂ * 2 ^ α) * r ^ α := by
        rw [h2r]; nlinarith
    _ ≤ C * r ^ α := mul_le_mul_of_nonneg_right hθ hr0

end Rigidity.Green
