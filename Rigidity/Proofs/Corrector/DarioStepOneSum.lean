import Rigidity.Proofs.Corrector.DarioStepOneBound
import Mathlib.MeasureTheory.Function.Floor

/-!
# The sum over bonds of Step 1 of Lemma 3.3 of Dario

Summing `flipTermOne_sq_le_of_bound` over the bonds and exchanging the sums gives Dario's (3.18) in
flip form: almost surely

`Σ_e T₁(e)² ≤ Σ_y Φ_{r²}(x, y)² W(y)`, `W(y) = Σ_e 1{y ∈ B(a_e, C₀ C s₁(e))} F_e`,

with `a_e = bondBase e`, `s₁(e)` the side of the partition cube of `ω^{e,1}` at `a_e`
(`flipSide`, measurable through the stopping size) and
`F_e = |B(a_e, C₀ C s₁)| (8 Σ_{z ∈ B(a_e, R₁)} Λ(z, ω^{e,1}))²` (`stepOneFactor`, `stepOneW`,
`ae_flipSumOne_le`). With `isOsBond_heatSqSum_of_moments`, Step 1 (`Σ_e T₁(e)² ≤ O_s(C/r²)`) then
reduces to uniform moments `E[W(y)^q] ≤ (A q^k)^q` (`flipSumOne_isOsBond_of_moments`).
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Poincare
open scoped Classical ENNReal

/-- The side of the partition cube of `ω^{e,1}` at the base of `e`, through the stopping size. -/
noncomputable def flipSide (e : Bond 2) (ω : Configuration 2) : ℕ :=
  ⌊TriadicCube.stoppingSize (planarGoodCubes (setBond e true ω)) (bondBase e)⌋₊

theorem measurable_flipSide (e : Bond 2) : Measurable (flipSide e) :=
  Nat.measurable_floor.comp
    ((measurable_stoppingSize_planar (bondBase e)).comp (measurable_setBond e true))

theorem flipSide_eq {e : Bond 2} {ω : Configuration 2}
    (hP : PlanarPartitionEvent (setBond e true ω)) :
    flipSide e ω = 3 ^ (planarPartCube (setBond e true ω) (bondBase e)).scale := by
  unfold flipSide
  rw [TriadicCube.stoppingSize_eq_of_mem (planarPartCube_spec hP _).1 (planarPartCube_spec hP _).2]
  rw [show (3 : ℝ) ^ (planarPartCube (setBond e true ω) (bondBase e)).scale =
    ((3 ^ (planarPartCube (setBond e true ω) (bondBase e)).scale : ℕ) : ℝ) by push_cast; rfl,
    Nat.floor_natCast]

/-- The local factor of Step 1 at the bond `e` seen from `y`, for the side `n`. -/
noncomputable def stepOneFactorAt (Λ : Vertex 2 → Configuration 2 → ℝ) (C₀ C : ℕ) (e : Bond 2)
    (y : Vertex 2) (n : ℕ) (ω : Configuration 2) : ℝ≥0∞ :=
  if y ∈ supBox (bondBase e) (C₀ * C * n) then
    ENNReal.ofReal ((supBox (bondBase e) (C₀ * C * n)).card *
      (8 * ∑ z ∈ supBox (bondBase e) ((C₀ * C * n + 1) + 5 * (C * (C * n))),
        Λ z (setBond e true ω)) ^ 2)
  else 0

/-- The local factor of Step 1 at the bond `e` seen from `y`. -/
noncomputable def stepOneFactor (Λ : Vertex 2 → Configuration 2 → ℝ) (C₀ C : ℕ) (e : Bond 2)
    (y : Vertex 2) (ω : Configuration 2) : ℝ≥0∞ :=
  stepOneFactorAt Λ C₀ C e y (flipSide e ω) ω

/-- Dario's sum (3.18): `W(y) = Σ_e 1{y ∈ B_e} F_e`. -/
noncomputable def stepOneW (Λ : Vertex 2 → Configuration 2 → ℝ) (C₀ C : ℕ) (y : Vertex 2)
    (ω : Configuration 2) : ℝ≥0∞ :=
  ∑' e, stepOneFactor Λ C₀ C e y ω

theorem measurable_stepOneFactor {Λ : Vertex 2 → Configuration 2 → ℝ}
    (hΛm : ∀ z, Measurable (Λ z)) (C₀ C : ℕ) (e : Bond 2) (y : Vertex 2) :
    Measurable (stepOneFactor Λ C₀ C e y) := by
  have hF : ∀ n, Measurable (stepOneFactorAt Λ C₀ C e y n) := fun n => by
    by_cases hc : y ∈ supBox (bondBase e) (C₀ * C * n)
    · unfold stepOneFactorAt
      simp only [if_pos hc]
      exact ENNReal.measurable_ofReal.comp (measurable_const.mul (((Finset.measurable_sum _
        fun z _ => (hΛm z).comp (measurable_setBond e true)).const_mul 8).pow_const 2))
    · unfold stepOneFactorAt
      simp only [if_neg hc]
      exact measurable_const
  have h : Measurable fun x : Configuration 2 × ℕ => stepOneFactorAt Λ C₀ C e y x.2 x.1 :=
    measurable_from_prod_countable_left fun n => hF n
  have e' : stepOneFactor Λ C₀ C e y =
      (fun x : Configuration 2 × ℕ => stepOneFactorAt Λ C₀ C e y x.2 x.1) ∘
        (fun ω => (ω, flipSide e ω)) := rfl
  rw [e']
  exact h.comp (measurable_id.prodMk (measurable_flipSide e))

theorem measurable_stepOneW {Λ : Vertex 2 → Configuration 2 → ℝ} (hΛm : ∀ z, Measurable (Λ z))
    (C₀ C : ℕ) (y : Vertex 2) : Measurable (stepOneW Λ C₀ C y) :=
  Measurable.tsum fun e => measurable_stepOneFactor hΛm C₀ C e y

/-- A product of a finite square sum with a constant, as a sum over all points. -/
theorem ofReal_card_mul_sum_sq_mul_eq (B : Finset (Vertex 2)) (φ : Vertex 2 → ℝ) (K : ℝ) :
    ENNReal.ofReal (B.card * (∑ y ∈ B, φ y ^ 2) * K) =
      ∑' y, ENNReal.ofReal (φ y ^ 2) *
        (if y ∈ B then ENNReal.ofReal (B.card * K) else 0) := by
  rw [tsum_eq_sum (s := B) fun y hy => by rw [if_neg hy, mul_zero]]
  have hB : ∀ y ∈ B, ENNReal.ofReal (φ y ^ 2) *
      (if y ∈ B then ENNReal.ofReal (B.card * K) else 0) =
        ENNReal.ofReal (φ y ^ 2) * ENNReal.ofReal (B.card * K) := fun y hy => by rw [if_pos hy]
  rw [Finset.sum_congr rfl hB, ← Finset.sum_mul,
    ← ENNReal.ofReal_sum_of_nonneg (f := fun y => φ y ^ 2) (s := B) fun _ _ => sq_nonneg _,
    ← ENNReal.ofReal_mul (p := ∑ y ∈ B, φ y ^ 2) (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  congr 1
  ring

section Sum

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- **Dario's (3.18) in flip form**: almost surely, `Σ_e T₁(e)² ≤ Σ_y Φ_{r²}(x, y)² W(y)`, for
Lipschitz bounds `Λ` of the corrector holding almost surely. -/
theorem ae_flipSumOne_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) {C₀ C : ℕ} (hC₀ : 0 < C₀)
    (hres : ResamplePartitionBound C₀ C) {i : Fin 2} {Λ : Vertex 2 → Configuration 2 → ℝ}
    (hΛ0 : ∀ z ω, 0 ≤ Λ z ω)
    (hlip : ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ z, ω ∈ infiniteComponentEvent z → ∀ y,
      (openGraph ω).Adj z y → |correctorDiff hG hGv (Pi.single i 1) ω z y| ≤ Λ z ω) :
    ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ (j : Fin 2) (r : ℝ) (x : Vertex 2),
      flipSumOne hG hGv i j r x ω ≤
        ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) * stepOneW Λ C₀ C y ω := by
  have hp0 : 0 < (p : ℝ) := (criticalProbability_nonneg 2).trans_lt hpc
  filter_upwards [ae_setBond hp0 hp1 hGae, ae_setBond hp0 hp1 (ae_planarPartitionEvent hpc),
    ae_setBond hp0 hp1 hlip] with ω hG' hP' hl j r x
  unfold flipSumOne stepOneW
  calc ∑' e, ENNReal.ofReal (flipTermOne hG hGv i j r x e ω ^ 2)
      ≤ ∑' e, ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) *
          stepOneFactor Λ C₀ C e y ω := ENNReal.tsum_le_tsum fun e => by
        have h := flipTermOne_sq_le_of_bound hG hGv hC₀ hres (hG' e true) (hP' e true)
          (hP' e false) (Λ := fun z => Λ z (setBond e true ω)) (fun z => hΛ0 z _) (hl e true)
          j r x
        refine (ENNReal.ofReal_le_ofReal h).trans (le_of_eq ?_)
        rw [ofReal_card_mul_sum_sq_mul_eq]
        refine tsum_congr fun y => ?_
        simp only [stepOneFactor, stepOneFactorAt, flipSide_eq (hP' e true)]
    _ = ∑' y, ∑' e, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) * stepOneFactor Λ C₀ C e y ω :=
        ENNReal.tsum_comm
    _ = ∑' y, ENNReal.ofReal (latticeHeat (r ^ 2) x y ^ 2) * ∑' e, stepOneFactor Λ C₀ C e y ω :=
        tsum_congr fun y => ENNReal.tsum_mul_left

/-- **Step 1 of Lemma 3.3 from the moments of `W`**: given Lemma 3.5 and almost sure Lipschitz
bounds `Λ` of the corrector, uniform moments `E[W(y)^q] ≤ (A q^k)^q` give `s, C' > 0` with
`Σ_e T₁(e)²` almost surely finite and `≤ O_s(C'/r²)` for all `j`, `r ≥ 1` and `x`. -/
theorem flipSumOne_isOsBond_of_moments {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) {C₀ C : ℕ} (hC₀ : 0 < C₀)
    (hres : ResamplePartitionBound C₀ C) {i : Fin 2} {Λ : Vertex 2 → Configuration 2 → ℝ}
    (hΛm : ∀ z, Measurable (Λ z)) (hΛ0 : ∀ z ω, 0 ≤ Λ z ω)
    (hlip : ∀ᵐ ω ∂latticeBondLaw 2 p, ∀ z, ω ∈ infiniteComponentEvent z → ∀ y,
      (openGraph ω).Adj z y → |correctorDiff hG hGv (Pi.single i 1) ω z y| ≤ Λ z ω)
    {A k : ℝ} (hA : 0 < A) (hk : 0 < k)
    (hmom : ∀ y (q : ℝ), 1 ≤ q →
      ∫⁻ ω, stepOneW Λ C₀ C y ω ^ q ∂latticeBondLaw 2 p ≤ ENNReal.ofReal ((A * q ^ k) ^ q)) :
    ∃ s C' : ℝ, 0 < s ∧ 0 < C' ∧ ∀ (j : Fin 2) (r : ℝ), 1 ≤ r → ∀ x : Vertex 2,
      (∀ᵐ ω ∂latticeBondLaw 2 p, flipSumOne hG hGv i j r x ω < ∞) ∧
      IsOsBond 2 p (fun ω => (flipSumOne hG hGv i j r x ω).toReal) s (C' / r ^ 2) := by
  obtain ⟨s, C', hs, hC', h⟩ := isOsBond_heatSqSum_of_moments (p := p) hA hk
  have hle := ae_flipSumOne_le hG hGv hpc hp1 hGae hC₀ hres hΛ0 hlip
  refine ⟨s, C', hs, hC', fun j r hr x => ?_⟩
  refine h r hr x (stepOneW Λ C₀ C) (fun y => measurable_stepOneW hΛm C₀ C y) hmom _
    (measurable_flipSumOne hG hGv i j r x) ?_
  filter_upwards [hle] with ω hω
  exact hω j r x

end Sum

end Rigidity.Corrector
