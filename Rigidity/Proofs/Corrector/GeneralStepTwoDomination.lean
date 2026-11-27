import Rigidity.Proofs.Corrector.DarioStepTwoDomination
import Rigidity.Proofs.Corrector.GeneralStepTwoFiniteProb

/-!
# The domination of the weight by the finite-range weight on `ℤᵈ`

A vertex `u` is good for the domination at range `R` (`DomGood`) when the partition into good cubes
exists, the configuration lies in the event `G` of the corrector, no far edge reaches `u`, the
capped sides are the sides near `u`, the same two events hold for the sides of the configurations
with the bond of an edge closed (`FarGoodFlip`, `SideGoodFlip`), and the local gradient bounds
dominate the plane gradient bound near `u`. Then the weight of the Step 2 sum at `u` is at most the
finite-range weight, and on a triadic cube all of whose vertices are good the weight bound of the
cube follows from the same bound for the finite-range weight (`weightGood_of_domGood`). For `d ≥ 3`
a vertex fails to be good with probability at most `C R^{2d} e^{-c R^σ}`, `σ = min(1/d, δs) ≤ 1`
(`measure_not_domGood_le`), collecting the five failure probabilities of
`GeneralStepTwoFiniteProb` (those of the closed-bond sides carry the factor `d/(1-p)`), which are
brought to this common form by real bounds:

* the far-edge term `K e^{-R/A}` (`far_term_le`), for `c ≤ 1/A` and `σ ≤ 1`;
* the capped-side term `(2R + 1)^d C e^{-c_s 3ⁿ}` for `R < 3 · 3ⁿ` (`side_term_le`), for
  `c ≤ c_s/3` and `σ ≤ 1`;
* the local-gradient term, a union over the `(2(R + 3κR) + 1)^d` points of a box of the finite
  cluster tail `(2R + 1)^d C₁ e^{-c₁ (R+1)^τ}` and the sublinearity tail
  `2 e^{-(R / (C₂ (LR)^{1-δ}))^s}` (`grad_term_le`, with `grad_exponent_eq`), for `σ ≤ τ`,
  `σ ≤ δs`, `c ≤ c₁` and `c ≤ (L^{δ-1}/C₂)^s`.

This ports the planar file `DarioStepTwoDomination`, with the partition into good cubes of `ℤᵈ`
in place of the planar partition. In the planar file `d = 2`, the far-edge constants are
`K = 8 (1 + 2 · 2 · 6κθ)²`, `A = 2 · 6κθ`, the counts `(2R + 1)²` give the power `R⁴`, the finite
cluster tail is `e^{-c₁ √(R+1)}` (`τ = 1/2`), the Euclidean radius of the box `B(0, R)` is `3R`
(`L = 3`) and `σ ≤ 1/2`. On `ℤᵈ` the far-edge constants are `K = 2 (2 (1 + d · 2 · 3dκθ))ᵈ`,
`A = 2 · 3dκθ`; in `d ≥ 3` the finite cluster tail is `e^{-c₁ (R+1)^{1/d}}` (`τ = 1/d`) and the
Euclidean radius is `2dR` (`L = 2d`); the box radius `R + 3κR` of the local-gradient term is that
of an `ℓ^∞` box and does not depend on `d`.
-/

namespace Rigidity.Corrector.GeneralDim

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped Classical ENNReal

variable {d : ℕ}

theorem grad_exponent_eq {R L C₂ δ s : ℝ} (hR : 0 < R) (hL : 0 < L) (hC₂ : 0 < C₂) :
    (R / (C₂ * (L * R) ^ (1 - δ))) ^ s = (L ^ (δ - 1) / C₂) ^ s * R ^ (δ * s) := by
  have h1 : (L * R) ^ (1 - δ) = L ^ (1 - δ) * R ^ (1 - δ) := Real.mul_rpow hL.le hR.le
  have hRδ : 0 < R ^ δ := Real.rpow_pos_of_pos hR δ
  have hLδ : 0 < L ^ δ := Real.rpow_pos_of_pos hL δ
  have h2 : R / (C₂ * (L * R) ^ (1 - δ)) = (L ^ (δ - 1) / C₂) * R ^ δ := by
    rw [h1, Real.rpow_sub hR, Real.rpow_sub hL, Real.rpow_sub hL, Real.rpow_one, Real.rpow_one]
    field_simp
  rw [h2, Real.mul_rpow (by positivity) hRδ.le, ← Real.rpow_mul hR.le]

/-- The far-edge term in the form `K x^a e^{-c x^σ}`. -/
theorem far_term_le {x A K c σ : ℝ} {a : ℕ} (hK : 0 ≤ K) (hx : 1 ≤ x) (hσ1 : σ ≤ 1)
    (hc0 : 0 ≤ c) (hcA : c ≤ 1 / A) :
    K * Real.exp (-(x / A)) ≤ K * x ^ a * Real.exp (-(c * x ^ σ)) := by
  have e : x / A = 1 / A * x := by ring
  rw [e]
  have h := Rigidity.Corrector.exp_neg_le_exp_neg_rpow hx hσ1 hc0 hcA
  have hxa : (1 : ℝ) ≤ x ^ a := one_le_pow₀ hx
  have hE0 : 0 ≤ Real.exp (-(c * x ^ σ)) := (Real.exp_pos _).le
  calc K * Real.exp (-(1 / A * x)) ≤ K * Real.exp (-(c * x ^ σ)) :=
        mul_le_mul_of_nonneg_left h hK
    _ ≤ K * (x ^ a * Real.exp (-(c * x ^ σ))) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hE0 hxa) hK
    _ = _ := by ring

/-- The capped-side term in the form `C x^{2d} e^{-c x^σ}`. -/
theorem side_term_le {d R n : ℕ} (hR : 1 ≤ R) (hn : R < 3 * 3 ^ n) {cs c σ C : ℝ} (hcs : 0 < cs)
    (hσ1 : σ ≤ 1) (hc0 : 0 ≤ c) (hccs : c ≤ cs / 3) (hC : 0 ≤ C) :
    ((((2 * R + 1) ^ d : ℕ) : ℝ)) * (C * Real.exp (-cs * (3 : ℝ) ^ n)) ≤
      3 ^ d * C * (R : ℝ) ^ (2 * d) * Real.exp (-(c * (R : ℝ) ^ σ)) := by
  have hx1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have h3 : (R : ℝ) / 3 ≤ (3 : ℝ) ^ n := by
    have : (R : ℝ) < 3 * 3 ^ n := by exact_mod_cast hn
    linarith
  have hexp : Real.exp (-cs * (3 : ℝ) ^ n) ≤ Real.exp (-(cs / 3 * R)) := by
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left h3 hcs.le
    have e : cs * (R / 3) = cs / 3 * R := by ring
    linarith
  have h2 := Rigidity.Corrector.exp_neg_le_exp_neg_rpow (a := cs / 3) hx1 hσ1 hc0 hccs
  have hN : ((((2 * R + 1) ^ d : ℕ) : ℝ)) ≤ 3 ^ d * (R : ℝ) ^ (2 * d) := by
    push_cast
    have hb : (2 * (R : ℝ) + 1) ^ d ≤ (3 * (R : ℝ)) ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith) d
    have hp : (R : ℝ) ^ d ≤ (R : ℝ) ^ (2 * d) := pow_le_pow_right₀ hx1 (by omega)
    calc (2 * (R : ℝ) + 1) ^ d ≤ (3 * (R : ℝ)) ^ d := hb
      _ = 3 ^ d * (R : ℝ) ^ d := mul_pow _ _ _
      _ ≤ 3 ^ d * (R : ℝ) ^ (2 * d) := mul_le_mul_of_nonneg_left hp (by positivity)
  calc ((((2 * R + 1) ^ d : ℕ) : ℝ)) * (C * Real.exp (-cs * (3 : ℝ) ^ n))
      ≤ 3 ^ d * (R : ℝ) ^ (2 * d) * (C * Real.exp (-(c * (R : ℝ) ^ σ))) :=
        mul_le_mul hN (mul_le_mul_of_nonneg_left (hexp.trans h2) hC) (by positivity)
          (by positivity)
    _ = _ := by ring

/-- The local-gradient term in the form `C x^{2d} e^{-c x^σ}`. -/
theorem grad_term_le {d R κ : ℕ} (hR : 1 ≤ R) {C₁ c₁ τ s δ L C₂ c σ : ℝ} (hC₁ : 0 ≤ C₁)
    (hL : 0 < L) (hC₂ : 0 < C₂) (hτ : 0 ≤ τ) (hστ : σ ≤ τ) (hσδ : σ ≤ δ * s) (hc0 : 0 ≤ c)
    (hcc₁ : c ≤ c₁) (hcc₃ : c ≤ (L ^ (δ - 1) / C₂) ^ s) :
    ((((2 * (R + 3 * κ * R) + 1) ^ d : ℕ) : ℝ)) *
      ((2 * (R : ℝ) + 1) ^ d * (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ τ))) +
        2 * Real.exp (-((R : ℝ) / (C₂ * (L * R) ^ (1 - δ))) ^ s)) ≤
      3 ^ d * (1 + 3 * κ) ^ d * (3 ^ d * C₁ + 2) * (R : ℝ) ^ (2 * d) *
        Real.exp (-(c * (R : ℝ) ^ σ)) := by
  have hx1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hx0 : (0 : ℝ) < R := by linarith
  set E : ℝ := Real.exp (-(c * (R : ℝ) ^ σ))
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hN : ((((2 * (R + 3 * κ * R) + 1) ^ d : ℕ) : ℝ)) ≤
      3 ^ d * (1 + 3 * κ) ^ d * (R : ℝ) ^ d := by
    push_cast
    have h1 : (1 : ℝ) ≤ (1 + 3 * κ) * R := by nlinarith
    have h2 : 2 * ((R : ℝ) + 3 * κ * R) + 1 ≤ 3 * ((1 + 3 * κ) * R) := by nlinarith
    have h0 : (0 : ℝ) ≤ 2 * ((R : ℝ) + 3 * κ * R) + 1 := by positivity
    calc (2 * ((R : ℝ) + 3 * κ * R) + 1) ^ d ≤ (3 * ((1 + 3 * κ) * R)) ^ d :=
          pow_le_pow_left₀ h0 h2 d
      _ = 3 ^ d * (1 + 3 * κ) ^ d * (R : ℝ) ^ d := by rw [mul_pow, mul_pow]; ring
  have hsq : (R : ℝ) ^ σ ≤ ((R : ℝ) + 1) ^ τ :=
    calc (R : ℝ) ^ σ ≤ (R : ℝ) ^ τ := Real.rpow_le_rpow_of_exponent_le hx1 hστ
      _ ≤ ((R : ℝ) + 1) ^ τ := Real.rpow_le_rpow hx0.le (by linarith) hτ
  have hE1 : Real.exp (-(c₁ * ((R : ℝ) + 1) ^ τ)) ≤ E := by
    refine Real.exp_le_exp.2 ?_
    have h0 : 0 ≤ (R : ℝ) ^ σ := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hcc₁ h0,
      mul_le_mul_of_nonneg_left hsq (hc0.trans hcc₁)]
  have hE2 : Real.exp (-((R : ℝ) / (C₂ * (L * R) ^ (1 - δ))) ^ s) ≤ E := by
    rw [grad_exponent_eq hx0 hL hC₂]
    exact Rigidity.Corrector.exp_neg_rpow_le_exp_neg_rpow hx1 hσδ hc0 hcc₃
  have hM : (2 * (R : ℝ) + 1) ^ d ≤ 3 ^ d * (R : ℝ) ^ d :=
    calc (2 * (R : ℝ) + 1) ^ d ≤ (3 * (R : ℝ)) ^ d :=
          pow_le_pow_left₀ (by positivity) (by linarith) d
      _ = 3 ^ d * (R : ℝ) ^ d := mul_pow _ _ _
  have hRd : (1 : ℝ) ≤ (R : ℝ) ^ d := one_le_pow₀ hx1
  have hY : (2 * (R : ℝ) + 1) ^ d * (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ τ))) +
      2 * Real.exp (-((R : ℝ) / (C₂ * (L * R) ^ (1 - δ))) ^ s) ≤
      (3 ^ d * C₁ + 2) * (R : ℝ) ^ d * E := by
    calc (2 * (R : ℝ) + 1) ^ d * (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ τ))) +
          2 * Real.exp (-((R : ℝ) / (C₂ * (L * R) ^ (1 - δ))) ^ s)
        ≤ 3 ^ d * (R : ℝ) ^ d * (C₁ * E) + 2 * ((R : ℝ) ^ d * E) := by
          gcongr
          exact hE2.trans (le_mul_of_one_le_left hE0 hRd)
      _ = (3 ^ d * C₁ + 2) * (R : ℝ) ^ d * E := by ring
  have hY0 : 0 ≤ (2 * (R : ℝ) + 1) ^ d * (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ τ))) +
      2 * Real.exp (-((R : ℝ) / (C₂ * (L * R) ^ (1 - δ))) ^ s) := by positivity
  calc ((((2 * (R + 3 * κ * R) + 1) ^ d : ℕ) : ℝ)) *
        ((2 * (R : ℝ) + 1) ^ d * (C₁ * Real.exp (-(c₁ * ((R : ℝ) + 1) ^ τ))) +
          2 * Real.exp (-((R : ℝ) / (C₂ * (L * R) ^ (1 - δ))) ^ s))
      ≤ 3 ^ d * (1 + 3 * κ) ^ d * (R : ℝ) ^ d * ((3 ^ d * C₁ + 2) * (R : ℝ) ^ d * E) :=
        mul_le_mul hN hY hY0 (by positivity)
    _ = _ := by ring

section Grad

variable {G : Set (Configuration d)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent d)

/-- The vertex `u` is good for the domination of the weight at range `R`. -/
def DomGood (κ R : ℕ) (i : Fin d) (ω : Configuration d) (u : Vertex d) : Prop :=
  PartitionEvent ω ∧ ω ∈ G ∧ FarGood κ R ω u ∧ SideGood R ω u ∧ FarGoodFlip edgeBond κ R ω u ∧
    SideGoodFlip edgeBond R ω u ∧ GradGood hG hGv κ R i ω u

/-- **The weight bound of a cube from the finite-range weight.** -/
theorem weightGood_of_domGood {κ R : ℕ} (hR : 1 ≤ R) {i : Fin d} {q M : ℝ} (hq : 0 ≤ q)
    {ω : Configuration d} {T : TriadicCube d}
    (hdom : ∀ u ∈ T.toIntegerCube.vertices, DomGood hG hGv κ R i ω u)
    (hsum : ∑ u ∈ T.toIntegerCube.vertices, finiteWeight κ R ω u ^ q ≤
      M * T.toIntegerCube.vertices.card) :
    weightGood hG hGv κ i q M ω T := by
  have hle : ∀ u ∈ T.toIntegerCube.vertices,
      stepTwoWeight hG hGv κ i ω u ≤ ENNReal.ofReal (finiteWeight κ R ω u) := fun u hu => by
    obtain ⟨hP, -, hfar, hside, hfarF, hsideF, hgrad⟩ := hdom u hu
    exact stepTwoWeight_le_finiteWeight hG hGv hP hR hfar hfarF hside hsideF hgrad
  refine ⟨fun u hu => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle u hu), le_trans ?_ hsum⟩
  refine Finset.sum_le_sum fun u hu => Real.rpow_le_rpow ENNReal.toReal_nonneg ?_ hq
  exact ENNReal.toReal_le_of_le_ofReal (finiteWeight_nonneg hR ω u) (hle u hu)

/-- The failure of the domination splits into the five failure events. -/
theorem measure_not_domGood_le_add {p : unitInterval}
    (hP0 : latticeBondLaw d p {ω | ¬ PartitionEvent ω} = 0)
    (hG0 : latticeBondLaw d p Gᶜ = 0) (κ R : ℕ) (i : Fin d) (u : Vertex d) :
    latticeBondLaw d p {ω | ¬ DomGood hG hGv κ R i ω u} ≤
      latticeBondLaw d p {ω | PartitionEvent ω ∧ ¬ FarGood κ R ω u} +
        (latticeBondLaw d p {ω | PartitionEvent ω ∧ ¬ SideGood R ω u} +
          (latticeBondLaw d p {ω | ¬ FarGoodFlip edgeBond κ R ω u} +
            (latticeBondLaw d p {ω | ¬ SideGoodFlip edgeBond R ω u} +
              latticeBondLaw d p {ω | ω ∈ G ∧ ¬ GradGood hG hGv κ R i ω u}))) := by
  have hsub : {ω | ¬ DomGood hG hGv κ R i ω u} ⊆ ({ω | ¬ PartitionEvent ω} ∪ Gᶜ) ∪
      ({ω | PartitionEvent ω ∧ ¬ FarGood κ R ω u} ∪
        ({ω | PartitionEvent ω ∧ ¬ SideGood R ω u} ∪
          ({ω | ¬ FarGoodFlip edgeBond κ R ω u} ∪
            ({ω | ¬ SideGoodFlip edgeBond R ω u} ∪
              {ω | ω ∈ G ∧ ¬ GradGood hG hGv κ R i ω u})))) := by
    intro ω hω
    by_cases hP : PartitionEvent ω
    · by_cases hGω : ω ∈ G
      · by_cases hF : FarGood κ R ω u
        · by_cases hS : SideGood R ω u
          · by_cases hFF : FarGoodFlip edgeBond κ R ω u
            · by_cases hSF : SideGoodFlip edgeBond R ω u
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                  ⟨hGω, fun hg => hω ⟨hP, hGω, hF, hS, hFF, hSF, hg⟩⟩))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hSF))))
            · exact Or.inr (Or.inr (Or.inr (Or.inl hFF)))
          · exact Or.inr (Or.inr (Or.inl ⟨hP, hS⟩))
        · exact Or.inr (Or.inl ⟨hP, hF⟩)
      · exact Or.inl (Or.inr hGω)
    · exact Or.inl (Or.inl hP)
  have hN := measure_union_null hP0 hG0
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hN, zero_add]
  exact (measure_union_le _ _).trans (add_le_add le_rfl ((measure_union_le _ _).trans
    (add_le_add le_rfl ((measure_union_le _ _).trans
      (add_le_add le_rfl (measure_union_le _ _))))))

/-- **A vertex is good for the domination, with high probability** (`d ≥ 3`). -/
theorem measure_not_domGood_le [NeZero d] (hd : 3 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hGae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ G) {κ : ℕ} (hκ : 1 ≤ κ) :
    ∃ C c σ : ℝ, 0 < C ∧ 0 < c ∧ 0 < σ ∧ σ ≤ 1 ∧ ∀ (i : Fin d) (R : ℕ), 1 ≤ R →
      ∀ u : Vertex d, latticeBondLaw d p {ω | ¬ DomGood hG hGv κ R i ω u} ≤
        ENNReal.ofReal (C * (R : ℝ) ^ (2 * d) * Real.exp (-(c * (R : ℝ) ^ σ))) := by
  obtain ⟨θ, hθ, hfar⟩ := measure_not_farGood_le (by omega : 2 ≤ d) hpc
  obtain ⟨Cs, hCs, cs, hcs, hside⟩ := measure_not_sideGood_le (by omega : 2 ≤ d) hpc
  obtain ⟨θF, hθF, hfarF⟩ := measure_not_farGoodFlip_le (by omega : 2 ≤ d) hpc hp1
  obtain ⟨CF, hCF, cF, hcF, hsideF⟩ := measure_not_sideGoodFlip_le (by omega : 2 ≤ d) hpc hp1
  obtain ⟨C₁, c₁, s, δ, C₂, hC₁, hc₁, hs, hδ, hC₂, hgrad⟩ :=
    measure_not_gradGood_le hG hGv hd hpc hp1 hGae
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hL : (0 : ℝ) < 2 * (d : ℝ) := by positivity
  have hτ : (0 : ℝ) ≤ (d : ℝ)⁻¹ := by positivity
  have hκ0 : (0 : ℝ) < κ := by exact_mod_cast hκ
  have hp1' : (0 : ℝ) < 1 - p := by linarith
  have hdp : (0 : ℝ) ≤ d / (1 - p) := by positivity
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = min (d : ℝ)⁻¹ (δ * s) := ⟨_, rfl⟩
  have hσ0 : 0 < σ := hσ ▸ lt_min (by positivity) (mul_pos hδ hs)
  have hστ : σ ≤ (d : ℝ)⁻¹ := hσ ▸ min_le_left _ _
  have hσ1 : σ ≤ 1 := hστ.trans (inv_le_one_of_one_le₀ hd1)
  have hσδ : σ ≤ δ * s := hσ ▸ min_le_right _ _
  have hca0 : 0 < 1 / (2 * (3 * (d : ℝ) * κ * θ)) := by positivity
  have hcaF0 : 0 < 1 / (2 * (3 * (d : ℝ) * κ * θF)) := by positivity
  have hc₃0 : 0 < ((2 * (d : ℝ)) ^ (δ - 1) / C₂) ^ s := by positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min (min (min (1 / (2 * (3 * (d : ℝ) * κ * θ))) (cs / 3))
      (min (1 / (2 * (3 * (d : ℝ) * κ * θF))) (cF / 3)))
      (min c₁ (((2 * (d : ℝ)) ^ (δ - 1) / C₂) ^ s)) := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ lt_min (lt_min (lt_min hca0 (by positivity))
    (lt_min hcaF0 (by positivity))) (lt_min hc₁ hc₃0)
  have hcca : c ≤ 1 / (2 * (3 * (d : ℝ) * κ * θ)) :=
    hc ▸ ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hccs : c ≤ cs / 3 :=
    hc ▸ ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hccaF : c ≤ 1 / (2 * (3 * (d : ℝ) * κ * θF)) :=
    hc ▸ ((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hccsF : c ≤ cF / 3 :=
    hc ▸ ((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hcc₁ : c ≤ c₁ := hc ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hcc₃ : c ≤ ((2 * (d : ℝ)) ^ (δ - 1) / C₂) ^ s :=
    hc ▸ (min_le_right _ _).trans (min_le_right _ _)
  have hCs0 : 0 ≤ Cs.toReal := ENNReal.toReal_nonneg
  have hCF0 : 0 ≤ CF.toReal := ENNReal.toReal_nonneg
  have hCa0 : 0 ≤ 2 * (2 * (1 + (d : ℝ) * (2 * (3 * d * κ * θ)))) ^ d := by positivity
  have hCaF0 : 0 ≤ 2 * (2 * (1 + (d : ℝ) * (2 * (3 * d * κ * θF)))) ^ d := by positivity
  have hCg0 : 0 ≤ 3 ^ d * (1 + 3 * (κ : ℝ)) ^ d * (3 ^ d * C₁ + 2) := by positivity
  refine ⟨2 * (2 * (1 + (d : ℝ) * (2 * (3 * d * κ * θ)))) ^ d + 3 ^ d * Cs.toReal +
      d / (1 - p) * (2 * (2 * (1 + (d : ℝ) * (2 * (3 * d * κ * θF)))) ^ d) +
      d / (1 - p) * (3 ^ d * CF.toReal) +
      3 ^ d * (1 + 3 * (κ : ℝ)) ^ d * (3 ^ d * C₁ + 2) + 1, c, σ, by positivity, hc0, hσ0, hσ1,
    fun i R hR u => ?_⟩
  have hx1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hX : (0 : ℝ) ≤ (R : ℝ) ^ (2 * d) * Real.exp (-(c * (R : ℝ) ^ σ)) := by positivity
  have hA := (hfar κ R hκ u).trans (ENNReal.ofReal_le_ofReal
    (far_term_le (a := 2 * d) (σ := σ) hCa0 hx1 hσ1 hc0.le hcca))
  have hB : latticeBondLaw d p {ω | PartitionEvent ω ∧ ¬ SideGood R ω u} ≤
      ENNReal.ofReal (3 ^ d * Cs.toReal * (R : ℝ) ^ (2 * d) * Real.exp (-(c * (R : ℝ) ^ σ))) := by
    refine (hside R u).trans ?_
    have hconv : (((2 * R + 1) ^ d : ℕ) : ℝ≥0∞) *
        (Cs * ENNReal.ofReal (Real.exp (-cs * (3 : ℝ) ^ capScale R))) =
        ENNReal.ofReal ((((2 * R + 1) ^ d : ℕ) : ℝ) *
          (Cs.toReal * Real.exp (-cs * (3 : ℝ) ^ capScale R))) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hCs0, ENNReal.ofReal_natCast,
        ENNReal.ofReal_toReal hCs]
    rw [hconv]
    exact ENNReal.ofReal_le_ofReal
      (side_term_le hR (lt_three_mul_three_pow_capScale R) hcs hσ1 hc0.le hccs hCs0)
  have hAF : latticeBondLaw d p {ω | ¬ FarGoodFlip edgeBond κ R ω u} ≤
      ENNReal.ofReal (d / (1 - p) * (2 * (2 * (1 + (d : ℝ) * (2 * (3 * d * κ * θF)))) ^ d) *
        (R : ℝ) ^ (2 * d) * Real.exp (-(c * (R : ℝ) ^ σ))) := by
    refine (hfarF edgeBond κ R hκ u).trans (ENNReal.ofReal_le_ofReal ?_)
    have h := far_term_le (a := 2 * d) (σ := σ) hCaF0 hx1 hσ1 hc0.le hccaF
    calc _ = (d : ℝ) / (1 - (p : ℝ)) * (2 * (2 * (1 + (d : ℝ) * (2 * (3 * d * κ * θF)))) ^ d *
          Real.exp (-((R : ℝ) / (2 * (3 * d * κ * θF))))) := by ring
      _ ≤ (d : ℝ) / (1 - (p : ℝ)) * (2 * (2 * (1 + (d : ℝ) * (2 * (3 * d * κ * θF)))) ^ d *
          (R : ℝ) ^ (2 * d) * Real.exp (-(c * (R : ℝ) ^ σ))) :=
          mul_le_mul_of_nonneg_left h hdp
      _ = _ := by ring
  have hBF : latticeBondLaw d p {ω | ¬ SideGoodFlip edgeBond R ω u} ≤
      ENNReal.ofReal (d / (1 - p) * (3 ^ d * CF.toReal) * (R : ℝ) ^ (2 * d) *
        Real.exp (-(c * (R : ℝ) ^ σ))) := by
    refine (hsideF edgeBond R u).trans ?_
    have hconv : ((d * (2 * R + 1) ^ d : ℕ) : ℝ≥0∞) *
        (CF * ENNReal.ofReal (Real.exp (-cF * (3 : ℝ) ^ capScale R) / (1 - p))) =
        ENNReal.ofReal (((d * (2 * R + 1) ^ d : ℕ) : ℝ) *
          (CF.toReal * (Real.exp (-cF * (3 : ℝ) ^ capScale R) / (1 - p)))) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hCF0, ENNReal.ofReal_natCast,
        ENNReal.ofReal_toReal hCF]
    rw [hconv]
    refine ENNReal.ofReal_le_ofReal ?_
    have h := side_term_le (d := d) hR (lt_three_mul_three_pow_capScale R) hcF hσ1 hc0.le hccsF
      hCF0
    calc (((d * (2 * R + 1) ^ d : ℕ) : ℝ) *
          (CF.toReal * (Real.exp (-cF * (3 : ℝ) ^ capScale R) / (1 - p))))
        = (d : ℝ) / (1 - (p : ℝ)) * ((((2 * R + 1) ^ d : ℕ) : ℝ) *
          (CF.toReal * Real.exp (-cF * (3 : ℝ) ^ capScale R))) := by push_cast; ring
      _ ≤ (d : ℝ) / (1 - (p : ℝ)) * (3 ^ d * CF.toReal * (R : ℝ) ^ (2 * d) *
          Real.exp (-(c * (R : ℝ) ^ σ))) := mul_le_mul_of_nonneg_left h hdp
      _ = _ := by ring
  have hC : latticeBondLaw d p {ω | ω ∈ G ∧ ¬ GradGood hG hGv κ R i ω u} ≤
      ENNReal.ofReal (3 ^ d * (1 + 3 * (κ : ℝ)) ^ d * (3 ^ d * C₁ + 2) * (R : ℝ) ^ (2 * d) *
        Real.exp (-(c * (R : ℝ) ^ σ))) := by
    refine (hgrad κ R i hR u).trans ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal
      (grad_term_le hR hC₁.le hL hC₂ hτ hστ hσδ hc0.le hcc₁ hcc₃)
  refine (measure_not_domGood_le_add hG hGv (ae_iff.1 (ae_partitionEvent (by omega) hpc))
    (ae_iff.1 hGae) κ R i u).trans ?_
  refine (add_le_add hA (add_le_add hB (add_le_add hAF (add_le_add hBF hC)))).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : (2 * (2 * (1 + (d : ℝ) * (2 * (3 * d * κ * θ)))) ^ d + 3 ^ d * Cs.toReal +
      d / (1 - p) * (2 * (2 * (1 + (d : ℝ) * (2 * (3 * d * κ * θF)))) ^ d) +
      d / (1 - p) * (3 ^ d * CF.toReal) +
      3 ^ d * (1 + 3 * (κ : ℝ)) ^ d * (3 ^ d * C₁ + 2) + 1) * (R : ℝ) ^ (2 * d) *
        Real.exp (-(c * (R : ℝ) ^ σ)) =
      (2 * (2 * (1 + (d : ℝ) * (2 * (3 * d * κ * θ)))) ^ d * (R : ℝ) ^ (2 * d) *
          Real.exp (-(c * (R : ℝ) ^ σ)) +
        (3 ^ d * Cs.toReal * (R : ℝ) ^ (2 * d) * Real.exp (-(c * (R : ℝ) ^ σ)) +
          (d / (1 - p) * (2 * (2 * (1 + (d : ℝ) * (2 * (3 * d * κ * θF)))) ^ d) *
              (R : ℝ) ^ (2 * d) * Real.exp (-(c * (R : ℝ) ^ σ)) +
            (d / (1 - p) * (3 ^ d * CF.toReal) * (R : ℝ) ^ (2 * d) *
                Real.exp (-(c * (R : ℝ) ^ σ)) +
              3 ^ d * (1 + 3 * (κ : ℝ)) ^ d * (3 ^ d * C₁ + 2) * (R : ℝ) ^ (2 * d) *
                Real.exp (-(c * (R : ℝ) ^ σ)))))) +
        (R : ℝ) ^ (2 * d) * Real.exp (-(c * (R : ℝ) ^ σ)) := by ring
  rw [e]
  exact le_add_of_nonneg_right hX

end Grad

end Rigidity.Corrector.GeneralDim
