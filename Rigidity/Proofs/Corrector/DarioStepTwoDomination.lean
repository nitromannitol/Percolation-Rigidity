import Rigidity.Proofs.Corrector.DarioStepTwoWeightMeas

/-!
# The domination of the weight by the finite-range weight

A vertex `u` is good for the domination at range `R` (`DomGood`) when the planar partition exists,
the configuration lies in the event `G` of the corrector, no far edge reaches `u`, the capped sides
are the sides near `u` and the local gradient bounds dominate the plane gradient bound near `u`.
Then the weight of the Step 2 sum at `u` is at most the finite-range weight. On a triadic cube all
of whose vertices are good, the weight bound of the cube follows from the same bound for the
finite-range weight (`weightGood_of_domGood`). A vertex fails to be good with probability at most
`C R⁴ e^{-c R^σ}` with `σ ≤ 1/2` (`measure_not_domGood_le`), collecting the three failure
probabilities of `DarioStepTwoFiniteProb`.
-/

namespace Rigidity.Corrector

open MeasureTheory Filter LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

theorem exp_neg_le_exp_neg_rpow {x a b σ : ℝ} (hx : 1 ≤ x) (hσ : σ ≤ 1) (hb0 : 0 ≤ b)
    (hb : b ≤ a) : Real.exp (-(a * x)) ≤ Real.exp (-(b * x ^ σ)) := by
  have h1 : x ^ σ ≤ x := by
    calc x ^ σ ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx hσ
      _ = x := Real.rpow_one x
  have hx0 : 0 ≤ x ^ σ := Real.rpow_nonneg (by linarith) σ
  exact Real.exp_le_exp.2 (by nlinarith)

theorem exp_neg_rpow_le_exp_neg_rpow {x a b σ τ : ℝ} (hx : 1 ≤ x) (hστ : σ ≤ τ) (hb0 : 0 ≤ b)
    (hb : b ≤ a) : Real.exp (-(a * x ^ τ)) ≤ Real.exp (-(b * x ^ σ)) := by
  have h1 : x ^ σ ≤ x ^ τ := Real.rpow_le_rpow_of_exponent_le hx hστ
  have hx0 : 0 ≤ x ^ σ := Real.rpow_nonneg (by linarith) σ
  exact Real.exp_le_exp.2 (by nlinarith)

theorem grad_exponent_eq {R C₂ δ s : ℝ} (hR : 0 < R) (hC₂ : 0 < C₂) :
    (R / (C₂ * (3 * R) ^ (1 - δ))) ^ s = (3 ^ (δ - 1) / C₂) ^ s * R ^ (δ * s) := by
  have h1 : (3 * R) ^ (1 - δ) = 3 ^ (1 - δ) * R ^ (1 - δ) := Real.mul_rpow (by norm_num) hR.le
  have hRδ : 0 < R ^ δ := Real.rpow_pos_of_pos hR δ
  have h3δ : (0 : ℝ) < 3 ^ δ := Real.rpow_pos_of_pos (by norm_num) δ
  have h2 : R / (C₂ * (3 * R) ^ (1 - δ)) = (3 ^ (δ - 1) / C₂) * R ^ δ := by
    rw [h1, Real.rpow_sub hR, Real.rpow_sub (by norm_num : (0 : ℝ) < 3),
      Real.rpow_sub (by norm_num : (0 : ℝ) < 3), Real.rpow_one, Real.rpow_one]
    field_simp
  rw [h2, Real.mul_rpow (by positivity) hRδ.le, ← Real.rpow_mul hR.le]

/-- The far-edge term in the form `C x⁴ e^{-c x^σ}`. -/
theorem far_term_le {x θ c σ : ℝ} {κ : ℕ} (hκ : 1 ≤ κ) (hθ : 0 < θ) (hx : 1 ≤ x) (hσ1 : σ ≤ 1)
    (hc0 : 0 ≤ c) (hcca : c ≤ 1 / (2 * (6 * κ * θ))) :
    8 * (1 + 2 * (2 * (6 * κ * θ))) ^ 2 * Real.exp (-(x / (2 * (6 * κ * θ)))) ≤
      8 * (1 + 2 * (2 * (6 * κ * θ))) ^ 2 * x ^ 4 * Real.exp (-(c * x ^ σ)) := by
  have hκ1 : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  have e : x / (2 * (6 * κ * θ)) = (1 / (2 * (6 * κ * θ))) * x := by ring
  rw [e]
  have h := exp_neg_le_exp_neg_rpow hx hσ1 hc0 hcca
  have hx4 : (1 : ℝ) ≤ x ^ 4 := one_le_pow₀ hx
  have hE0 : 0 ≤ Real.exp (-(c * x ^ σ)) := (Real.exp_pos _).le
  have hCa : 0 ≤ 8 * (1 + 2 * (2 * (6 * (κ : ℝ) * θ))) ^ 2 := by positivity
  calc 8 * (1 + 2 * (2 * (6 * κ * θ))) ^ 2 * Real.exp (-(1 / (2 * (6 * κ * θ)) * x))
      ≤ 8 * (1 + 2 * (2 * (6 * κ * θ))) ^ 2 * Real.exp (-(c * x ^ σ)) :=
        mul_le_mul_of_nonneg_left h hCa
    _ ≤ 8 * (1 + 2 * (2 * (6 * κ * θ))) ^ 2 * (x ^ 4 * Real.exp (-(c * x ^ σ))) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hE0 hx4) hCa
    _ = _ := by ring

/-- The capped-side term in the form `C x⁴ e^{-c x^σ}`. -/
theorem side_term_le {R : ℕ} (hR : 1 ≤ R) {cs c σ C : ℝ} (hcs : 0 < cs) (hσ1 : σ ≤ 1)
    (hc0 : 0 ≤ c) (hccs : c ≤ cs / 3) (hC : 0 ≤ C) :
    ((((2 * R + 1) ^ 2 : ℕ) : ℝ)) * (C * Real.exp (-cs * (3 : ℝ) ^ capScale R)) ≤
      9 * C * (R : ℝ) ^ 4 * Real.exp (-(c * (R : ℝ) ^ σ)) := by
  have hx1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have h3 : (R : ℝ) / 3 ≤ (3 : ℝ) ^ capScale R := by
    have := lt_three_mul_three_pow_capScale R
    have : (R : ℝ) < 3 * 3 ^ capScale R := by exact_mod_cast this
    linarith
  have hexp : Real.exp (-cs * (3 : ℝ) ^ capScale R) ≤ Real.exp (-(cs / 3 * R)) := by
    refine Real.exp_le_exp.2 ?_
    have := mul_le_mul_of_nonneg_left h3 hcs.le
    have e : cs * (R / 3) = cs / 3 * R := by ring
    linarith
  have h2 := exp_neg_le_exp_neg_rpow (a := cs / 3) hx1 hσ1 hc0 hccs
  have hN : ((((2 * R + 1) ^ 2 : ℕ) : ℝ)) ≤ 9 * (R : ℝ) ^ 4 := by
    push_cast
    have h1 : (2 * (R : ℝ) + 1) ^ 2 ≤ 9 * (R : ℝ) ^ 2 := by nlinarith
    have h2 : (R : ℝ) ^ 2 ≤ (R : ℝ) ^ 4 := pow_le_pow_right₀ hx1 (by norm_num)
    linarith
  calc ((((2 * R + 1) ^ 2 : ℕ) : ℝ)) * (C * Real.exp (-cs * (3 : ℝ) ^ capScale R))
      ≤ 9 * (R : ℝ) ^ 4 * (C * Real.exp (-(c * (R : ℝ) ^ σ))) :=
        mul_le_mul hN (mul_le_mul_of_nonneg_left (hexp.trans h2) hC) (by positivity)
          (by positivity)
    _ = _ := by ring

/-- The local-gradient term in the form `C x⁴ e^{-c x^σ}`. -/
theorem grad_term_le {R κ : ℕ} (hR : 1 ≤ R) {C₁ c₁ s δ C₂ c σ : ℝ} (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂) (hσ1 : σ ≤ 1 / 2) (hσδ : σ ≤ δ * s) (hc0 : 0 ≤ c) (hcc₁ : c ≤ c₁)
    (hcc₃ : c ≤ (3 ^ (δ - 1) / C₂) ^ s) :
    ((((2 * (R + 3 * κ * R) + 1) ^ 2 : ℕ) : ℝ)) *
      ((2 * (R : ℝ) + 1) ^ 2 * (C₁ * Real.exp (-(c₁ * Real.sqrt (R + 1)))) +
        2 * Real.exp (-((R : ℝ) / (C₂ * (3 * R) ^ (1 - δ))) ^ s)) ≤
      9 * (1 + 3 * κ) ^ 2 * (9 * C₁ + 2) * (R : ℝ) ^ 4 * Real.exp (-(c * (R : ℝ) ^ σ)) := by
  have hx1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hx0 : (0 : ℝ) < R := by linarith
  set E : ℝ := Real.exp (-(c * (R : ℝ) ^ σ)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  have hN : ((((2 * (R + 3 * κ * R) + 1) ^ 2 : ℕ) : ℝ)) ≤
      9 * (1 + 3 * κ) ^ 2 * (R : ℝ) ^ 2 := by
    push_cast
    have h1 : (1 : ℝ) ≤ (1 + 3 * κ) * R := by nlinarith
    have h2 : 2 * ((R : ℝ) + 3 * κ * R) + 1 ≤ 3 * ((1 + 3 * κ) * R) := by nlinarith
    have h0 : (0 : ℝ) ≤ 2 * ((R : ℝ) + 3 * κ * R) + 1 := by positivity
    calc (2 * ((R : ℝ) + 3 * κ * R) + 1) ^ 2 ≤ (3 * ((1 + 3 * κ) * R)) ^ 2 :=
          pow_le_pow_left₀ h0 h2 2
      _ = 9 * (1 + 3 * κ) ^ 2 * (R : ℝ) ^ 2 := by ring
  have hsq : (R : ℝ) ^ σ ≤ Real.sqrt (R + 1) := by
    calc (R : ℝ) ^ σ ≤ (R : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hσ1
      _ = Real.sqrt R := (Real.sqrt_eq_rpow _).symm
      _ ≤ Real.sqrt (R + 1) := Real.sqrt_le_sqrt (by linarith)
  have hE1 : Real.exp (-(c₁ * Real.sqrt (R + 1))) ≤ E := by
    refine Real.exp_le_exp.2 ?_
    have h0 : 0 ≤ (R : ℝ) ^ σ := by positivity
    nlinarith
  have hE2 : Real.exp (-((R : ℝ) / (C₂ * (3 * R) ^ (1 - δ))) ^ s) ≤ E := by
    rw [grad_exponent_eq hx0 hC₂]
    exact exp_neg_rpow_le_exp_neg_rpow hx1 hσδ hc0 hcc₃
  have hM : (2 * (R : ℝ) + 1) ^ 2 ≤ 9 * (R : ℝ) ^ 2 := by nlinarith
  have hR2 : (1 : ℝ) ≤ (R : ℝ) ^ 2 := one_le_pow₀ hx1
  have hY : (2 * (R : ℝ) + 1) ^ 2 * (C₁ * Real.exp (-(c₁ * Real.sqrt (R + 1)))) +
      2 * Real.exp (-((R : ℝ) / (C₂ * (3 * R) ^ (1 - δ))) ^ s) ≤
      (9 * C₁ + 2) * (R : ℝ) ^ 2 * E := by
    calc (2 * (R : ℝ) + 1) ^ 2 * (C₁ * Real.exp (-(c₁ * Real.sqrt (R + 1)))) +
          2 * Real.exp (-((R : ℝ) / (C₂ * (3 * R) ^ (1 - δ))) ^ s)
        ≤ 9 * (R : ℝ) ^ 2 * (C₁ * E) + 2 * ((R : ℝ) ^ 2 * E) := by
          gcongr
          exact hE2.trans (le_mul_of_one_le_left hE0 hR2)
      _ = (9 * C₁ + 2) * (R : ℝ) ^ 2 * E := by ring
  have hY0 : 0 ≤ (2 * (R : ℝ) + 1) ^ 2 * (C₁ * Real.exp (-(c₁ * Real.sqrt (R + 1)))) +
      2 * Real.exp (-((R : ℝ) / (C₂ * (3 * R) ^ (1 - δ))) ^ s) := by positivity
  calc ((((2 * (R + 3 * κ * R) + 1) ^ 2 : ℕ) : ℝ)) *
        ((2 * (R : ℝ) + 1) ^ 2 * (C₁ * Real.exp (-(c₁ * Real.sqrt (R + 1)))) +
          2 * Real.exp (-((R : ℝ) / (C₂ * (3 * R) ^ (1 - δ))) ^ s))
      ≤ 9 * (1 + 3 * κ) ^ 2 * (R : ℝ) ^ 2 * ((9 * C₁ + 2) * (R : ℝ) ^ 2 * E) :=
        mul_le_mul hN hY hY0 (by positivity)
    _ = _ := by ring

section Grad

variable {G : Set (Configuration 2)} (hG : MeasurableSet G) (hGv : G ⊆ correctorValidEvent 2)

/-- The vertex `u` is good for the domination of the weight at range `R`. -/
def DomGood (κ R : ℕ) (i : Fin 2) (ω : Configuration 2) (u : Vertex 2) : Prop :=
  PlanarPartitionEvent ω ∧ ω ∈ G ∧ FarGood κ R ω u ∧ SideGood R ω u ∧
    GradGood hG hGv κ R i ω u

/-- **The weight bound of a cube from the finite-range weight.** -/
theorem weightGood_of_domGood {κ R : ℕ} (hR : 1 ≤ R) {i : Fin 2} {q M : ℝ} (hq : 0 ≤ q)
    {ω : Configuration 2} {T : TriadicCube 2}
    (hdom : ∀ u ∈ T.toIntegerCube.vertices, DomGood hG hGv κ R i ω u)
    (hsum : ∑ u ∈ T.toIntegerCube.vertices, finiteWeight κ R ω u ^ q ≤
      M * T.toIntegerCube.vertices.card) :
    weightGood hG hGv κ i q M ω T := by
  have hle : ∀ u ∈ T.toIntegerCube.vertices,
      stepTwoWeight hG hGv κ i ω u ≤ ENNReal.ofReal (finiteWeight κ R ω u) := fun u hu =>
    stepTwoWeight_le_finiteWeight hG hGv (hdom u hu).1 hR (hdom u hu).2.2.1 (hdom u hu).2.2.2.1
      (hdom u hu).2.2.2.2
  refine ⟨fun u hu => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hle u hu), le_trans ?_ hsum⟩
  refine Finset.sum_le_sum fun u hu => Real.rpow_le_rpow ENNReal.toReal_nonneg ?_ hq
  exact ENNReal.toReal_le_of_le_ofReal (finiteWeight_nonneg hR ω u) (hle u hu)

/-- The failure of the domination splits into the three failure events. -/
theorem measure_not_domGood_le_add {p : unitInterval}
    (hP0 : latticeBondLaw 2 p {ω | ¬ PlanarPartitionEvent ω} = 0)
    (hG0 : latticeBondLaw 2 p Gᶜ = 0) (κ R : ℕ) (i : Fin 2) (u : Vertex 2) :
    latticeBondLaw 2 p {ω | ¬ DomGood hG hGv κ R i ω u} ≤
      latticeBondLaw 2 p {ω | PlanarPartitionEvent ω ∧ ¬ FarGood κ R ω u} +
        (latticeBondLaw 2 p {ω | PlanarPartitionEvent ω ∧ ¬ SideGood R ω u} +
          latticeBondLaw 2 p {ω | ω ∈ G ∧ ¬ GradGood hG hGv κ R i ω u}) := by
  have hsub : {ω | ¬ DomGood hG hGv κ R i ω u} ⊆ ({ω | ¬ PlanarPartitionEvent ω} ∪ Gᶜ) ∪
      ({ω | PlanarPartitionEvent ω ∧ ¬ FarGood κ R ω u} ∪
        ({ω | PlanarPartitionEvent ω ∧ ¬ SideGood R ω u} ∪
          {ω | ω ∈ G ∧ ¬ GradGood hG hGv κ R i ω u})) := by
    intro ω hω
    by_cases hP : PlanarPartitionEvent ω
    · by_cases hGω : ω ∈ G
      · by_cases hF : FarGood κ R ω u
        · by_cases hS : SideGood R ω u
          · exact Or.inr (Or.inr (Or.inr ⟨hGω, fun hg => hω ⟨hP, hGω, hF, hS, hg⟩⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨hP, hS⟩))
        · exact Or.inr (Or.inl ⟨hP, hF⟩)
      · exact Or.inl (Or.inr hGω)
    · exact Or.inl (Or.inl hP)
  have hN := measure_union_null hP0 hG0
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [hN, zero_add]
  exact (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))

/-- **A vertex is good for the domination, with high probability.** -/
theorem measure_not_domGood_le {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (hGae : ∀ᵐ ω ∂latticeBondLaw 2 p, ω ∈ G) {κ : ℕ} (hκ : 1 ≤ κ) :
    ∃ C c σ : ℝ, 0 < C ∧ 0 < c ∧ 0 < σ ∧ σ ≤ 1 / 2 ∧ ∀ (i : Fin 2) (R : ℕ), 1 ≤ R →
      ∀ u : Vertex 2, latticeBondLaw 2 p {ω | ¬ DomGood hG hGv κ R i ω u} ≤
        ENNReal.ofReal (C * (R : ℝ) ^ 4 * Real.exp (-(c * (R : ℝ) ^ σ))) := by
  obtain ⟨θ, hθ, hfar⟩ := measure_not_farGood_le hpc
  obtain ⟨Cs, hCs, cs, hcs, hside⟩ := measure_not_sideGood_le hpc
  obtain ⟨C₁, c₁, s, δ, C₂, hC₁, hc₁, hs, hδ, hC₂, hgrad⟩ :=
    measure_not_gradGood_le hG hGv hpc hp1 hGae
  have hκ1 : (1 : ℝ) ≤ κ := by exact_mod_cast hκ
  obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = min (1 / 2) (δ * s) := ⟨_, rfl⟩
  have hσ0 : 0 < σ := hσ ▸ lt_min (by norm_num) (mul_pos hδ hs)
  have hσ1 : σ ≤ 1 / 2 := hσ ▸ min_le_left _ _
  have hσδ : σ ≤ δ * s := hσ ▸ min_le_right _ _
  have hca0 : 0 < 1 / (2 * (6 * (κ : ℝ) * θ)) := by positivity
  have hc₃0 : 0 < (3 ^ (δ - 1) / C₂) ^ s := by positivity
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = min (min (1 / (2 * (6 * (κ : ℝ) * θ))) (cs / 3))
      (min c₁ ((3 ^ (δ - 1) / C₂) ^ s)) := ⟨_, rfl⟩
  have hc0 : 0 < c := hc ▸ lt_min (lt_min hca0 (by positivity)) (lt_min hc₁ hc₃0)
  have hcca : c ≤ 1 / (2 * (6 * (κ : ℝ) * θ)) := hc ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hccs : c ≤ cs / 3 := hc ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hcc₁ : c ≤ c₁ := hc ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hcc₃ : c ≤ (3 ^ (δ - 1) / C₂) ^ s := hc ▸ (min_le_right _ _).trans (min_le_right _ _)
  have hCs0 : 0 ≤ Cs.toReal := ENNReal.toReal_nonneg
  have hCa0 : 0 ≤ 8 * (1 + 2 * (2 * (6 * (κ : ℝ) * θ))) ^ 2 := by positivity
  have hCg0 : 0 ≤ 9 * (1 + 3 * (κ : ℝ)) ^ 2 * (9 * C₁ + 2) := by positivity
  refine ⟨8 * (1 + 2 * (2 * (6 * (κ : ℝ) * θ))) ^ 2 + 9 * Cs.toReal +
      9 * (1 + 3 * (κ : ℝ)) ^ 2 * (9 * C₁ + 2) + 1, c, σ, by positivity, hc0, hσ0, hσ1,
    fun i R hR u => ?_⟩
  have hx1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hX : (0 : ℝ) ≤ (R : ℝ) ^ 4 * Real.exp (-(c * (R : ℝ) ^ σ)) := by positivity
  have hA := (hfar κ R hκ u).trans (ENNReal.ofReal_le_ofReal
    (far_term_le (σ := σ) hκ hθ hx1 (by linarith) hc0.le hcca))
  have hB : latticeBondLaw 2 p {ω | PlanarPartitionEvent ω ∧ ¬ SideGood R ω u} ≤
      ENNReal.ofReal (9 * Cs.toReal * (R : ℝ) ^ 4 * Real.exp (-(c * (R : ℝ) ^ σ))) := by
    refine (hside R u).trans ?_
    have hconv : (((2 * R + 1) ^ 2 : ℕ) : ℝ≥0∞) *
        (Cs * ENNReal.ofReal (Real.exp (-cs * (3 : ℝ) ^ capScale R))) =
        ENNReal.ofReal ((((2 * R + 1) ^ 2 : ℕ) : ℝ) *
          (Cs.toReal * Real.exp (-cs * (3 : ℝ) ^ capScale R))) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hCs0, ENNReal.ofReal_natCast,
        ENNReal.ofReal_toReal hCs]
    rw [hconv]
    exact ENNReal.ofReal_le_ofReal
      (side_term_le (σ := σ) hR hcs (by linarith) hc0.le hccs hCs0)
  have hC : latticeBondLaw 2 p {ω | ω ∈ G ∧ ¬ GradGood hG hGv κ R i ω u} ≤
      ENNReal.ofReal (9 * (1 + 3 * (κ : ℝ)) ^ 2 * (9 * C₁ + 2) * (R : ℝ) ^ 4 *
        Real.exp (-(c * (R : ℝ) ^ σ))) := by
    refine (hgrad κ R i hR u).trans ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (grad_term_le hR hC₁ hC₂ hσ1 hσδ hc0.le hcc₁ hcc₃)
  refine (measure_not_domGood_le_add hG hGv (ae_iff.1 (ae_planarPartitionEvent hpc))
    (ae_iff.1 hGae) κ R i u).trans ?_
  refine (add_le_add hA (add_le_add hB hC)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : (8 * (1 + 2 * (2 * (6 * (κ : ℝ) * θ))) ^ 2 + 9 * Cs.toReal +
      9 * (1 + 3 * (κ : ℝ)) ^ 2 * (9 * C₁ + 2) + 1) * (R : ℝ) ^ 4 *
        Real.exp (-(c * (R : ℝ) ^ σ)) =
      (8 * (1 + 2 * (2 * (6 * (κ : ℝ) * θ))) ^ 2 * (R : ℝ) ^ 4 * Real.exp (-(c * (R : ℝ) ^ σ)) +
        (9 * Cs.toReal * (R : ℝ) ^ 4 * Real.exp (-(c * (R : ℝ) ^ σ)) +
          9 * (1 + 3 * (κ : ℝ)) ^ 2 * (9 * C₁ + 2) * (R : ℝ) ^ 4 *
            Real.exp (-(c * (R : ℝ) ^ σ)))) +
        (R : ℝ) ^ 4 * Real.exp (-(c * (R : ℝ) ^ σ)) := by ring
  rw [e]
  exact le_add_of_nonneg_right hX

end Grad

end Rigidity.Corrector
