/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Support/AppendixA/CoarseDefs.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model
import Rigidity.Vendor.LHCH.Support.AppendixA.CoarseScaling
import Rigidity.Vendor.LHCH.Support.AppendixA.CoarseDuality
import Rigidity.Vendor.LHCH.Support.AppendixA.CoefficientUpper
import Rigidity.Vendor.LHCH.Support.AppendixA.CoefficientUpperB
import Rigidity.Vendor.LHCH.Support.AppendixA.MatrixQuadraticForms
import Rigidity.Vendor.LHCH.Support.AppendixA.RateArithmetic

/-!
# Vocabulary and deterministic facts for Appendix A

Scalar means and moment bounds of the coarse-grained matrices of lattice cubes, their averages
over children, and the facts about `A_□`, `B_□`: invariance under the conductances off the cube,
homogeneity, nonnegativity and strict positivity of the quadratic forms, the operator-norm bounds,
the restriction to the conductances of one cube, stationarity of the laws, the comparison of two
conductance fields, the cells of a cube, the bilinear energy, and the symmetry of the effective
conductivity (Appendix A, `s:homogenization`). It also states the three rate propositions
`WeakNormAt`, `DecayConcl` and `FiniteRangeRateConcl`.

The matrix-algebra facts (operator norm and quadratic forms) and the real arithmetic of the rates
that do not mention conductances live in `MatrixQuadraticForms` and `RateArithmetic`, which this
module imports.
-/

open MeasureTheory ProbabilityTheory Filter Topology LatticeProb Matrix
open scoped ENNReal NNReal Matrix.Norms.L2Operator

noncomputable section

namespace LatticeHC

variable {d : ℕ}

/-! ## Vocabulary -/

/-- Scalar means of the coarse-grained matrices of every cube `z + {0,…,L}^d` of side `L ≥ 1`:
`E A_□ = a(L) Id` and `E B_□ = b(L) Id`, with the same `a(L)`, `b(L)` for every `z`. -/
def CubeMeans {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (c : Ω → Edge d → ℝ)
    (hc : ∀ ω e, 0 < c ω e) (a b : ℕ → ℝ) : Prop :=
  ∀ (z : Site d) (L : ℕ), 1 ≤ L → ∀ i j : Fin d,
    ∫ ω, coarseA (c ω) z L (fun e _ => hc ω e) i j ∂μ = a L * (1 : Matrix (Fin d) (Fin d) ℝ) i j ∧
    ∫ ω, coarseB (c ω) z L (fun e _ => hc ω e) i j ∂μ = b L * (1 : Matrix (Fin d) (Fin d) ℝ) i j

/-- Moment bound of order `q`: `E[c_e^q] ≤ M^q` and `E[c_e^{-q}] ≤ M^q` for every edge, in
`ℝ≥0∞` and with no positivity assumption (`0^{-q} = ∞`), as in `IsFiniteRangeLaw` and `HypH1`. -/
def MomentBound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (c : Ω → Edge d → ℝ)
    (M q : ℝ) : Prop :=
  ∀ e : Edge d, ∫⁻ ω, ENNReal.ofReal (c ω e) ^ q ∂μ ≤ ENNReal.ofReal M ^ q ∧
    ∫⁻ ω, ENNReal.ofReal (c ω e) ^ (-q) ∂μ ≤ ENNReal.ofReal M ^ q

/-- The average `S_A` over the children `3^ℓ y + □_ℓ`, `y ∈ {0,…,3^{k-ℓ}-1}^d`, of `□_k` of the
matrices `A_□` (paper: `S_{k,ℓ}`, upper-left block). -/
def childAvgA (c : Edge d → ℝ) (hc : ∀ e, 0 < c e) (ℓ k : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  ((3 : ℝ) ^ (d * (k - ℓ)))⁻¹ •
    ∑ y ∈ Fintype.piFinset fun _ : Fin d => Finset.range (3 ^ (k - ℓ)),
      coarseA c (fun i => (3 ^ ℓ * y i : ℤ)) (3 ^ ℓ) (fun e _ => hc e)

/-- The average `S_B` over the children of `□_k` of the matrices `B_□`. -/
def childAvgB (c : Edge d → ℝ) (hc : ∀ e, 0 < c e) (ℓ k : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  ((3 : ℝ) ^ (d * (k - ℓ)))⁻¹ •
    ∑ y ∈ Fintype.piFinset fun _ : Fin d => Finset.range (3 ^ (k - ℓ)),
      coarseB c (fun i => (3 ^ ℓ * y i : ℤ)) (3 ^ ℓ) (fun e _ => hc e)

/-! ## Locality, homogeneity and positivity of the coarse-grained matrices -/

/-- The energy `ℰ_□(u)` depends on the conductances only through their values on the edges of
`□`. -/
theorem cubeEnergy_congr_edges {c c' : Edge d → ℝ} {z : Site d} {L : ℕ}
    (h : ∀ e ∈ edgesOf z L, c e = c' e) (u : Site d → ℝ) :
    cubeEnergy c z L u = cubeEnergy c' z L u := by
  unfold cubeEnergy
  congr 1
  exact Finset.sum_congr rfl fun e he => by rw [h e he]

/-- The energy depends only on the values of the function in the cube. -/
lemma cubeEnergy_congr {c : Edge d → ℝ} {z : Site d} {L : ℕ} {u v : Site d → ℝ}
    (h : ∀ x ∈ latticeCube z L, u x = v x) : cubeEnergy c z L u = cubeEnergy c z L v := by
  unfold cubeEnergy
  congr 1
  refine Finset.sum_congr rfl fun e he => ?_
  have he' := he
  simp only [edgesOf, Finset.mem_filter, Finset.mem_product] at he'
  rw [h e.tgt he'.2, h e.src he'.1.1]

/-- **Locality.** `A_□` depends only on the conductances of the edges of `□`. Route:
`cubeEnergy_congr_edges` and the uniqueness in `existsUnique_coarseA`. -/
theorem coarseA_congr {c c' : Edge d → ℝ} {z : Site d} {L : ℕ}
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) (hc' : ∀ e ∈ edgesOf z L, 0 < c' e)
    (h : ∀ e ∈ edgesOf z L, c e = c' e) : coarseA c z L hc = coarseA c' z L hc' := by
  have h1 := coarseA_spec c z L hc
  have h2 : (coarseA c z L hc).IsSymm ∧ ∀ p : Fin d → ℝ,
      IsLeast {E | ∃ u : Site d → ℝ, (∀ x ∈ vertexBoundary z L, u x = affine p x) ∧
        E = cubeEnergy c' z L u} (p ⬝ᵥ (coarseA c z L hc *ᵥ p)) := by
    refine ⟨h1.1, fun p => ?_⟩
    simpa only [cubeEnergy_congr_edges h] using h1.2 p
  exact (existsUnique_coarseA c' z L hc').unique h2 (coarseA_spec c' z L hc')

/-- **Locality.** `B_□` depends only on the conductances of the edges of `□`. Route:
`cubeEnergy_congr_edges` and the uniqueness in `existsUnique_coarseB`. -/
theorem coarseB_congr {c c' : Edge d → ℝ} {z : Site d} {L : ℕ}
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) (hc' : ∀ e ∈ edgesOf z L, 0 < c' e)
    (h : ∀ e ∈ edgesOf z L, c e = c' e) : coarseB c z L hc = coarseB c' z L hc' := by
  have h1 := coarseB_spec c z L hc
  have h2 : (coarseB c z L hc).IsSymm ∧ ∀ q : Fin d → ℝ,
      IsGreatest {E | ∃ u : Site d → ℝ,
        E = 2 * (q ⬝ᵥ cubeMeanGrad z L u) - cubeEnergy c' z L u}
        (q ⬝ᵥ (coarseB c z L hc *ᵥ q)) := by
    refine ⟨h1.1, fun q => ?_⟩
    simpa only [cubeEnergy_congr_edges h] using h1.2 q
  exact (existsUnique_coarseB c' z L hc').unique h2 (coarseB_spec c' z L hc')

/-- Two symmetric matrices with the same quadratic form are equal. -/
theorem eq_of_dotProduct_eq_symm {A A' : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsSymm)
    (hA' : A'.IsSymm) (h : ∀ p, p ⬝ᵥ (A *ᵥ p) = p ⬝ᵥ (A' *ᵥ p)) : A = A' := by
  classical
  ext i j
  have h1 := h (Pi.single i 1 + Pi.single j 1)
  have h2 := h (Pi.single i 1)
  have h3 := h (Pi.single j 1)
  have hs : A j i = A i j := by simpa using congrFun (congrFun hA i) j
  have hs' : A' j i = A' i j := by simpa using congrFun (congrFun hA' i) j
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, Matrix.mulVec_single_one,
    single_dotProduct, one_mul] at h1 h2 h3
  simp at h1 h2 h3
  linarith

/-- **Homogeneity as matrices.** `A_□(t c) = t A_□(c)`. Route: `coarse_smul` (for
quadratic forms) and `eq_of_dotProduct_eq_symm`. Used for the normalization
`c' = c / √(a_{n₀}/b_{n₀})` of `p:finite-range` Step 2. -/
theorem coarseA_smul (c : Edge d → ℝ) (z : Site d) (L : ℕ) (hc : ∀ e ∈ edgesOf z L, 0 < c e)
    {t : ℝ} (ht : 0 < t) :
    coarseA (fun e => t * c e) z L (fun e he => mul_pos ht (hc e he)) = t • coarseA c z L hc := by
  refine eq_of_dotProduct_eq_symm (coarseA_spec _ z L _).1 ?_ fun p => ?_
  · have h := (coarseA_spec c z L hc).1
    unfold Matrix.IsSymm at h ⊢
    rw [Matrix.transpose_smul, h]
  · rw [(coarse_smul c z L hc ht p).1, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **Homogeneity as matrices.** `B_□(t c) = t⁻¹ B_□(c)`. -/
theorem coarseB_smul (c : Edge d → ℝ) (z : Site d) (L : ℕ) (hc : ∀ e ∈ edgesOf z L, 0 < c e)
    {t : ℝ} (ht : 0 < t) :
    coarseB (fun e => t * c e) z L (fun e he => mul_pos ht (hc e he)) =
      t⁻¹ • coarseB c z L hc := by
  refine eq_of_dotProduct_eq_symm (coarseB_spec _ z L _).1 ?_ fun p => ?_
  · have h := (coarseB_spec c z L hc).1
    unfold Matrix.IsSymm at h ⊢
    rw [Matrix.transpose_smul, h]
  · rw [(coarse_smul c z L hc ht p).2, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- The energy of a positive field is nonnegative. -/
theorem cubeEnergy_nonneg (c : Edge d → ℝ) (z : Site d) (L : ℕ)
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) (u : Site d → ℝ) : 0 ≤ cubeEnergy c z L u := by
  unfold cubeEnergy
  refine mul_nonneg (inv_nonneg.2 (pow_nonneg (Nat.cast_nonneg L) d)) ?_
  refine Finset.sum_nonneg fun e he => ?_
  have : 0 ≤ faceWeight z L e := by unfold faceWeight; positivity
  exact mul_nonneg (mul_nonneg this (hc e he).le) (sq_nonneg _)

/-- **Positivity.** `p · A_□ p ≥ 0`. Proof: a least element of a set of energies. -/
theorem coarseA_form_nonneg (c : Edge d → ℝ) (z : Site d) (L : ℕ)
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) (p : Fin d → ℝ) :
    0 ≤ p ⬝ᵥ (coarseA c z L hc *ᵥ p) := by
  obtain ⟨u, -, hu⟩ := ((coarseA_spec c z L hc).2 p).1
  rw [hu]
  exact cubeEnergy_nonneg c z L hc u

/-- **Positivity.** `q · B_□ q ≥ 0`. Proof: test the maximum with `u = 0`. -/
theorem coarseB_form_nonneg (c : Edge d → ℝ) (z : Site d) (L : ℕ)
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) (q : Fin d → ℝ) :
    0 ≤ q ⬝ᵥ (coarseB c z L hc *ᵥ q) := by
  have h := ((coarseB_spec c z L hc).2 q).2 ⟨fun _ => 0, rfl⟩
  have h0 : cubeMeanGrad z L (fun _ => (0 : ℝ)) = 0 := by
    funext j; simp [cubeMeanGrad]
  have h1 : cubeEnergy c z L (fun _ => (0 : ℝ)) = 0 := by
    simp [cubeEnergy]
  rw [h0, h1] at h
  simpa using h

/-! ## Norm bounds and strict positivity -/

/-- **Operator-norm bound** for `A_□`: `‖A_□‖ ≤ Σ_j Λ_j`,
`Λ_j = L^{-d} Σ_{e ∥ e_j} w_□(e) c_e`. Proof: `A_□` is symmetric with nonnegative form,
`dotProduct_coarseA_le` and
`opNorm_le_of_abs_dotProduct_le`. -/
theorem norm_coarseA_le (c : Edge d → ℝ) (z : Site d) (L : ℕ)
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) :
    ‖coarseA c z L hc‖ ≤ ∑ j, ((L : ℝ) ^ d)⁻¹ *
      ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * c e := by
  have hΛ : ∀ j, 0 ≤ ((L : ℝ) ^ d)⁻¹ *
      ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * c e := fun j => by
    refine mul_nonneg (inv_nonneg.2 (pow_nonneg (Nat.cast_nonneg L) d))
      (Finset.sum_nonneg fun e he => ?_)
    exact mul_nonneg (by unfold faceWeight; positivity) (hc e (Finset.mem_filter.1 he).1).le
  set T := ∑ j, ((L : ℝ) ^ d)⁻¹ *
    ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * c e with hT
  refine opNorm_le_of_abs_dotProduct_le (coarseA_spec c z L hc).1
    (Finset.sum_nonneg fun j _ => hΛ j) fun p => ?_
  rw [abs_of_nonneg (coarseA_form_nonneg c z L hc p)]
  calc p ⬝ᵥ (coarseA c z L hc *ᵥ p)
      ≤ ∑ j, p j ^ 2 * (((L : ℝ) ^ d)⁻¹ *
        ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * c e) :=
        dotProduct_coarseA_le c z L hc p
    _ ≤ ∑ j, p j ^ 2 * T := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun i _ => hΛ i) (Finset.mem_univ j)) (sq_nonneg _)
    _ = T * (p ⬝ᵥ p) := by
        rw [← Finset.sum_mul, mul_comm]
        simp [dotProduct, sq]

/-- **Operator-norm bound** for `B_□`: `‖B_□‖ ≤ Σ_j Λ'_j`, `Λ'_j = L^{-d} Σ_{e ∥ e_j}
w_□(e) c_e⁻¹`. Proof: `dotProduct_coarseB_le` and `opNorm_le_of_abs_dotProduct_le`. -/
theorem norm_coarseB_le (c : Edge d → ℝ) (z : Site d) (L : ℕ)
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) :
    ‖coarseB c z L hc‖ ≤ ∑ j, ((L : ℝ) ^ d)⁻¹ *
      ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * (c e)⁻¹ := by
  have hΛ : ∀ j, 0 ≤ ((L : ℝ) ^ d)⁻¹ *
      ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * (c e)⁻¹ := fun j => by
    refine mul_nonneg (inv_nonneg.2 (pow_nonneg (Nat.cast_nonneg L) d))
      (Finset.sum_nonneg fun e he => ?_)
    exact mul_nonneg (by unfold faceWeight; positivity)
      (inv_nonneg.2 (hc e (Finset.mem_filter.1 he).1).le)
  set T := ∑ j, ((L : ℝ) ^ d)⁻¹ *
    ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * (c e)⁻¹ with hT
  refine opNorm_le_of_abs_dotProduct_le (coarseB_spec c z L hc).1
    (Finset.sum_nonneg fun j _ => hΛ j) fun p => ?_
  rw [abs_of_nonneg (coarseB_form_nonneg c z L hc p)]
  calc p ⬝ᵥ (coarseB c z L hc *ᵥ p)
      ≤ ∑ j, p j ^ 2 * (((L : ℝ) ^ d)⁻¹ *
        ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * (c e)⁻¹) :=
        dotProduct_coarseB_le c z L hc p
    _ ≤ ∑ j, p j ^ 2 * T := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun i _ => hΛ i) (Finset.mem_univ j)) (sq_nonneg _)
    _ = T * (p ⬝ᵥ p) := by
        rw [← Finset.sum_mul, mul_comm]
        simp [dotProduct, sq]

/-- **Strict positivity of `A_□`** for `L ≥ 1`. Proof: the duality
`2 p·q ≤ p·A p + q·B q` (`two_mul_dotProduct_le_coarse`) with `q = t p`, and `q·B q ≤ ‖B‖ |q|²`,
`‖B‖ ≤ Σ_j Λ'_j =: T` (`norm_coarseB_le`): `p·A p ≥ 2t|p|² - t² T |p|² > 0` for `t = (T+1)⁻¹`. -/
theorem coarseA_form_pos (c : Edge d → ℝ) (z : Site d) {L : ℕ} (hL : 1 ≤ L)
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) {p : Fin d → ℝ} (hp : p ≠ 0) :
    0 < p ⬝ᵥ (coarseA c z L hc *ᵥ p) := by
  set T := ∑ j, ((L : ℝ) ^ d)⁻¹ *
    ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * (c e)⁻¹ with hT
  have hT0 : 0 ≤ T := by
    refine Finset.sum_nonneg fun j _ => mul_nonneg (inv_nonneg.2 (pow_nonneg (Nat.cast_nonneg L) d))
      (Finset.sum_nonneg fun e he => ?_)
    exact mul_nonneg (by unfold faceWeight; positivity)
      (inv_nonneg.2 (hc e (Finset.mem_filter.1 he).1).le)
  have hpp : 0 < p ⬝ᵥ p := lt_of_le_of_ne (dotProduct_self_star_nonneg p)
    (Ne.symm fun h => hp (dotProduct_self_eq_zero.1 h))
  set t : ℝ := (T + 1)⁻¹ with ht
  have ht0 : 0 < t := inv_pos.2 (by linarith)
  have htT : t * T < 1 := by
    rw [ht, inv_mul_lt_iff₀ (by linarith)]
    linarith
  have h1 := two_mul_dotProduct_le_coarse c z hL hc p (t • p)
  have h2 : (t • p) ⬝ᵥ (coarseB c z L hc *ᵥ (t • p)) ≤ T * ((t • p) ⬝ᵥ (t • p)) :=
    ((le_abs_self _).trans (abs_dotProduct_mulVec_le_opNorm _ _)).trans
      (mul_le_mul_of_nonneg_right (norm_coarseB_le c z L hc) (dotProduct_self_star_nonneg _))
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h1 h2
  have key : 0 < t * (p ⬝ᵥ p) * (2 - t * T) :=
    mul_pos (mul_pos ht0 hpp) (by linarith)
  linarith [key]

/-- **Strict positivity of `B_□`** for `L ≥ 1`. Proof: the duality with `p = t q`,
`‖A‖ ≤ Σ_j Λ_j` (`norm_coarseA_le`). -/
theorem coarseB_form_pos (c : Edge d → ℝ) (z : Site d) {L : ℕ} (hL : 1 ≤ L)
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) {q : Fin d → ℝ} (hq : q ≠ 0) :
    0 < q ⬝ᵥ (coarseB c z L hc *ᵥ q) := by
  set T := ∑ j, ((L : ℝ) ^ d)⁻¹ *
    ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * c e with hT
  have hT0 : 0 ≤ T := by
    refine Finset.sum_nonneg fun j _ => mul_nonneg (inv_nonneg.2 (pow_nonneg (Nat.cast_nonneg L) d))
      (Finset.sum_nonneg fun e he => ?_)
    exact mul_nonneg (by unfold faceWeight; positivity) (hc e (Finset.mem_filter.1 he).1).le
  have hqq : 0 < q ⬝ᵥ q := lt_of_le_of_ne (dotProduct_self_star_nonneg q)
    (Ne.symm fun h => hq (dotProduct_self_eq_zero.1 h))
  set t : ℝ := (T + 1)⁻¹ with ht
  have ht0 : 0 < t := inv_pos.2 (by linarith)
  have htT : t * T < 1 := by
    rw [ht, inv_mul_lt_iff₀ (by linarith)]
    linarith
  have h1 := two_mul_dotProduct_le_coarse c z hL hc (t • q) q
  have h2 : (t • q) ⬝ᵥ (coarseA c z L hc *ᵥ (t • q)) ≤ T * ((t • q) ⬝ᵥ (t • q)) :=
    ((le_abs_self _).trans (abs_dotProduct_mulVec_le_opNorm _ _)).trans
      (mul_le_mul_of_nonneg_right (norm_coarseA_le c z L hc) (dotProduct_self_star_nonneg _))
  simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul] at h1 h2
  have key : 0 < t * (q ⬝ᵥ q) * (2 - t * T) :=
    mul_pos (mul_pos ht0 hqq) (by linarith)
  linarith [key]

/-! ## Dependence on the conductances of one cube -/

/-- `A_□` as a function of the conductances `ξ` on the edges of `□` alone: extended by `1` off the
edges of `□`, and read as `0` off the positive cone (the junk value of a total function; it is
never read on positive conductances, see `coarseA_eq_coarseAR`). -/
def coarseAR (z : Site d) (L : ℕ) (ξ : edgesOf z L → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  if h : ∀ e, 0 < ξ e then
    coarseA (fun e => if he : e ∈ edgesOf z L then ξ ⟨e, he⟩ else 1) z L
      (fun e he => by rw [dif_pos he]; exact h ⟨e, he⟩)
  else 0

/-- `B_□` as a function of the conductances on the edges of `□` alone (see `coarseAR`). -/
def coarseBR (z : Site d) (L : ℕ) (ξ : edgesOf z L → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  if h : ∀ e, 0 < ξ e then
    coarseB (fun e => if he : e ∈ edgesOf z L then ξ ⟨e, he⟩ else 1) z L
      (fun e he => by rw [dif_pos he]; exact h ⟨e, he⟩)
  else 0

/-- On positive conductances `A_□` is `coarseAR` of the restriction. Proof: `coarseA_congr`. -/
theorem coarseA_eq_coarseAR (c : Edge d → ℝ) (hc : ∀ e, 0 < c e) (z : Site d) (L : ℕ) :
    coarseA c z L (fun e _ => hc e) = coarseAR z L (fun e => c e.1) := by
  have h : ∀ e : edgesOf z L, 0 < c e.1 := fun e => hc e.1
  unfold coarseAR
  rw [dif_pos h]
  refine coarseA_congr _ _ fun e he => ?_
  simp [he]

/-- On positive conductances `B_□` is `coarseBR` of the restriction. -/
theorem coarseB_eq_coarseBR (c : Edge d → ℝ) (hc : ∀ e, 0 < c e) (z : Site d) (L : ℕ) :
    coarseB c z L (fun e _ => hc e) = coarseBR z L (fun e => c e.1) := by
  have h : ∀ e : edgesOf z L, 0 < c e.1 := fun e => hc e.1
  unfold coarseBR
  rw [dif_pos h]
  refine coarseB_congr _ _ fun e he => ?_
  simp [he]

/-! ## Stationarity -/

/-- **Stationarity of a law under shifts of the field.** Proof: `lintegral_map` twice. -/
theorem lintegral_shift_eq_of_edgeShiftStationary {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {c : Ω → Edge d → ℝ} (hcm : ∀ e, Measurable fun ω => c ω e)
    (hst : IsEdgeShiftStationary (μ.map c)) (z : Site d) {Φ : (Edge d → ℝ) → ℝ≥0∞}
    (hΦ : Measurable Φ) :
    ∫⁻ ω, Φ (shiftEdgeField z (c ω)) ∂μ = ∫⁻ ω, Φ (c ω) ∂μ := by
  have hc : Measurable c := measurable_pi_iff.2 hcm
  have hs : Measurable (shiftEdgeField (α := ℝ) z) :=
    measurable_pi_lambda _ fun e => measurable_pi_apply (z + e.1, e.2)
  calc ∫⁻ ω, Φ (shiftEdgeField z (c ω)) ∂μ
      = ∫⁻ x, Φ (shiftEdgeField z x) ∂(μ.map c) := by
        exact (lintegral_map (f := fun x => Φ (shiftEdgeField z x)) (hΦ.comp hs) hc).symm
    _ = ∫⁻ y, Φ y ∂((μ.map c).map (shiftEdgeField z)) := by
        rw [lintegral_map hΦ hs]
    _ = ∫⁻ y, Φ y ∂(μ.map c) := by rw [hst z]
    _ = ∫⁻ ω, Φ (c ω) ∂μ := by rw [lintegral_map hΦ hc]

/-- `IsStationary τ c` (used in `p:coarse`, `l:diffusivity`) gives the stationarity of the
law of `c` under the shifts of the field (used by `IsFiniteRangeLaw`). Proof: countably many
edges, so `c ∘ τ_x = τ_x c` almost surely as fields, then `map_act`. -/
theorem isEdgeShiftStationary_of_isStationary {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (τ : LatticeAction d μ) {c : Ω → Edge d → ℝ} (hcm : ∀ e, Measurable fun ω => c ω e)
    (hst : IsStationary τ c) : IsEdgeShiftStationary (μ.map c) := by
  intro x
  have hc : Measurable c := measurable_pi_iff.2 hcm
  have hs : Measurable (shiftEdgeField (α := ℝ) x) :=
    measurable_pi_lambda _ fun e => measurable_pi_apply (x + e.1, e.2)
  have hae : ∀ᵐ ω ∂μ, shiftEdgeField x (c ω) = c (τ.act x ω) := by
    have h : ∀ᵐ ω ∂μ, ∀ e : Edge d, shiftEdgeField x (c ω) e = c (τ.act x ω) e :=
      ae_all_iff.2 fun e => hst x e
    exact h.mono fun ω hω => funext hω
  calc (μ.map c).map (shiftEdgeField x) = μ.map (fun ω => shiftEdgeField x (c ω)) := by
        rw [Measure.map_map hs hc]; rfl
    _ = μ.map (fun ω => c (τ.act x ω)) := Measure.map_congr hae
    _ = (μ.map (τ.act x)).map c := by
        rw [Measure.map_map hc (τ.measurable_act x)]; rfl
    _ = μ.map c := by rw [τ.map_act x]

/-! ## The statements of the rate propositions -/

/-- The instance at `d` of the weak-norm input of Step 3 of the proof of `p:finite-range` (the
lattice version of AK25 (3.55), (3.68) and (4.17)), with its body written out.
`r = ⌈log₃(C₀(R+1))⌉`, `δ_n = a_n - b_n⁻¹`, `v_k` is `coarseDeviation`, the normalized conductances
are `c / D₀` with `D₀ = (a_{n₀}/b_{n₀})^{1/2}`, and `n₁ = n₀ + ⌈C₁ log(2 + M)⌉`. -/
def WeakNormAt (d : ℕ) : Prop :=
  ∃ κ₀ ε₀ C₀ C₁ C₂ : ℝ, 0 < κ₀ ∧ κ₀ ≤ 1 ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧
    ∀ M : ℝ, 2 ≤ M → ∃ C : ℝ, ∀ R : ℝ, 0 ≤ R →
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (c : Ω → Edge d → ℝ) (hc : ∀ ω e, 0 < c ω e), (∀ e, Measurable fun ω => c ω e) →
      IsFiniteRangeLaw d M R μ c → ∀ a b : ℕ → ℝ,
      (∀ n i j, ∫ ω, triadicA c hc n ω i j ∂μ = a n * (1 : Matrix (Fin d) (Fin d) ℝ) i j ∧
        ∫ ω, triadicB c hc n ω i j ∂μ = b n * (1 : Matrix (Fin d) (Fin d) ℝ) i j) →
      (∀ n : ℕ, ⌈Real.logb 3 (C₀ * (R + 1))⌉₊ + 4 ≤ n →
        ENNReal.ofReal ((a n - (b n)⁻¹) ^ 2) ≤ ENNReal.ofReal C *
          (∑ k ∈ Finset.Icc ⌈Real.logb 3 (C₀ * (R + 1))⌉₊ n,
              ENNReal.ofReal ((3 : ℝ) ^ (-(κ₀ * ((n : ℝ) - k)))) *
                (coarseDeviation μ c hc a b k +
                  ENNReal.ofReal (a k - (b k)⁻¹ - (a n - (b n)⁻¹))) +
            ENNReal.ofReal ((3 : ℝ) ^ (-(κ₀ * ((n : ℝ) - ⌈Real.logb 3 (C₀ * (R + 1))⌉₊)))))) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ n₀ : ℕ, ⌈Real.logb 3 (C₀ * (R + 1))⌉₊ ≤ n₀ →
        a n₀ - (b n₀)⁻¹ ≤ ε / M →
        ∀ (c' : Ω → Edge d → ℝ) (hc' : ∀ ω e, 0 < c' ω e),
          (∀ ω e, c' ω e = c ω e / Real.sqrt (a n₀ / b n₀)) → ∀ a' b' : ℕ → ℝ,
          (∀ n i j,
            ∫ ω, triadicA c' hc' n ω i j ∂μ = a' n * (1 : Matrix (Fin d) (Fin d) ℝ) i j ∧
            ∫ ω, triadicB c' hc' n ω i j ∂μ = b' n * (1 : Matrix (Fin d) (Fin d) ℝ) i j) →
          ∀ n : ℕ, n₀ + ⌈C₁ * Real.log (2 + M)⌉₊ + 4 ≤ n →
            ENNReal.ofReal (a' n - (b' n)⁻¹) ≤ ENNReal.ofReal C₂ *
              (∑ k ∈ Finset.Icc (n₀ + ⌈C₁ * Real.log (2 + M)⌉₊) n,
                  ENNReal.ofReal ((3 : ℝ) ^ (-(κ₀ * ((n : ℝ) - k)))) *
                    (coarseDeviation μ c' hc' a' b' k +
                      ENNReal.ofReal (a' k - (b' k)⁻¹ - (a' n - (b' n)⁻¹))) +
                ENNReal.ofReal ((3 : ℝ) ^ (-(κ₀ *
                  ((n : ℝ) - (n₀ + ⌈C₁ * Real.log (2 + M)⌉₊ : ℕ))))))

/-- The decay of the gap, `a_n - b_n⁻¹ ≤ C 3^{-κ(n - r_R)}` for `n ≥ r_R`, for the scalar means
`(a, b)` of a finite-range law (`p:finite-range` (ii)), for probability spaces in the universe
`v`. -/
def DecayConcl.{v} (d : ℕ) : Prop :=
  ∃ κ C₀ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ M : ℝ, 2 ≤ M → ∃ C : ℝ, ∀ R : ℝ, 0 ≤ R →
    ∀ {Ω : Type v} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (c : Ω → Edge d → ℝ) (hc : ∀ ω e, 0 < c ω e), (∀ e, Measurable fun ω => c ω e) →
      IsFiniteRangeLaw d M R μ c → ∀ a b : ℕ → ℝ,
      (∀ n i j, ∫ ω, triadicA c hc n ω i j ∂μ = a n * (1 : Matrix (Fin d) (Fin d) ℝ) i j ∧
        ∫ ω, triadicB c hc n ω i j ∂μ = b n * (1 : Matrix (Fin d) (Fin d) ℝ) i j) →
      (∀ n, M⁻¹ ≤ a n ∧ a n ≤ M ∧ M⁻¹ ≤ b n ∧ b n ≤ M ∧ (b n)⁻¹ ≤ a n) →
      Antitone a → Antitone b →
      ∀ n : ℕ, ⌈Real.logb 3 (C₀ * (R + 1))⌉ ≤ (n : ℤ) →
        a n - (b n)⁻¹ ≤ C * (3 : ℝ) ^ (-(κ * ((n : ℝ) - ⌈Real.logb 3 (C₀ * (R + 1))⌉)))

/-- The conclusion of `p:finite-range`, parts (i) and (ii), as a proposition, for probability
spaces in the universe `v`: the input of the transfer to the approximated conductances
(`p:coarse`). -/
def FiniteRangeRateConcl.{v} (d : ℕ) : Prop :=
  ∃ κ C₀ : ℝ, 0 < κ ∧ κ < 1 ∧ ∀ M : ℝ, 2 ≤ M → ∃ C : ℝ, ∀ R : ℝ, 0 ≤ R →
      ∀ {Ω : Type v} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (c : Ω → Edge d → ℝ) (hc : ∀ ω e, 0 < c ω e), (∀ e, Measurable fun ω => c ω e) →
        IsFiniteRangeLaw d M R μ c →
      ∃ a b : ℕ → ℝ, (∀ n, M⁻¹ ≤ a n ∧ a n ≤ M ∧ M⁻¹ ≤ b n ∧ b n ≤ M ∧
          (∀ i j, ∫ ω, triadicA c hc n ω i j ∂μ = a n * (1 : Matrix (Fin d) (Fin d) ℝ) i j) ∧
          (∀ i j, ∫ ω, triadicB c hc n ω i j ∂μ = b n * (1 : Matrix (Fin d) (Fin d) ℝ) i j) ∧
          0 ≤ a n - (b n)⁻¹ ∧ a n - (b n)⁻¹ ≤ M) ∧ Antitone a ∧ Antitone b ∧
        ∀ n : ℕ, ⌈Real.logb 3 (C₀ * (R + 1))⌉ ≤ (n : ℤ) →
          a n - (b n)⁻¹ ≤ C * (3 : ℝ) ^ (-(κ * ((n : ℝ) - ⌈Real.logb 3 (C₀ * (R + 1))⌉)))

/-! ## Comparison of two conductance fields -/

/-- **Comparison under a bounded ratio.** If `c ≤ Γ c'` and `c' ≤ Γ c` on the edges of `□`
(`Γ ≥ 1`), then `‖X(c) - X(c')‖ ≤ (Γ - 1) ‖X(c')‖` for `X = A_□, B_□`. Proof: `coarse_mono` and
`coarse_smul` give `Γ⁻¹ X(c') ⪯ X(c) ⪯ Γ X(c')` as quadratic forms, then
`opNorm_sub_le_of_ratio_forms`. -/
theorem coarse_sub_norm_le_of_ratio (c c' : Edge d → ℝ) (z : Site d) (L : ℕ)
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) (hc' : ∀ e ∈ edgesOf z L, 0 < c' e) {Γ : ℝ}
    (hΓ : 1 ≤ Γ) (h1 : ∀ e ∈ edgesOf z L, c e ≤ Γ * c' e)
    (h2 : ∀ e ∈ edgesOf z L, c' e ≤ Γ * c e) :
    ‖coarseA c z L hc - coarseA c' z L hc'‖ ≤ (Γ - 1) * ‖coarseA c' z L hc'‖ ∧
      ‖coarseB c z L hc - coarseB c' z L hc'‖ ≤ (Γ - 1) * ‖coarseB c' z L hc'‖ := by
  have hΓ0 : 0 < Γ := by linarith
  have hΓc : ∀ e ∈ edgesOf z L, 0 < Γ * c e := fun e he => mul_pos hΓ0 (hc e he)
  have hΓc' : ∀ e ∈ edgesOf z L, 0 < Γ * c' e := fun e he => mul_pos hΓ0 (hc' e he)
  have hA1 : ∀ p : Fin d → ℝ, p ⬝ᵥ (coarseA c z L hc *ᵥ p) ≤
      Γ * (p ⬝ᵥ (coarseA c' z L hc' *ᵥ p)) := fun p => by
    have := (coarse_mono c (fun e => Γ * c' e) z L hc hΓc' h1 p).1
    rwa [(coarse_smul c' z L hc' hΓ0 p).1] at this
  have hA2 : ∀ p : Fin d → ℝ, Γ⁻¹ * (p ⬝ᵥ (coarseA c' z L hc' *ᵥ p)) ≤
      p ⬝ᵥ (coarseA c z L hc *ᵥ p) := fun p => by
    have := (coarse_mono c' (fun e => Γ * c e) z L hc' hΓc h2 p).1
    rw [(coarse_smul c z L hc hΓ0 p).1] at this
    rw [inv_mul_le_iff₀ hΓ0]
    linarith
  have hB1 : ∀ p : Fin d → ℝ, Γ⁻¹ * (p ⬝ᵥ (coarseB c' z L hc' *ᵥ p)) ≤
      p ⬝ᵥ (coarseB c z L hc *ᵥ p) := fun p => by
    have := (coarse_mono c (fun e => Γ * c' e) z L hc hΓc' h1 p).2
    rwa [(coarse_smul c' z L hc' hΓ0 p).2] at this
  have hB2 : ∀ p : Fin d → ℝ, p ⬝ᵥ (coarseB c z L hc *ᵥ p) ≤
      Γ * (p ⬝ᵥ (coarseB c' z L hc' *ᵥ p)) := fun p => by
    have := (coarse_mono c' (fun e => Γ * c e) z L hc' hΓc h2 p).2
    rw [(coarse_smul c z L hc hΓ0 p).2] at this
    rw [← inv_mul_le_iff₀ hΓ0]
    linarith
  exact ⟨opNorm_sub_le_of_ratio_forms (coarseA_spec c z L hc).1 (coarseA_spec c' z L hc').1 hΓ
      (coarseA_form_nonneg c' z L hc') hA2 hA1,
    opNorm_sub_le_of_ratio_forms (coarseB_spec c z L hc).1 (coarseB_spec c' z L hc').1 hΓ
      (coarseB_form_nonneg c' z L hc') hB1 hB2⟩

/-! ## Cells of a cube -/

/-- The unit cells of the cube `z + {0,…,L}^d`, by their lower corners `z + {0,…,L-1}^d`. -/
def cubeCells (z : Site d) (L : ℕ) : Finset (Site d) :=
  Fintype.piFinset fun i => Finset.Ico (z i) (z i + (L : ℤ))

/-- A site lies in the cells of the cube `z + {0, …, L}^d` exactly when its coordinates lie in the
half-open ranges `[z_i, z_i + L)`. -/
lemma mem_cubeCells_iff_coord (z x : Site d) (L : ℕ) :
    x ∈ cubeCells z L ↔ ∀ i, z i ≤ x i ∧ x i < z i + (L : ℤ) := by
  simp only [cubeCells, Fintype.mem_piFinset, Finset.mem_Ico]

/-! ## The bilinear energy -/

/-- The bilinear energy `ℰ_□(u, v) = L^{-d} Σ_{e ⊂ □} w_□(e) c_e ∇u(e) ∇v(e)` (the polarization
of `cubeEnergy`, Appendix A.1, `ss:coarse-def`). -/
def cubeBilin (c : Edge d → ℝ) (z : Site d) (L : ℕ) (u v : Site d → ℝ) : ℝ :=
  ((L : ℝ) ^ d)⁻¹ * ∑ e ∈ edgesOf z L,
    faceWeight z L e * c e * ((u e.tgt - u e.src) * (v e.tgt - v e.src))

/-- `ℰ_□(u, u) = ℰ_□(u)`. -/
theorem cubeBilin_self (c : Edge d → ℝ) (z : Site d) (L : ℕ) (u : Site d → ℝ) :
    cubeBilin c z L u u = cubeEnergy c z L u := by
  unfold cubeBilin cubeEnergy
  congr 1
  refine Finset.sum_congr rfl fun e _ => by ring

/-! ## The effective conductivity -/

/-- `A_*` is symmetric: `p·A_*q = ⟨F_p, F_q⟩_c` is a real inner product. Proof: entries are
`⟪F_{e_i}, F_{e_j}⟫`, `real_inner_comm`. -/
theorem effConductivity_isSymm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (τ : LatticeAction d μ) {c : Ω → Edge d → ℝ} (hcm : ∀ e, Measurable fun ω => c ω e)
    (hint : ∀ j, Integrable (fun ω => c ω (0, j)) μ) :
    (effConductivity τ c hcm hint).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, effConductivity]
  exact real_inner_comm _ _

/-- A limit argument: `x ≤ y + K L^{-κ}` for all `L ≥ 2` gives `x ≤ y`. -/
theorem le_of_forall_add_rpow_neg {x y K κ : ℝ} (hκ : 0 < κ)
    (h : ∀ L : ℕ, 2 ≤ L → x ≤ y + K * (L : ℝ) ^ (-κ)) : x ≤ y := by
  have ht : Tendsto (fun L : ℕ => y + K * (L : ℝ) ^ (-κ)) atTop (𝓝 (y + K * 0)) :=
    tendsto_const_nhds.add
      ((((tendsto_rpow_neg_atTop hκ).comp tendsto_natCast_atTop_atTop)).const_mul K)
  rw [mul_zero, add_zero] at ht
  exact ge_of_tendsto ht (Filter.eventually_atTop.2 ⟨2, h⟩)

end LatticeHC

end
