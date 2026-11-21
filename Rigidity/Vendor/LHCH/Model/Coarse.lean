/-
Copied from Lattice-High-Contrast-Homogenization (https://github.com/nitromannitol/Lattice-High-Contrast-Homogenization),
commit f47a932a9f7a07e1692bfe4aae564d02e8ca0944, file `LatticeHC/Model/Coarse.lean` (Apache License 2.0,
Copyright 2026 Ahmed Bou-Rabee and Yuval Peres).
Changes: imports `LatticeHC.*` renamed to `Rigidity.Vendor.LHCH.*`; namespace `LatticeHC` kept.
-/
import Rigidity.Vendor.LHCH.Model.Lattice

/-!
# The coarse-grained matrices of a lattice cube

The objects of Appendix A.1 (`e:energy`, `e:AB`) for a field `c` of conductances and a lattice
cube `□ = z + {0, …, L}^d`.
* The face weight of an edge `e ⊂ □` is `w_□(e) = 2^{-k(e)}`, where `k(e)` is the number of
  `(d-1)`-dimensional faces of `□` containing `e`.
* The energy is `ℰ_□(u) = L^{-d} Σ_{e ⊂ □} w_□(e) c_e |∇u(e)|²`, and the mean gradient is
  `𝒢_□(u) = L^{-d} Σ_{e ⊂ □} w_□(e) ∇u(e) e_{j(e)}`.
* The coarse-grained matrices `A_□` and `B_□` are characterized, for `p, q ∈ ℝ^d`, by
  `p · A_□ p = min {ℰ_□(u) : u = p · x on the vertex boundary of □}` and
  `q · B_□ q = max_u {2 q · 𝒢_□(u) - ℰ_□(u)}`.

`A_□` and `B_□` are defined by characterization, so each is constructed from a proved `∃!` theorem:
there is exactly one symmetric matrix with the given quadratic form. The minimum and the maximum are
attained (`IsLeast`, `IsGreatest`). The theorems need the conductances to be positive on the edges
of `□`, which is an argument of the definitions.

An edge `(x, j)` lies in the face `{y_i = a}` of `□` exactly when `i ≠ j` and `x_i = a`.
-/

namespace LatticeHC

open LatticeProb Matrix

noncomputable section

variable {d : ℕ}

open Classical in
/-- The edges `e ⊂ □` of the lattice cube `□ = z + {0, …, L}^d`: both endpoints in `□`. -/
def edgesOf (z : Site d) (L : ℕ) : Finset (Edge d) :=
  (latticeCube z L ×ˢ Finset.univ).filter fun e => e.tgt ∈ latticeCube z L

open Classical in
/-- The number `k(e)` of `(d-1)`-dimensional faces of `□ = z + {0, …, L}^d` that contain `e`. -/
def faceCount (z : Site d) (L : ℕ) (e : Edge d) : ℕ :=
  (Finset.univ.filter fun i : Fin d => i ≠ e.2 ∧ (e.1 i = z i ∨ e.1 i = z i + L)).card

/-- The face weight `w_□(e) = 2^{-k(e)}` (Appendix A.1, `ss:coarse-def`). -/
def faceWeight (z : Site d) (L : ℕ) (e : Edge d) : ℝ := (1 / 2 : ℝ) ^ faceCount z L e

/-- The energy per unit volume `ℰ_□(u) = L^{-d} Σ_{e ⊂ □} w_□(e) c_e |∇u(e)|²` (`(e:energy)`). -/
def cubeEnergy (c : Edge d → ℝ) (z : Site d) (L : ℕ) (u : Site d → ℝ) : ℝ :=
  ((L : ℝ) ^ d)⁻¹ * ∑ e ∈ edgesOf z L, faceWeight z L e * c e * (u e.tgt - u e.src) ^ 2

/-- The mean gradient `𝒢_□(u) = L^{-d} Σ_{e ⊂ □} w_□(e) ∇u(e) e_{j(e)}` (`(e:energy)`). -/
def cubeMeanGrad (z : Site d) (L : ℕ) (u : Site d → ℝ) : Fin d → ℝ :=
  fun j => ((L : ℝ) ^ d)⁻¹ *
    ∑ e ∈ (edgesOf z L).filter (fun e => e.2 = j), faceWeight z L e * (u e.tgt - u e.src)

open Classical in
/-- The vertex boundary of `□`: its vertices with a neighbour outside `□` (§1.1). -/
def vertexBoundary (z : Site d) (L : ℕ) : Finset (Site d) :=
  (latticeCube z L).filter fun x => ∃ y ∈ nbrFinset x, y ∉ latticeCube z L

/-- The affine function `x ↦ p · x` on the lattice. -/
def affine (p : Fin d → ℝ) (x : Site d) : ℝ := ∑ i, p i * (x i : ℝ)

/-- A linear map from `ℝ^d` into an inner product space gives a symmetric matrix whose quadratic
form is the squared norm. -/
private lemma exists_symm_dotProduct_eq_norm_sq {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (S : (Fin d → ℝ) →ₗ[ℝ] F) :
    ∃ A : Matrix (Fin d) (Fin d) ℝ, A.IsSymm ∧ ∀ p, p ⬝ᵥ (A *ᵥ p) = ‖S p‖ ^ 2 := by
  classical
  refine ⟨Matrix.of fun i j => inner ℝ (S (Pi.single i 1)) (S (Pi.single j 1)), ?_, ?_⟩
  · ext i j
    simp [real_inner_comm]
  · intro p
    have hp : p = ∑ i, p i • (Pi.single i 1 : Fin d → ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    have hS : S p = ∑ i, p i • S (Pi.single i 1) := by
      conv_lhs => rw [hp]
      simp only [map_sum, map_smul]
    rw [← real_inner_self_eq_norm_sq, hS]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm]
    ring

/-- A symmetric matrix is determined by its quadratic form. -/
private lemma eq_of_dotProduct_eq {A A' : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsSymm)
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
  simp only [col_apply] at h1 h2 h3
  linarith

/-- The Dirichlet principle for a quadratic form `‖T u‖²` on the affine spaces `A₀ p + W`: the
minimum is attained and is the quadratic form of a symmetric matrix. -/
private lemma exists_isLeast_norm_sq {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T : E →ₗ[ℝ] F) (W : Submodule ℝ E) (A₀ : (Fin d → ℝ) →ₗ[ℝ] E) :
    ∃ A : Matrix (Fin d) (Fin d) ℝ, A.IsSymm ∧ ∀ p,
      IsLeast {r | ∃ u, u - A₀ p ∈ W ∧ r = ‖T u‖ ^ 2} (p ⬝ᵥ (A *ᵥ p)) := by
  classical
  set K : Submodule ℝ F := W.map T with hK
  let P : F →ₗ[ℝ] F := (K.starProjection : F →L[ℝ] F)
  let S : (Fin d → ℝ) →ₗ[ℝ] F := (LinearMap.id - P) ∘ₗ T ∘ₗ A₀
  obtain ⟨A, hA, hAp⟩ := exists_symm_dotProduct_eq_norm_sq S
  refine ⟨A, hA, fun p => ?_⟩
  rw [hAp]
  have hS : S p = T (A₀ p) - K.starProjection (T (A₀ p)) := rfl
  constructor
  · obtain ⟨v, hv, hvT⟩ := (Submodule.mem_map).1 (K.starProjection_apply_mem (T (A₀ p)))
    refine ⟨A₀ p - v, ?_, ?_⟩
    · simpa using W.neg_mem hv
    · rw [hS, map_sub, hvT]
  · rintro r ⟨u, hu, rfl⟩
    have hk : T (u - A₀ p) ∈ K := ⟨_, hu, rfl⟩
    have hmem : K.starProjection (T (A₀ p)) + T (u - A₀ p) ∈ K :=
      K.add_mem (K.starProjection_apply_mem _) hk
    have hTu : T u = S p + (K.starProjection (T (A₀ p)) + T (u - A₀ p)) := by
      rw [hS, map_sub]
      abel
    have horth : inner ℝ (S p) (K.starProjection (T (A₀ p)) + T (u - A₀ p)) = 0 := by
      rw [hS]
      exact K.starProjection_inner_eq_zero _ _ hmem
    rw [hTu, norm_add_sq_real, horth]
    nlinarith [sq_nonneg ‖K.starProjection (T (A₀ p)) + T (u - A₀ p)‖]

/-- The Neumann principle for the objective `2 ⟪G q, T u⟫ - ‖T u‖²`: the maximum is attained and is
the quadratic form of a symmetric matrix. -/
private lemma exists_isGreatest_norm_sq {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (T : E →ₗ[ℝ] F) (G : (Fin d → ℝ) →ₗ[ℝ] F) :
    ∃ B : Matrix (Fin d) (Fin d) ℝ, B.IsSymm ∧ ∀ q,
      IsGreatest {r | ∃ u, r = 2 * inner ℝ (G q) (T u) - ‖T u‖ ^ 2} (q ⬝ᵥ (B *ᵥ q)) := by
  classical
  set R : Submodule ℝ F := LinearMap.range T with hR
  let P : F →ₗ[ℝ] F := (R.starProjection : F →L[ℝ] F)
  let S : (Fin d → ℝ) →ₗ[ℝ] F := P ∘ₗ G
  obtain ⟨B, hB, hBq⟩ := exists_symm_dotProduct_eq_norm_sq S
  refine ⟨B, hB, fun q => ?_⟩
  rw [hBq]
  have hS : S q = R.starProjection (G q) := rfl
  have horth : ∀ w ∈ R, inner ℝ (G q) w = inner ℝ (S q) w := by
    intro w hw
    have h := R.starProjection_inner_eq_zero (G q) w hw
    rw [inner_sub_left, sub_eq_zero] at h
    rw [hS]
    exact h
  constructor
  · obtain ⟨u, hu⟩ := LinearMap.mem_range.1 (R.starProjection_apply_mem (G q))
    refine ⟨u, ?_⟩
    rw [horth (T u) ⟨u, rfl⟩, hu, ← hS, real_inner_self_eq_norm_sq]
    ring
  · rintro r ⟨u, rfl⟩
    rw [horth (T u) ⟨u, rfl⟩]
    nlinarith [norm_sub_sq_real (S q) (T u), sq_nonneg ‖S q - T u‖]

/-- The cube `z + {0}^d` is the single site `z`. -/
private lemma eq_of_mem_latticeCube_zero {z x : Site d} (hx : x ∈ latticeCube z 0) : x = z := by
  simp only [latticeCube, qbox, Finset.mem_image, Fintype.mem_piFinset, Finset.mem_Icc,
    Nat.cast_zero] at hx
  obtain ⟨w, hw, rfl⟩ := hx
  have : w = 0 := funext fun i => le_antisymm (hw i).2 (hw i).1
  simp [this]

/-- The side of a cube containing an edge is positive, so `L ^ d` is a positive real. -/
private lemma natCast_pow_pos_of_mem_edgesOf {z : Site d} {L : ℕ} {e : Edge d}
    (he : e ∈ edgesOf z L) : 0 < ((L : ℝ) ^ d) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · exfalso
    simp only [edgesOf, Finset.mem_filter, Finset.mem_product] at he
    have h1 := eq_of_mem_latticeCube_zero he.1.1
    have h2 := eq_of_mem_latticeCube_zero he.2
    have h3 : e.tgt = e.src + unit e.2 := rfl
    have h4 : e.src = z := h1
    rw [h2, h4] at h3
    exact unit_ne_zero e.2 (by simpa using h3.symm)
  · positivity

/-- The weighted gradient map and the mean-gradient map of a lattice cube: the energy is the squared
norm of the weighted gradient `T u`, and the pairing of `q` with the mean gradient is an inner
product. -/
private lemma exists_gradMap (c : Edge d → ℝ) (z : Site d) (L : ℕ)
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) :
    ∃ (T : (Site d → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (edgesOf z L))
      (G : (Fin d → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (edgesOf z L)),
      (∀ u, cubeEnergy c z L u = ‖T u‖ ^ 2) ∧
      ∀ q u, q ⬝ᵥ cubeMeanGrad z L u = inner ℝ (G q) (T u) := by
  classical
  set a : Edge d → ℝ := fun e => ((L : ℝ) ^ d)⁻¹ * (faceWeight z L e * c e) with ha
  have hw : ∀ e, 0 < faceWeight z L e := fun e => by unfold faceWeight; positivity
  have ha0 : ∀ e ∈ edgesOf z L, 0 ≤ a e := fun e he => by
    have := hc e he
    have := hw e
    simp only [ha]
    positivity
  have ha1 : ∀ e ∈ edgesOf z L, 0 < a e := fun e he => by
    have := hc e he
    have := hw e
    have := natCast_pow_pos_of_mem_edgesOf he
    simp only [ha]
    positivity
  let T : (Site d → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (edgesOf z L) :=
    { toFun := fun u => WithLp.toLp 2 fun e => Real.sqrt (a e.1) * (u e.1.tgt - u e.1.src)
      map_add' := fun u v => by
        ext e
        simp only [Pi.add_apply, PiLp.add_apply]
        ring
      map_smul' := fun r u => by
        ext e
        simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  let G : (Fin d → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (edgesOf z L) :=
    { toFun := fun q => WithLp.toLp 2 fun e =>
        ((L : ℝ) ^ d)⁻¹ * faceWeight z L e.1 * q e.1.2 / Real.sqrt (a e.1)
      map_add' := fun q q' => by
        ext e
        simp only [Pi.add_apply, PiLp.add_apply]
        ring
      map_smul' := fun r q => by
        ext e
        simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  refine ⟨T, G, fun u => ?_, fun q u => ?_⟩
  · rw [EuclideanSpace.norm_sq_eq]
    have h1 : ∑ e : ↥(edgesOf z L), ‖(T u).ofLp e‖ ^ 2 =
        ∑ e : ↥(edgesOf z L), a e.1 * (u e.1.tgt - u e.1.src) ^ 2 := by
      refine Finset.sum_congr rfl fun e _ => ?_
      show ‖Real.sqrt (a e.1) * (u e.1.tgt - u e.1.src)‖ ^ 2 = _
      rw [Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (ha0 e.1 e.2)]
    rw [h1, cubeEnergy, Finset.mul_sum, ← Finset.sum_coe_sort (edgesOf z L)]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [ha]
    ring
  · have hR : ∑ i, inner ℝ ((G q).ofLp i) ((T u).ofLp i) = ∑ e ∈ edgesOf z L,
        ((L : ℝ) ^ d)⁻¹ * (faceWeight z L e * q e.2 * (u e.tgt - u e.src)) := by
      rw [← Finset.sum_coe_sort (edgesOf z L)]
      refine Finset.sum_congr rfl fun e _ => ?_
      have hne : Real.sqrt (a e.1) ≠ 0 := (Real.sqrt_pos.2 (ha1 e.1 e.2)).ne'
      show inner ℝ (((L : ℝ) ^ d)⁻¹ * faceWeight z L e.1 * q e.1.2 / Real.sqrt (a e.1))
        (Real.sqrt (a e.1) * (u e.1.tgt - u e.1.src)) = _
      rw [Real.inner_apply]
      field_simp
    rw [PiLp.inner_apply, hR, ← Finset.sum_fiberwise (edgesOf z L) (fun e => e.2), dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [cubeMeanGrad, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [(Finset.mem_filter.1 he).2]
    ring

/-- `A_□` is well defined (`(e:AB)`): for conductances positive on the edges of `□`, there is
exactly one symmetric matrix `A` with `p · A p = min {ℰ_□(u) : u = p · x on the vertex boundary}`
for every `p`, the minimum being attained. -/
theorem existsUnique_coarseA (c : Edge d → ℝ) (z : Site d) (L : ℕ)
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) :
    ∃! A : Matrix (Fin d) (Fin d) ℝ, A.IsSymm ∧ ∀ p : Fin d → ℝ,
      IsLeast {E | ∃ u : Site d → ℝ, (∀ x ∈ vertexBoundary z L, u x = affine p x) ∧
        E = cubeEnergy c z L u} (p ⬝ᵥ (A *ᵥ p)) := by
  classical
  obtain ⟨T, G, hT, -⟩ := exists_gradMap c z L hc
  let W : Submodule ℝ (Site d → ℝ) :=
    { carrier := {v | ∀ x ∈ vertexBoundary z L, v x = 0}
      add_mem' := fun ha hb x hx => by simp only [Pi.add_apply, ha x hx, hb x hx, add_zero]
      zero_mem' := fun _ _ => rfl
      smul_mem' := fun r v hv x hx => by simp only [Pi.smul_apply, hv x hx, smul_zero] }
  let A₀ : (Fin d → ℝ) →ₗ[ℝ] (Site d → ℝ) :=
    { toFun := fun p x => affine p x
      map_add' := fun p p' => by
        ext x
        simp only [affine, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun r p => by
        ext x
        simp only [affine, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum,
          mul_assoc] }
  obtain ⟨A, hA, hAp⟩ := exists_isLeast_norm_sq T W A₀
  have hset : ∀ p : Fin d → ℝ, {E | ∃ u : Site d → ℝ,
      (∀ x ∈ vertexBoundary z L, u x = affine p x) ∧ E = cubeEnergy c z L u} =
      {r | ∃ u, u - A₀ p ∈ W ∧ r = ‖T u‖ ^ 2} := by
    intro p
    ext r
    simp only [Set.mem_setOf_eq, hT]
    refine exists_congr fun u => and_congr ?_ Iff.rfl
    refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
    · show u x - affine p x = 0
      rw [h x hx, sub_self]
    · exact sub_eq_zero.1 (h x hx)
  have hleast : ∀ p : Fin d → ℝ, IsLeast {E | ∃ u : Site d → ℝ,
      (∀ x ∈ vertexBoundary z L, u x = affine p x) ∧ E = cubeEnergy c z L u}
      (p ⬝ᵥ (A *ᵥ p)) := fun p => by
    rw [hset p]
    exact hAp p
  refine ⟨A, ⟨hA, hleast⟩, fun A' hA' => ?_⟩
  exact eq_of_dotProduct_eq hA'.1 hA fun p => (hA'.2 p).unique (hleast p)

/-- `B_□` is well defined (`(e:AB)`): for conductances positive on the edges of `□`, there is
exactly one symmetric matrix `B` with `q · B q = max_u {2 q · 𝒢_□(u) - ℰ_□(u)}` for every `q`, the
maximum being attained. -/
theorem existsUnique_coarseB (c : Edge d → ℝ) (z : Site d) (L : ℕ)
    (hc : ∀ e ∈ edgesOf z L, 0 < c e) :
    ∃! B : Matrix (Fin d) (Fin d) ℝ, B.IsSymm ∧ ∀ q : Fin d → ℝ,
      IsGreatest {E | ∃ u : Site d → ℝ,
        E = 2 * (q ⬝ᵥ cubeMeanGrad z L u) - cubeEnergy c z L u} (q ⬝ᵥ (B *ᵥ q)) := by
  obtain ⟨T, G, hT, hG⟩ := exists_gradMap c z L hc
  obtain ⟨B, hB, hBq⟩ := exists_isGreatest_norm_sq T G
  have hgreatest : ∀ q : Fin d → ℝ, IsGreatest {E | ∃ u : Site d → ℝ,
      E = 2 * (q ⬝ᵥ cubeMeanGrad z L u) - cubeEnergy c z L u} (q ⬝ᵥ (B *ᵥ q)) := fun q => by
    have hset : {E | ∃ u : Site d → ℝ,
        E = 2 * (q ⬝ᵥ cubeMeanGrad z L u) - cubeEnergy c z L u} =
        {r | ∃ u, r = 2 * inner ℝ (G q) (T u) - ‖T u‖ ^ 2} := by
      ext r
      simp only [Set.mem_setOf_eq, hT, hG]
    rw [hset]
    exact hBq q
  refine ⟨B, ⟨hB, hgreatest⟩, fun B' hB' => ?_⟩
  exact eq_of_dotProduct_eq hB'.1 hB fun q => (hB'.2 q).unique (hgreatest q)

/-- The coarse-grained matrix `A_□` of `c` on `□ = z + {0, …, L}^d` (`(e:AB)`). -/
def coarseA (c : Edge d → ℝ) (z : Site d) (L : ℕ) (hc : ∀ e ∈ edgesOf z L, 0 < c e) :
    Matrix (Fin d) (Fin d) ℝ :=
  (existsUnique_coarseA c z L hc).exists.choose

/-- The coarse-grained matrix `B_□` of `c` on `□ = z + {0, …, L}^d` (`(e:AB)`). -/
def coarseB (c : Edge d → ℝ) (z : Site d) (L : ℕ) (hc : ∀ e ∈ edgesOf z L, 0 < c e) :
    Matrix (Fin d) (Fin d) ℝ :=
  (existsUnique_coarseB c z L hc).exists.choose

/-- The characterization of `A_□`: it is symmetric, and `p · A_□ p` is the minimal energy with
boundary values `p · x`. -/
theorem coarseA_spec (c : Edge d → ℝ) (z : Site d) (L : ℕ) (hc : ∀ e ∈ edgesOf z L, 0 < c e) :
    (coarseA c z L hc).IsSymm ∧ ∀ p : Fin d → ℝ,
      IsLeast {E | ∃ u : Site d → ℝ, (∀ x ∈ vertexBoundary z L, u x = affine p x) ∧
        E = cubeEnergy c z L u} (p ⬝ᵥ (coarseA c z L hc *ᵥ p)) :=
  (existsUnique_coarseA c z L hc).exists.choose_spec

/-- The characterization of `B_□`: it is symmetric, and `q · B_□ q` is the maximum of
`2 q · 𝒢_□(u) - ℰ_□(u)`. -/
theorem coarseB_spec (c : Edge d → ℝ) (z : Site d) (L : ℕ) (hc : ∀ e ∈ edgesOf z L, 0 < c e) :
    (coarseB c z L hc).IsSymm ∧ ∀ q : Fin d → ℝ,
      IsGreatest {E | ∃ u : Site d → ℝ,
        E = 2 * (q ⬝ᵥ cubeMeanGrad z L u) - cubeEnergy c z L u} (q ⬝ᵥ (coarseB c z L hc *ᵥ q)) :=
  (existsUnique_coarseB c z L hc).exists.choose_spec

end

end LatticeHC
