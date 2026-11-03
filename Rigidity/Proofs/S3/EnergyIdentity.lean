import Rigidity.Proofs.S3.Divergence

/-!
# The energy identity of the corrected plane on boxes

Deterministic part of the proof of `HomogenizedCoefficientProposed` (defined in
`Proofs/S3/FluxEvent.lean`, proved in `Proofs/S3/HomogenizedCoefficient.lean`): the box form of
the identity `E[X] = E[Σ_i (∇_{e_i} ℓ)² 1{0 ∈ C, {0, e_i} open}]` between the mean of the
horizontal edge difference `X = ℓ(e₁) - ℓ(0)` of the corrected plane `ℓ = ℓ_{e₁}` and its energy
density.

Write `∇(x, y) = edgeDifference C u x y = (u(x) - u(y)) 1{x ∈ C, {x, y} open}`.

* **Green's identity on a finite set** (`sum_mul_nbrSum_eq`). For an antisymmetric `f` and any
  `g`, summing `g(x) Σ_i (f(x, x + e_i) + f(x, x - e_i))` over a finite set `A` gives the sum of
  `(g(x) - g(x + e_i)) f(x, x + e_i)` over the edges `{x, x + e_i}` inside `A` plus the sum of
  `g(x) f(x, y)` over the oriented edges `(x, y)` leaving `A`.
* **The energy identity** (`boxEnergy_eq`). For `u` harmonic on the cluster, take `f = ∇` and the
  test function `g(x) = u(x) - x₁ - c`: on an edge inside the cluster,
  `(g(x) - g(x + e_i)) ∇(x, x + e_i) = ∇(x, x + e_i)² + 1{i = 1} ∇(x, x + e₁)`, so
  `Σ_{edges in A} ∇² = Σ_{x, x + e₁ ∈ A} ∇(x + e₁, x) - Σ_{(x, y) leaving A} (u(x) - x₁ - c) ∇(x, y)`.
  The test function `x₁` turns the boundary term `Σ ℓ · flux` into the bulk sum of the horizontal
  differences, so no face average weighted by `x₁` has to be controlled.
* **The boundary remainder** (`abs_boundaryTerm_le`) is at most
  `sup_{A ∩ C} |u - x₁ - c|` times the total absolute flux out of `A`; on the cube `Q_N` the
  sublinearity of a corrected plane of slope `e₁` (`IsCorrectedPlane`) makes the supremum at most
  `ε N` for large `N` (`abs_sub_coord_le_of_isCorrectedPlane`), giving
  `|boxEnergy - boxDrift| ≤ ε N · boundaryFlux` (`abs_boxEnergy_sub_boxDrift_le`).
* **Faces of the cube** (`boxEnergy_latticeCube`, `boxDrift_latticeCube`,
  `boundaryFlux_latticeCube`): on `Q_N` the three sums are full cube sums of the stationary fields
  `Σ_i ∇(x, x + e_i)²` and `∇(x + e₁, x)` minus sums over the faces `x_i = N`, and the flux out of
  `Q_N` is a sum over the faces `x_i = ±N`; the ergodic limit is taken on these forms.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Rigidity.Proofs.S3

open LatticeProb LatticeProb.Percolation Rigidity.Section3 Rigidity.Steps.S3 Classical

variable {d : ℕ}

/-! ### Green's identity on a finite set -/

section Green

/-- Green's identity in the direction `e_i`: the edges `{x, x + e_i}` inside `A` are counted from
both endpoints, the oriented edges leaving `A` once. -/
theorem sum_mul_dir_eq (A : Finset (Vertex d)) (f : Vertex d → Vertex d → ℝ)
    (hanti : ∀ x y, f y x = - f x y) (g : Vertex d → ℝ) (i : Fin d) :
    ∑ x ∈ A, g x * (f x (x + unit i) + f x (x - unit i)) =
      ∑ x ∈ A, (if x + unit i ∈ A then (g x - g (x + unit i)) * f x (x + unit i) else 0) +
        ∑ x ∈ A, ((if x + unit i ∈ A then 0 else g x * f x (x + unit i)) +
          (if x - unit i ∈ A then 0 else g x * f x (x - unit i))) := by
  have hcancel : ∑ x ∈ A.filter (fun x => x - unit i ∈ A), g x * f x (x - unit i) =
      ∑ x ∈ A.filter (fun x => x + unit i ∈ A), - (g (x + unit i) * f x (x + unit i)) := by
    refine Finset.sum_nbij' (fun x => x - unit i) (fun x => x + unit i) ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.2, by rw [sub_add_cancel]; exact hx.1⟩
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.2, by rw [add_sub_cancel_right]; exact hx.1⟩
    · intro x _
      exact sub_add_cancel x (unit i)
    · intro x _
      exact add_sub_cancel_right x (unit i)
    · intro x _
      rw [sub_add_cancel, hanti]
      ring
  have h1 := Finset.sum_filter_add_sum_filter_not A (fun x => x + unit i ∈ A)
    (fun x => g x * f x (x + unit i))
  have h2 := Finset.sum_filter_add_sum_filter_not A (fun x => x - unit i ∈ A)
    (fun x => g x * f x (x - unit i))
  simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero, zero_add, add_zero,
    mul_add, sub_mul]
  rw [Finset.sum_sub_distrib, ← h1, ← h2, hcancel, Finset.sum_neg_distrib]
  ring

/-- **Green's identity on a finite set.** -/
theorem sum_mul_nbrSum_eq (A : Finset (Vertex d)) (f : Vertex d → Vertex d → ℝ)
    (hanti : ∀ x y, f y x = - f x y) (g : Vertex d → ℝ) :
    ∑ x ∈ A, g x * ∑ i, (f x (x + unit i) + f x (x - unit i)) =
      ∑ x ∈ A, ∑ i,
          (if x + unit i ∈ A then (g x - g (x + unit i)) * f x (x + unit i) else 0) +
        ∑ x ∈ A, ∑ i, ((if x + unit i ∈ A then 0 else g x * f x (x + unit i)) +
          (if x - unit i ∈ A then 0 else g x * f x (x - unit i))) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := A) (t := Finset.univ),
    Finset.sum_comm (s := A) (t := Finset.univ), ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => sum_mul_dir_eq A f hanti g i

end Green

/-! ### The energy identity -/

section Energy

variable {ω : Configuration d}

/-- The Dirichlet energy of `u` on the open edges of the cluster `C` with both endpoints in `A`:
`Σ ∇(x, x + e_i)²` over the edges `{x, x + e_i}` with `x, x + e_i ∈ A`. -/
noncomputable def boxEnergy (C : OpenComponent ω) (u : C → ℝ) (A : Finset (Vertex d)) : ℝ :=
  ∑ x ∈ A, ∑ i, if x + unit i ∈ A then edgeDifference C u x (x + unit i) ^ 2 else 0

/-- The sum of the horizontal differences `∇(x + e₁, x) = u(x + e₁) - u(x)` over the open edges
`{x, x + e₁}` of the cluster with both endpoints in `A`; at `x = 0` this is the variable `X` of
`HomogenizedCoefficientProposed`. -/
noncomputable def boxDrift [NeZero d] (C : OpenComponent ω) (u : C → ℝ) (A : Finset (Vertex d)) :
    ℝ :=
  ∑ x ∈ A, if x + unit 0 ∈ A then edgeDifference C u (x + unit 0) x else 0

/-- The boundary term `Σ g(x) ∇(x, y)` over the oriented edges `(x, y) = (x, x ± e_i)` leaving
`A`. -/
noncomputable def boundaryTerm (C : OpenComponent ω) (u : C → ℝ) (A : Finset (Vertex d))
    (g : Vertex d → ℝ) : ℝ :=
  ∑ x ∈ A, ∑ i, ((if x + unit i ∈ A then 0 else g x * edgeDifference C u x (x + unit i)) +
    (if x - unit i ∈ A then 0 else g x * edgeDifference C u x (x - unit i)))

/-- The total absolute flux `Σ |∇(x, y)|` of `u` over the oriented edges `(x, y)` leaving `A`. -/
noncomputable def boundaryFlux (C : OpenComponent ω) (u : C → ℝ) (A : Finset (Vertex d)) : ℝ :=
  ∑ x ∈ A, ∑ i, ((if x + unit i ∈ A then 0 else |edgeDifference C u x (x + unit i)|) +
    (if x - unit i ∈ A then 0 else |edgeDifference C u x (x - unit i)|))

/-- The deviation `u(x) - x₁ - c` of `u` from the plane of slope `e₁` (zero-extended off `C`). -/
noncomputable def planeDeviation [NeZero d] (C : OpenComponent ω) (u : C → ℝ) (c : ℝ)
    (x : Vertex d) : ℝ :=
  extend C u x - (x 0 : ℝ) - c

/-- On an edge `{x, x + e_i}`: `(g(x) - g(x + e_i)) ∇(x, x + e_i) = ∇² + 1{i = 1} ∇` for the
deviation `g` from the plane of slope `e₁`. -/
theorem planeDeviation_sub_mul_edgeDifference [NeZero d] (C : OpenComponent ω) (u : C → ℝ)
    (c : ℝ) (x : Vertex d) (i : Fin d) :
    (planeDeviation C u c x - planeDeviation C u c (x + unit i)) *
        edgeDifference C u x (x + unit i) =
      edgeDifference C u x (x + unit i) ^ 2 +
        if i = 0 then edgeDifference C u x (x + unit i) else 0 := by
  have hc : ((x + unit i) 0 : ℝ) = (x 0 : ℝ) + if i = 0 then 1 else 0 := by
    rw [add_unit_apply]
    by_cases h : i = 0
    · subst h
      simp
    · simp [Ne.symm h, h]
  unfold planeDeviation edgeDifference
  rw [hc]
  split_ifs <;> ring

/-- **The energy identity.** For `u` harmonic on the cluster, a finite set `A` and a constant
`c`: the energy of `u` on the edges inside `A` is the sum of its horizontal differences inside `A`
minus the boundary term of the deviation `u - x₁ - c` against the flux out of `A`. -/
theorem boxEnergy_eq [NeZero d] (C : OpenComponent ω) (u : C → ℝ)
    (hu : ∀ x, componentLaplacian C u x = 0) (A : Finset (Vertex d)) (c : ℝ) :
    boxEnergy C u A = boxDrift C u A - boundaryTerm C u A (planeDeviation C u c) := by
  have h := sum_mul_nbrSum_eq A (edgeDifference C u) (edgeDifference_antisymm C u)
    (planeDeviation C u c)
  simp only [edgeDifference_nbrSum_eq_zero C u hu, mul_zero, Finset.sum_const_zero] at h
  have hbulk : ∑ x ∈ A, ∑ i, (if x + unit i ∈ A then
        (planeDeviation C u c x - planeDeviation C u c (x + unit i)) *
          edgeDifference C u x (x + unit i) else 0) =
      boxEnergy C u A - boxDrift C u A := by
    unfold boxEnergy boxDrift
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hsplit : ∀ i : Fin d, (if x + unit i ∈ A then
          (planeDeviation C u c x - planeDeviation C u c (x + unit i)) *
            edgeDifference C u x (x + unit i) else 0) =
        (if x + unit i ∈ A then edgeDifference C u x (x + unit i) ^ 2 else 0) +
          if i = 0 then
            (if x + unit i ∈ A then edgeDifference C u x (x + unit i) else 0) else 0 := by
      intro i
      rw [planeDeviation_sub_mul_edgeDifference]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ (0 : Fin d), if_pos (Finset.mem_univ _),
      edgeDifference_antisymm C u x (x + unit 0)]
    split_ifs <;> ring
  unfold boundaryTerm
  linarith

/-- A term `g(x) ∇(x, y)` is at most `M |∇(x, y)|` when `|g| ≤ M` on the cluster. -/
theorem abs_mul_edgeDifference_le (C : OpenComponent ω) (u : C → ℝ) (g : Vertex d → ℝ) {M : ℝ}
    {x : Vertex d} (hg : x ∈ C.supp → |g x| ≤ M) (y : Vertex d) :
    |g x * edgeDifference C u x y| ≤ M * |edgeDifference C u x y| := by
  by_cases h : x ∈ C.supp ∧ (openGraph ω).Adj x y
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hg h.1) (abs_nonneg _)
  · have h0 : edgeDifference C u x y = 0 := by
      unfold edgeDifference
      rw [if_neg h]
    simp [h0]

/-- **The boundary remainder**: at most the supremum of `|g|` over `A ∩ C` times the total absolute
flux out of `A`. -/
theorem abs_boundaryTerm_le (C : OpenComponent ω) (u : C → ℝ) (A : Finset (Vertex d))
    (g : Vertex d → ℝ) {M : ℝ} (hg : ∀ x ∈ A, x ∈ C.supp → |g x| ≤ M) :
    |boundaryTerm C u A g| ≤ M * boundaryFlux C u A := by
  unfold boundaryTerm boundaryFlux
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [mul_add]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_) <;> split_ifs <;>
    first
    | exact abs_mul_edgeDifference_le C u g (hg x hx) _
    | simp

end Energy

/-! ### The cube `Q_N` -/

section Cube

variable {ω : Configuration d} {N : ℕ}

theorem add_unit_mem_latticeCube_iff {x : Vertex d} (hx : x ∈ latticeCube d N) (i : Fin d) :
    x + unit i ∈ latticeCube d N ↔ x i ≠ N := by
  simp only [latticeCube, Fintype.mem_piFinset, Finset.mem_Icc] at hx ⊢
  constructor
  · intro h
    have hi := h i
    rw [add_unit_apply, if_pos rfl] at hi
    omega
  · intro h j
    obtain ⟨h1, h2⟩ := hx j
    rw [add_unit_apply]
    split_ifs with hj
    · subst hj
      omega
    · exact ⟨h1, h2⟩

theorem sub_unit_mem_latticeCube_iff {x : Vertex d} (hx : x ∈ latticeCube d N) (i : Fin d) :
    x - unit i ∈ latticeCube d N ↔ x i ≠ -(N : ℤ) := by
  simp only [latticeCube, Fintype.mem_piFinset, Finset.mem_Icc] at hx ⊢
  constructor
  · intro h
    have hi := h i
    rw [sub_unit_apply, if_pos rfl] at hi
    omega
  · intro h j
    obtain ⟨h1, h2⟩ := hx j
    rw [sub_unit_apply]
    split_ifs with hj
    · subst hj
      omega
    · exact ⟨h1, h2⟩

/-- A sum over the edges `{x, x + e_i}` inside `Q_N` is the full cube sum minus the face
`x_i = N`. -/
theorem sum_latticeCube_ite_add_unit (N : ℕ) (i : Fin d) (F : Vertex d → ℝ) :
    ∑ x ∈ latticeCube d N, (if x + unit i ∈ latticeCube d N then F x else 0) =
      ∑ x ∈ latticeCube d N, F x - ∑ x ∈ (latticeCube d N).filter (fun x => x i = (N : ℤ)), F x := by
  rw [Finset.sum_filter, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  by_cases h : x i = (N : ℤ) <;> simp [add_unit_mem_latticeCube_iff hx, h]

/-- The energy on `Q_N`: the cube sum of the energy density `Σ_i ∇(x, x + e_i)²` minus the faces
`x_i = N`. -/
theorem boxEnergy_latticeCube (C : OpenComponent ω) (u : C → ℝ) (N : ℕ) :
    boxEnergy C u (latticeCube d N) =
      ∑ x ∈ latticeCube d N, ∑ i, edgeDifference C u x (x + unit i) ^ 2 -
        ∑ i, ∑ x ∈ (latticeCube d N).filter (fun x => x i = (N : ℤ)),
          edgeDifference C u x (x + unit i) ^ 2 := by
  unfold boxEnergy
  rw [Finset.sum_comm, Finset.sum_comm (s := latticeCube d N), ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => sum_latticeCube_ite_add_unit N i _

/-- The horizontal differences on `Q_N`: the cube sum of `∇(x + e₁, x)` minus the face
`x₁ = N`. -/
theorem boxDrift_latticeCube [NeZero d] (C : OpenComponent ω) (u : C → ℝ) (N : ℕ) :
    boxDrift C u (latticeCube d N) =
      ∑ x ∈ latticeCube d N, edgeDifference C u (x + unit 0) x -
        ∑ x ∈ (latticeCube d N).filter (fun x => x 0 = (N : ℤ)),
          edgeDifference C u (x + unit 0) x :=
  sum_latticeCube_ite_add_unit N 0 _

/-- The total absolute flux out of `Q_N` is a sum over the faces `x_i = ± N`. -/
theorem boundaryFlux_latticeCube (C : OpenComponent ω) (u : C → ℝ) (N : ℕ) :
    boundaryFlux C u (latticeCube d N) =
      ∑ i, (∑ x ∈ (latticeCube d N).filter (fun x => x i = (N : ℤ)),
          |edgeDifference C u x (x + unit i)| +
        ∑ x ∈ (latticeCube d N).filter (fun x => x i = -(N : ℤ)),
          |edgeDifference C u x (x - unit i)|) := by
  unfold boundaryFlux
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_filter, Finset.sum_filter]
  congr 1 <;> refine Finset.sum_congr rfl fun x hx => ?_
  · by_cases h : x i = (N : ℤ) <;> simp [add_unit_mem_latticeCube_iff hx, h]
  · by_cases h : x i = -(N : ℤ) <;> simp [sub_unit_mem_latticeCube_iff hx, h]

end Cube

/-! ### Corrected planes of slope `e₁` -/

section CorrectedPlane

variable [NeZero d] {ω : Configuration d}

/-- **Sublinearity on cubes.** A corrected plane `u` of slope `e₁` satisfies
`|u(x) - x₁| ≤ ε N` on `C ∩ Q_N` for every large `N`. -/
theorem abs_sub_coord_le_of_isCorrectedPlane {C : OpenComponent ω} {u : C → ℝ}
    (hu : IsCorrectedPlane C (slopeE1 d) u) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : C, x.val ∈ latticeCube d N → |u x - (x.val 0 : ℝ)| ≤ ε * N := by
  have hd : (0 : ℝ) < d + 1 := by positivity
  obtain ⟨R₀, -, hR⟩ := hu.2 (ε / (d + 1)) (div_pos hε hd)
  refine ⟨⌈R₀⌉₊ + 1, fun N hN x hx => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hR₀ : R₀ ≤ (d + 1) * N := by
    have h1 : R₀ ≤ (⌈R₀⌉₊ : ℝ) := Nat.le_ceil R₀
    have h2 : ((⌈R₀⌉₊ : ℕ) : ℝ) ≤ N := by exact_mod_cast (show ⌈R₀⌉₊ ≤ N by omega)
    nlinarith
  have hball : x ∈ componentEuclideanBall C 0 ((d + 1) * N) := by
    rw [mem_componentEuclideanBall, EuclideanSpace.dist_eq, Real.sqrt_lt' (by positivity)]
    simp only [latticeCube, Fintype.mem_piFinset, Finset.mem_Icc] at hx
    have hterm : ∀ i : Fin d, dist (latticeEuclideanEmbedding x.val i)
        (latticeEuclideanEmbedding (0 : Vertex d) i) ^ 2 ≤ (N : ℝ) ^ 2 := by
      intro i
      have hxi : |(x.val i : ℝ)| ≤ N := by
        rw [abs_le]
        obtain ⟨h1, h2⟩ := hx i
        exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
      have : dist (latticeEuclideanEmbedding x.val i)
          (latticeEuclideanEmbedding (0 : Vertex d) i) = |(x.val i : ℝ)| := by
        simp [latticeEuclideanEmbedding]
      rw [this, sq_abs]
      nlinarith [abs_nonneg (x.val i : ℝ), sq_abs (x.val i : ℝ)]
    calc ∑ i, dist (latticeEuclideanEmbedding x.val i)
          (latticeEuclideanEmbedding (0 : Vertex d) i) ^ 2
        ≤ ∑ _i : Fin d, (N : ℝ) ^ 2 := Finset.sum_le_sum fun i _ => hterm i
      _ = d * (N : ℝ) ^ 2 := by simp
      _ < ((d + 1) * N) ^ 2 := by nlinarith
  have h := hR ((d + 1) * N) hR₀ x hball
  have hslope : componentSlope C (slopeE1 d) x = (x.val 0 : ℝ) := by
    simp [componentSlope, slopeE1, Pi.single_apply]
  rw [hslope] at h
  calc |u x - (x.val 0 : ℝ)| ≤ ε / (d + 1) * ((d + 1) * N) := h
    _ = ε * N := by field_simp

/-- **The energy identity of a corrected plane on `Q_N`.** For a corrected plane `u` of slope
`e₁` and `ε > 0`, for every large `N` the energy of `u` on `Q_N` differs from the sum of its
horizontal differences by at most `ε N` times the total absolute flux out of `Q_N`. -/
theorem abs_boxEnergy_sub_boxDrift_le {C : OpenComponent ω} {u : C → ℝ}
    (hu : IsCorrectedPlane C (slopeE1 d) u) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |boxEnergy C u (latticeCube d N) - boxDrift C u (latticeCube d N)| ≤
        ε * N * boundaryFlux C u (latticeCube d N) := by
  obtain ⟨N₀, hN₀⟩ := abs_sub_coord_le_of_isCorrectedPlane hu hε
  refine ⟨N₀, fun N hN => ?_⟩
  rw [boxEnergy_eq C u hu.1.1 (latticeCube d N) 0, sub_sub_cancel_left, abs_neg]
  refine abs_boundaryTerm_le C u _ _ fun x hx hxC => ?_
  have h := hN₀ N hN ⟨x, hxC⟩ hx
  simpa [planeDeviation, extend, hxC] using h

/-- **The energy identity of a corrected plane on `Q_N`, in cube and face sums.** For a corrected
plane `u` of slope `e₁` and `ε > 0`, for every large `N`: the cube sums of the energy density
`Σ_i ∇(x, x + e_i)²` and of the horizontal difference `∇(x + e₁, x)` differ by at most `ε N` times
the absolute flux through the faces `x_i = ± N`, plus the energy density and the absolute
horizontal difference summed over the faces `x_i = N`. -/
theorem abs_sum_energyDensity_sub_sum_drift_le {C : OpenComponent ω} {u : C → ℝ}
    (hu : IsCorrectedPlane C (slopeE1 d) u) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      |∑ x ∈ latticeCube d N, ∑ i, edgeDifference C u x (x + unit i) ^ 2 -
          ∑ x ∈ latticeCube d N, edgeDifference C u (x + unit 0) x| ≤
        ε * N * ∑ i, (∑ x ∈ (latticeCube d N).filter (fun x => x i = (N : ℤ)),
            |edgeDifference C u x (x + unit i)| +
          ∑ x ∈ (latticeCube d N).filter (fun x => x i = -(N : ℤ)),
            |edgeDifference C u x (x - unit i)|) +
        ∑ i, ∑ x ∈ (latticeCube d N).filter (fun x => x i = (N : ℤ)),
            edgeDifference C u x (x + unit i) ^ 2 +
        ∑ x ∈ (latticeCube d N).filter (fun x => x 0 = (N : ℤ)),
            |edgeDifference C u (x + unit 0) x| := by
  obtain ⟨N₀, hN₀⟩ := abs_boxEnergy_sub_boxDrift_le hu hε
  refine ⟨N₀, fun N hN => ?_⟩
  have h := hN₀ N hN
  rw [boxEnergy_latticeCube, boxDrift_latticeCube, boundaryFlux_latticeCube] at h
  have hE : 0 ≤ ∑ i, ∑ x ∈ (latticeCube d N).filter (fun x => x i = (N : ℤ)),
      edgeDifference C u x (x + unit i) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun x _ => sq_nonneg _
  have hD := Finset.abs_sum_le_sum_abs (fun x => edgeDifference C u (x + unit 0) x)
    ((latticeCube d N).filter (fun x => x 0 = (N : ℤ)))
  rw [abs_le] at h hD ⊢
  constructor <;> linarith [h.1, h.2, hD.1, hD.2]

end CorrectedPlane

end Rigidity.Proofs.S3
