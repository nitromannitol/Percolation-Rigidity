import Rigidity.Proofs.Percolation.GeneralDim.CubeEnergyBounds

/-!
# `ν` as a Dirichlet problem with affine data, in `ℤ^d`

Summation by parts on the cluster gives `B w u = -∑ w(x) Δu(x)`, so the functions vanishing at the
vertices of `C_*(U)` outside `int(U)` are orthogonal to `A_*(U)` (Armstrong and Dario, (4.1)), and
the Dirichlet problem with arbitrary boundary values is solvable in `A_*(U)`. The flux pairing is
the Dirichlet form against the affine function `x ↦ p · x`. Consequently, on the partition event
and for a resolved cube, the maximizer of `ν(U, p)` is affine with slope `p` at the boundary
vertices of the cluster, up to a constant, and `ν(U, p) |U| = B v v / 2` is the least half energy
of a function with these boundary values (Armstrong and Dario, Lemma 4.3, (4.9), and (4.7)).
-/

open LatticeProb.Percolation Rigidity.External
open scoped Classical

namespace Rigidity.Percolation

variable {d : ℕ} {ω : Configuration d}

/-- **Summation by parts.** -/
theorem cubeForm_eq_sum {U : TriadicCube d} (w u : CubeFun ω U) :
    cubeForm ω U w u = ∑ x, ∑ y,
      (if (openGraph ω).Adj x.1 y.1 then w x * (u x - u y) else 0) := by
  rw [cubeForm_apply]
  set g : ↥(crossingClusterVertices ω U) → ↥(crossingClusterVertices ω U) → ℝ := fun x y =>
    if (openGraph ω).Adj x.1 y.1 then w x * (u x - u y) else 0 with hg
  have h : ∀ x y, cubeFormTerm ω w u x y = g x y + g y x := by
    intro x y
    simp only [cubeFormTerm, hg, SimpleGraph.adj_comm (openGraph ω) y.1 x.1]
    split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun x y => g y x)]
  ring

theorem cubeForm_eq_neg_sum_laplacian {U : TriadicCube d} (w u : CubeFun ω U) :
    cubeForm ω U w u = -∑ x, w x * cubeLaplacianAt ω U x u := by
  rw [cubeForm_eq_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [cubeLaplacianAt_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> ring

/-- The functions on the cluster vanishing at its vertices outside `int(U)`. -/
noncomputable def cubeZeroBoundary (ω : Configuration d) (U : TriadicCube d) :
    Submodule ℝ (CubeFun ω U) where
  carrier := {h | ∀ x : ↥(crossingClusterVertices ω U), ¬ U.IsLatticeInterior x.1 → h x = 0}
  add_mem' ha hb x hx := by simp [ha x hx, hb x hx]
  zero_mem' x _ := rfl
  smul_mem' c h hh x hx := by simp [hh x hx]

/-- **Orthogonality** of the functions vanishing on the boundary to `A_*(U)` (Armstrong and
Dario, (4.1)). -/
theorem cubeForm_eq_zero_of_mem {U : TriadicCube d} {h u : CubeFun ω U}
    (hh : h ∈ cubeZeroBoundary ω U) (hu : u ∈ cubeHarmonic ω U) :
    cubeForm ω U h u = 0 := by
  rw [cubeForm_eq_neg_sum_laplacian, neg_eq_zero]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : U.IsLatticeInterior x.1
  · rw [mem_cubeHarmonic.1 hu x hx, mul_zero]
  · rw [hh x hx, zero_mul]

/-- Functions orthogonal to all functions vanishing on the boundary are harmonic (Armstrong and
Dario, (4.1)). -/
theorem mem_cubeHarmonic_of_orthogonal {U : TriadicCube d} {u : CubeFun ω U}
    (h : ∀ h ∈ cubeZeroBoundary ω U, cubeForm ω U h u = 0) :
    u ∈ cubeHarmonic ω U := by
  rw [mem_cubeHarmonic]
  intro x hx
  have hδ : (Pi.single x 1 : CubeFun ω U) ∈ cubeZeroBoundary ω U := by
    intro z hz
    have hzx : z ≠ x := fun e => hz (e ▸ hx)
    simp [hzx]
  have h1 := h _ hδ
  rw [cubeForm_eq_neg_sum_laplacian, neg_eq_zero] at h1
  rw [Finset.sum_eq_single x (fun z _ hz => by simp [hz])
    (fun hx' => absurd (Finset.mem_univ x) hx')] at h1
  simpa using h1

/-- A function with zero energy has vanishing pairing with every function. -/
theorem cubeForm_eq_zero_of_self {U : TriadicCube d} {h : CubeFun ω U}
    (hh : cubeForm ω U h h = 0) (g : CubeFun ω U) : cubeForm ω U h g = 0 := by
  rw [cubeForm_apply]
  have : ∀ x y, cubeFormTerm ω h g x y = 0 := by
    intro x y
    simp only [cubeFormTerm]
    split_ifs with hxy
    · rw [eq_of_cubeForm_self_eq_zero hh hxy, sub_self, zero_mul]
    · rfl
  simp [this]

/-- **The Dirichlet problem.** Every boundary data on the cluster extends to a function in
`A_*(U)`. -/
theorem exists_cubeHarmonic_eq_on_boundary {U : TriadicCube d} (g : CubeFun ω U) :
    ∃ w ∈ cubeHarmonic ω U, w - g ∈ cubeZeroBoundary ω U := by
  set C0 := cubeZeroBoundary ω U
  let B0 : LinearMap.BilinForm ℝ C0 := (cubeForm ω U).compl₁₂ C0.subtype C0.subtype
  let ℓ : Module.Dual ℝ C0 := -((cubeForm ω U).flip g).comp C0.subtype
  have hℓ : ∀ h : C0, ℓ h = -cubeForm ω U h g := fun h => rfl
  obtain ⟨h, hh⟩ := LinearMap.BilinForm.exists_apply_eq_of_symm B0
    (fun u w => cubeForm_symm (u : CubeFun ω U) w) ℓ
    (fun h hh => by
      rw [hℓ, cubeForm_eq_zero_of_self (h := (h : CubeFun ω U)) (hh h) g, neg_zero])
  refine ⟨g + h, mem_cubeHarmonic_of_orthogonal fun h' hh' => ?_, ?_⟩
  · have e := hh ⟨h', hh'⟩
    change cubeForm ω U h' h = -cubeForm ω U h' g at e
    rw [map_add]
    linarith
  · rw [add_sub_cancel_left]
    exact h.2

/-- The affine function `x ↦ p · x` on the cluster. -/
noncomputable def cubeAffine (ω : Configuration d) (U : TriadicCube d) (p : Fin d → ℝ) :
    CubeFun ω U :=
  fun x => ∑ i, p i * (x.1 i : ℝ)

/-- The flux pairing is the Dirichlet form against the affine function. -/
theorem cubeFluxPairing_eq_cubeForm {U : TriadicCube d} (p : Fin d → ℝ) (w : CubeFun ω U) :
    cubeFluxPairing ω U p w = cubeForm ω U w (cubeAffine ω U p) := by
  rw [cubeFluxPairing_apply, cubeForm_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [cubeFormTerm, cubeAffine]
  split_ifs
  · have e : ∑ i, p i * (x.1 i : ℝ) - ∑ i, p i * (y.1 i : ℝ) =
        -∑ i, p i * ((y.1 i : ℝ) - x.1 i) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    ring
  · rfl

/-- **Affine boundary values** (Armstrong and Dario, Lemma 4.3, (4.9)). On the partition event and
for a resolved cube, a function solving the first variation equation of `ν(U, p)` coincides with
`x ↦ p · x + c` at the vertices of the cluster outside `int(U)`, for some constant `c`. -/
theorem exists_affine_boundary_of_cubeNu_variation (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (p : Fin d → ℝ) {v : CubeFun ω U}
    (hvar : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w v = cubeFluxPairing ω U p w) :
    ∃ c : ℝ, ∀ x : ↥(crossingClusterVertices ω U), ¬ U.IsLatticeInterior x.1 →
      v x = ∑ i, p i * (x.1 i : ℝ) + c := by
  set a := cubeAffine ω U p
  have horth : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w (v - a) = 0 := by
    intro w hw
    rw [map_sub, hvar w hw, cubeFluxPairing_eq_cubeForm, sub_self]
  obtain ⟨w, hw, hwb⟩ := exists_cubeHarmonic_eq_on_boundary (v - a)
  have h1 : cubeForm ω U (w - (v - a)) w = 0 := cubeForm_eq_zero_of_mem hwb hw
  have h2 : cubeForm ω U w w = 0 := by
    have h3 := horth w hw
    rw [LinearMap.map_sub₂] at h1
    rw [cubeForm_symm (v - a) w, h3] at h1
    linarith
  by_cases hne : Nonempty ↥(crossingClusterVertices ω U)
  · obtain ⟨z⟩ := hne
    refine ⟨w z, fun x hx => ?_⟩
    have hbx : (w - (v - a)) x = 0 := hwb x hx
    have hwx : w x = w z := by
      have hxz := cubeExtend_eq_of_cubeForm_self_eq_zero hd hP hU h2
        (mem_crossingClusterVertices.1 x.2) (mem_crossingClusterVertices.1 z.2)
      rwa [cubeExtend_apply_of_mem w x.2, cubeExtend_apply_of_mem w z.2] at hxz
    simp only [Pi.sub_apply] at hbx
    have : v x = a x + w x := by linarith
    rw [this, hwx]
    rfl
  · exact ⟨0, fun x _ => absurd ⟨x⟩ hne⟩

/-- The maximizer of `ν(U, p)`: its energy is `2 |U| ν(U, p)` and it is affine at the boundary
vertices of the cluster (Armstrong and Dario, (4.7) and Lemma 4.3). -/
theorem exists_cubeNu_maximizer_affine (hd : 0 < d) (hP : PartitionEvent ω) {U : TriadicCube d}
    (hU : PartitionResolved ω U) (p : Fin d → ℝ) :
    ∃ v ∈ cubeHarmonic ω U, (∀ w ∈ cubeHarmonic ω U,
        cubeForm ω U w v = cubeFluxPairing ω U p w) ∧
      cubeNu ω U p = cubeForm ω U v v / 2 / U.latticeVolume ∧
      ∃ c : ℝ, ∀ x : ↥(crossingClusterVertices ω U), ¬ U.IsLatticeInterior x.1 →
        v x = ∑ i, p i * (x.1 i : ℝ) + c := by
  obtain ⟨v, hv, hvar, hν⟩ := exists_cubeNu_maximizer (ω := ω) (U := U) p
  refine ⟨v, hv, hvar, ?_, exists_affine_boundary_of_cubeNu_variation hd hP hU p hvar⟩
  rw [hν, ← hvar v hv]
  ring

/-- Any solution of the first variation equation of `ν(U, p)` has energy at most
`2 |U| ν(U, p)`. -/
theorem cubeForm_le_of_cubeNu_variation {U : TriadicCube d} (p : Fin d → ℝ) {v : CubeFun ω U}
    (hv : v ∈ cubeHarmonic ω U)
    (hvar : ∀ w ∈ cubeHarmonic ω U, cubeForm ω U w v = cubeFluxPairing ω U p w) :
    cubeForm ω U v v ≤ 2 * U.latticeVolume * cubeNu ω U p := by
  have h := le_cubeNu p hv
  rw [← hvar v hv, div_le_iff₀ U.latticeVolume_pos] at h
  linarith

/-- **Dirichlet principle** (Armstrong and Dario, Lemma 4.3, cell problem). `ν(U, p) |U|` is at
most half the energy of any function on the cluster equal to `x ↦ p · x` up to a function
vanishing at the boundary vertices. -/
theorem cubeNu_le_of_affine_boundary {U : TriadicCube d} (p : Fin d → ℝ)
    {w : CubeFun ω U} (hw : w - cubeAffine ω U p ∈ cubeZeroBoundary ω U) :
    cubeNu ω U p ≤ cubeForm ω U w w / 2 / U.latticeVolume := by
  obtain ⟨v, hv, hvar, hν⟩ := exists_cubeNu_maximizer (ω := ω) (U := U) p
  rw [hν]
  have hvol := U.latticeVolume_pos
  refine div_le_div_of_nonneg_right ?_ hvol.le
  set a := cubeAffine ω U p
  have h1 : cubeFluxPairing ω U p v = cubeForm ω U v w := by
    rw [cubeFluxPairing_eq_cubeForm]
    have h0 := cubeForm_eq_zero_of_mem hw hv
    rw [LinearMap.map_sub₂] at h0
    rw [cubeForm_symm v w, cubeForm_symm v a]
    linarith
  rw [h1]
  have hpos := cubeForm_self_nonneg (w - v)
  rw [LinearMap.map_sub₂, map_sub, map_sub] at hpos
  rw [cubeForm_symm v w] at hpos ⊢
  linarith

/-- Constant functions have zero pairing with every function. -/
theorem cubeForm_const_left {U : TriadicCube d} (c : ℝ) (g : CubeFun ω U) :
    cubeForm ω U (fun _ => c) g = 0 := by
  rw [cubeForm_apply]
  simp [cubeFormTerm]

/-- **`ν` is the energy of the cell problem** (Armstrong and Dario, Lemma 4.3). On the partition
event and for a resolved cube, `ν(U, p)` is attained, as the least value of `B w w / (2 |U|)` over
the functions `w` on the cluster equal to `x ↦ p · x` up to a function vanishing at the boundary
vertices (the lower bound is `cubeNu_le_of_affine_boundary`), at the maximizer minus its additive
constant. -/
theorem exists_cubeNu_eq_of_affine_boundary (hd : 0 < d) (hP : PartitionEvent ω)
    {U : TriadicCube d} (hU : PartitionResolved ω U) (p : Fin d → ℝ) :
    ∃ w : CubeFun ω U, w - cubeAffine ω U p ∈ cubeZeroBoundary ω U ∧
      cubeNu ω U p = cubeForm ω U w w / 2 / U.latticeVolume := by
  obtain ⟨v, -, -, hν, c, hc⟩ := exists_cubeNu_maximizer_affine hd hP hU p
  refine ⟨v - fun _ => c, fun x hx => ?_, ?_⟩
  · simp only [Pi.sub_apply, cubeAffine]
    rw [hc x hx]
    ring
  · rw [hν]
    congr 2
    rw [LinearMap.map_sub₂, map_sub, map_sub, cubeForm_const_left, cubeForm_const_left,
      cubeForm_symm v (fun _ => c), cubeForm_const_left]
    ring

end Rigidity.Percolation
