import Rigidity.Proofs.Percolation.PlanarCubeEnergyBounds

/-!
# `ν` as a Dirichlet problem with affine data

Summation by parts on the cluster gives `B w u = -∑ w(x) Δu(x)`, so the functions vanishing at the
boundary vertices of the cluster (those with a lattice neighbour outside `U`) are orthogonal to
`A_*(U)`, and the Dirichlet problem with arbitrary boundary values is solvable in `A_*(U)`. The
flux pairing is the Dirichlet form against the affine function `x ↦ p · x`. Consequently the
maximizer of `ν(U, p)` is affine with slope `p` on the boundary vertices, up to a constant, and
`ν(U, p) |U| = B v v / 2` is the least energy of a function with these boundary values
(Armstrong and Dario, Lemma 4.2 and (4.7)).
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Section5
open scoped Classical

namespace Rigidity.Percolation

variable {ω : Configuration 2}

/-- **Summation by parts.** -/
theorem clusterForm_eq_sum {U : TriadicCube 2} (w u : ClusterFun ω U) :
    clusterForm ω U w u = ∑ x, ∑ y,
      (if (openGraph ω).Adj x.1 y.1 then w x * (u x - u y) else 0) := by
  rw [clusterForm_apply]
  set g : ↥(clusterVertices ω U) → ↥(clusterVertices ω U) → ℝ := fun x y =>
    if (openGraph ω).Adj x.1 y.1 then w x * (u x - u y) else 0 with hg
  have h : ∀ x y, clusterFormTerm ω w u x y = g x y + g y x := by
    intro x y
    simp only [clusterFormTerm, hg, SimpleGraph.adj_comm (openGraph ω) y.1 x.1]
    split_ifs <;> ring
  simp only [h, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun x y => g y x)]
  ring

theorem clusterForm_eq_neg_sum_laplacian {U : TriadicCube 2} (w u : ClusterFun ω U) :
    clusterForm ω U w u = -∑ x, w x * clusterLaplacianAt ω U x u := by
  rw [clusterForm_eq_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [clusterLaplacianAt_apply, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs <;> ring

/-- The functions on the cluster vanishing at its boundary vertices. -/
noncomputable def clusterZeroBoundary (ω : Configuration 2) (U : TriadicCube 2) :
    Submodule ℝ (ClusterFun ω U) where
  carrier := {h | ∀ x : ↥(clusterVertices ω U), ¬ U.IsInterior x.1 → h x = 0}
  add_mem' ha hb x hx := by simp [ha x hx, hb x hx]
  zero_mem' x _ := rfl
  smul_mem' c h hh x hx := by simp [hh x hx]

/-- **Orthogonality** of functions vanishing on the boundary to `A_*(U)` (Armstrong and Dario,
(4.4)). -/
theorem clusterForm_eq_zero_of_mem {U : TriadicCube 2} {h u : ClusterFun ω U}
    (hh : h ∈ clusterZeroBoundary ω U) (hu : u ∈ clusterHarmonic ω U) :
    clusterForm ω U h u = 0 := by
  rw [clusterForm_eq_neg_sum_laplacian, neg_eq_zero]
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : U.IsInterior x.1
  · rw [mem_clusterHarmonic.1 hu x hx, mul_zero]
  · rw [hh x hx, zero_mul]

/-- Functions orthogonal to all functions vanishing on the boundary are harmonic. -/
theorem mem_clusterHarmonic_of_orthogonal {U : TriadicCube 2} {u : ClusterFun ω U}
    (h : ∀ h ∈ clusterZeroBoundary ω U, clusterForm ω U h u = 0) :
    u ∈ clusterHarmonic ω U := by
  rw [mem_clusterHarmonic]
  intro x hx
  have hδ : (Pi.single x 1 : ClusterFun ω U) ∈ clusterZeroBoundary ω U := by
    intro z hz
    have hzx : z ≠ x := fun e => hz (e ▸ hx)
    simp [hzx]
  have h1 := h _ hδ
  rw [clusterForm_eq_neg_sum_laplacian, neg_eq_zero] at h1
  rw [Finset.sum_eq_single x (fun z _ hz => by simp [hz])
    (fun hx' => absurd (Finset.mem_univ x) hx')] at h1
  simpa using h1

/-- A function with zero energy has vanishing pairing with every function. -/
theorem clusterForm_eq_zero_of_self {U : TriadicCube 2} {h : ClusterFun ω U}
    (hh : clusterForm ω U h h = 0) (g : ClusterFun ω U) : clusterForm ω U h g = 0 := by
  rw [clusterForm_apply]
  have : ∀ x y, clusterFormTerm ω h g x y = 0 := by
    intro x y
    simp only [clusterFormTerm]
    split_ifs with hxy
    · rw [eq_of_clusterForm_self_eq_zero hh hxy, sub_self, zero_mul]
    · rfl
  simp [this]

/-- **The Dirichlet problem.** Every boundary data on the cluster extends to a function in
`A_*(U)`. -/
theorem exists_clusterHarmonic_eq_on_boundary {U : TriadicCube 2} (g : ClusterFun ω U) :
    ∃ w ∈ clusterHarmonic ω U, w - g ∈ clusterZeroBoundary ω U := by
  set C0 := clusterZeroBoundary ω U
  let B0 : LinearMap.BilinForm ℝ C0 :=
    (clusterForm ω U).compl₁₂ C0.subtype C0.subtype
  let ℓ : Module.Dual ℝ C0 := -((clusterForm ω U).flip g).comp C0.subtype
  have hℓ : ∀ h : C0, ℓ h = -clusterForm ω U h g := fun h => rfl
  obtain ⟨h, hh⟩ := LinearMap.BilinForm.exists_apply_eq_of_symm B0
    (fun u w => clusterForm_symm (u : ClusterFun ω U) w) ℓ
    (fun h hh => by
      rw [hℓ, clusterForm_eq_zero_of_self (h := (h : ClusterFun ω U)) (hh h) g, neg_zero])
  refine ⟨g + h, mem_clusterHarmonic_of_orthogonal fun h' hh' => ?_, ?_⟩
  · have e := hh ⟨h', hh'⟩
    change clusterForm ω U h' h = -clusterForm ω U h' g at e
    rw [map_add]
    linarith
  · rw [add_sub_cancel_left]
    exact h.2

/-- The affine function `x ↦ p · x` on the cluster. -/
noncomputable def clusterAffine (ω : Configuration 2) (U : TriadicCube 2) (p : Fin 2 → ℝ) :
    ClusterFun ω U :=
  fun x => ∑ i, p i * (x.1 i : ℝ)

/-- The flux pairing is the Dirichlet form against the affine function. -/
theorem fluxPairing_eq_clusterForm {U : TriadicCube 2} (p : Fin 2 → ℝ) (w : ClusterFun ω U) :
    fluxPairing ω U p w = clusterForm ω U w (clusterAffine ω U p) := by
  rw [fluxPairing_apply, clusterForm_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  simp only [clusterFormTerm, clusterAffine]
  split_ifs
  · rw [← Finset.sum_sub_distrib]
    simp only [← mul_sub]
    rw [Finset.sum_congr rfl fun i _ => (mul_comm (p i) _ : _)]
    ring_nf
    simp only [Fin.sum_univ_two]
    ring
  · rfl

/-- **Affine boundary values** (Armstrong and Dario, Lemma 4.2). A function of `A_*(U)` solving
the first-variation equation of `ν(U, p)` coincides with `x ↦ p · x + c` at the boundary vertices
of the cluster, for some constant `c`. -/
theorem exists_affine_boundary_of_variation (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (p : Fin 2 → ℝ) {v : ClusterFun ω U}
    (hvar : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w v = fluxPairing ω U p w) :
    ∃ c : ℝ, ∀ x : ↥(clusterVertices ω U), ¬ U.IsInterior x.1 →
      v x = ∑ i, p i * (x.1 i : ℝ) + c := by
  set a := clusterAffine ω U p
  have horth : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w (v - a) = 0 := by
    intro w hw
    rw [map_sub, hvar w hw, fluxPairing_eq_clusterForm, sub_self]
  obtain ⟨w, hw, hwb⟩ := exists_clusterHarmonic_eq_on_boundary (v - a)
  have h1 : clusterForm ω U (w - (v - a)) w = 0 := clusterForm_eq_zero_of_mem hwb hw
  have h2 : clusterForm ω U w w = 0 := by
    have h3 := horth w hw
    rw [LinearMap.map_sub₂] at h1
    rw [clusterForm_symm (v - a) w, h3] at h1
    linarith
  by_cases hne : Nonempty ↥(clusterVertices ω U)
  · obtain ⟨z⟩ := hne
    refine ⟨w z, fun x hx => ?_⟩
    have hbx : (w - (v - a)) x = 0 := hwb x hx
    have hwx : w x = w z := by
      have hxz := clusterExtend_eq_of_clusterForm_self_eq_zero hP hU h2
        (mem_clusterVertices.1 x.2) (mem_clusterVertices.1 z.2)
      rwa [clusterExtend_apply_of_mem w x.2, clusterExtend_apply_of_mem w z.2] at hxz
    simp only [Pi.sub_apply] at hbx
    have : v x = a x + w x := by linarith
    rw [this, hwx]
    rfl
  · exact ⟨0, fun x _ => absurd ⟨x⟩ hne⟩

/-- The maximizer of `ν(U, p)`: its energy is `2 |U| ν(U, p)` and it is affine at the boundary
vertices of the cluster. -/
theorem exists_planarNu_maximizer_affine (hP : PlanarPartitionEvent ω) {U : TriadicCube 2}
    (hU : PlanarResolved ω U) (p : Fin 2 → ℝ) :
    ∃ v ∈ clusterHarmonic ω U, (∀ w ∈ clusterHarmonic ω U,
        clusterForm ω U w v = fluxPairing ω U p w) ∧
      planarNu ω U p = clusterForm ω U v v / 2 / U.volume ∧
      ∃ c : ℝ, ∀ x : ↥(clusterVertices ω U), ¬ U.IsInterior x.1 →
        v x = ∑ i, p i * (x.1 i : ℝ) + c := by
  obtain ⟨v, hv, hvar, hν⟩ := exists_planarNu_maximizer (ω := ω) (U := U) p
  refine ⟨v, hv, hvar, ?_, exists_affine_boundary_of_variation hP hU p hvar⟩
  rw [hν, ← hvar v hv]
  ring

/-- Any solution of the first-variation equation of `ν(U, p)` has energy at most
`2 |U| ν(U, p)`. -/
theorem clusterForm_le_of_variation {U : TriadicCube 2} (p : Fin 2 → ℝ) {v : ClusterFun ω U}
    (hv : v ∈ clusterHarmonic ω U)
    (hvar : ∀ w ∈ clusterHarmonic ω U, clusterForm ω U w v = fluxPairing ω U p w) :
    clusterForm ω U v v ≤ 2 * U.volume * planarNu ω U p := by
  have h := le_planarNu p hv
  rw [← hvar v hv, div_le_iff₀ U.volume_pos] at h
  linarith

/-- **Dirichlet principle** (Armstrong and Dario, (4.7)). `ν(U, p) |U|` is at most half the
energy of any function on the cluster equal to `x ↦ p · x` up to a function vanishing at the
boundary vertices. -/
theorem planarNu_le_of_affine_boundary {U : TriadicCube 2} (p : Fin 2 → ℝ)
    {w : ClusterFun ω U} (hw : w - clusterAffine ω U p ∈ clusterZeroBoundary ω U) :
    planarNu ω U p ≤ clusterForm ω U w w / 2 / U.volume := by
  obtain ⟨v, hv, hvar, hν⟩ := exists_planarNu_maximizer (ω := ω) (U := U) p
  rw [hν]
  have hvol := U.volume_pos
  refine div_le_div_of_nonneg_right ?_ hvol.le
  set a := clusterAffine ω U p
  -- `F_p v = B v a = B v w` since `w - a` vanishes on the boundary and `v ∈ A_*(U)`
  have h1 : fluxPairing ω U p v = clusterForm ω U v w := by
    rw [fluxPairing_eq_clusterForm]
    have h0 := clusterForm_eq_zero_of_mem hw hv
    rw [LinearMap.map_sub₂] at h0
    rw [clusterForm_symm v w, clusterForm_symm v a]
    linarith
  rw [h1]
  have hpos := clusterForm_self_nonneg (w - v)
  rw [LinearMap.map_sub₂, map_sub, map_sub] at hpos
  rw [clusterForm_symm v w] at hpos ⊢
  linarith

end Rigidity.Percolation
