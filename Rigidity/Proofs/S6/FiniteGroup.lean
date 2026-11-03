import Rigidity.Steps.S6.SlowMixing
import LatticeProb.External.SupercriticalBondUniquenessInput
import LatticeProb.Prob.Percolation.LatticeBondProbability
import Mathlib.LinearAlgebra.FreeModule.Int

/-! # Section 6: the sandpile group of a finite subset of the infinite cluster

step:6.5-finite-group (paper L2829-2830, L2848). If `V ⊂ 𝒞_∞` is finite, the toppling Laplacian
`Δ_V` is injective on `ℤ^V`: at a positive maximum of a kernel element `g` (extended by zero
outside `V`, the chips leaving `V` being lost) every open neighbour lies in `V` and attains
the maximum, so the open cluster of the maximizer, which is `𝒞_∞`, would lie in the finite set `V`.
The range of an injective endomorphism of `ℤ^V` has finite index, so the sandpile group
`ℤ^V / Δ_V ℤ^V` is finite. We also record the almost sure uniqueness of `𝒞_∞` for
`p_c < p`. -/

open MeasureTheory LatticeProb.Percolation Classical Rigidity.Section6

namespace Rigidity.Proofs.S6

variable {d : ℕ}

/-- Almost surely the infinite open cluster exists and is unique: for `p < 1` this is the cited
classical input (Aizenman-Kesten-Newman, Burton-Keane); at `p = 1` every bond is open. -/
theorem uniqueClusterStep {d : ℕ} [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ))
    (hclassical : LatticeProb.External.SupercriticalBondUniqueness) :
    Steps.S6.UniqueClusterStep d p := by
  rcases lt_or_eq_of_le p.2.2 with hp1 | hp1
  · exact (mem_ae_iff_prob_eq_one (measurableSet_uniqueInfiniteComponentEvent d)).mpr
      (hclassical.2 d hd p hpc hp1)
  · obtain rfl : p = 1 := Subtype.ext hp1
    rw [Steps.S6.UniqueClusterStep, latticeBondLaw_one]
    exact (ae_dirac_iff (measurableSet_uniqueInfiniteComponentEvent d)).2
      (allOpen_hasUniqueInfiniteOpenComponent d)

/-- The extension by zero outside `V` of a function on `V`. -/
noncomputable def extendByZero (V : Finset (Vertex d)) (g : V → ℤ) (v : Vertex d) : ℤ :=
  if hv : v ∈ V then g ⟨v, hv⟩ else 0

theorem extendByZero_coe (V : Finset (Vertex d)) (g : V → ℤ) (x : V) :
    extendByZero V g x = g x := by
  simp [extendByZero]

/-- `Δ_V g` is the open-graph Laplacian of the extension of `g` by zero outside `V`. -/
theorem toppling_apply_eq (ω : Configuration d) (V : Finset (Vertex d)) (g : V → ℤ) (x : V) :
    toppling ω V g x = ((openGraph ω).degree x.val : ℤ) * g x -
      ∑ v ∈ (openGraph ω).neighborFinset x.val, extendByZero V g v := by
  change ((openGraph ω).degree x.val : ℤ) * g x -
    ∑ y : V, (if (openGraph ω).Adj x.val y.val then g y else 0) = _
  congr 1
  calc ∑ y : V, (if (openGraph ω).Adj x.val y.val then g y else 0)
      = ∑ y : V, (if (openGraph ω).Adj x.val y.val then extendByZero V g y else 0) := by
        simp only [extendByZero_coe]
    _ = ∑ v ∈ V, (if (openGraph ω).Adj x.val v then extendByZero V g v else 0) :=
        Finset.sum_coe_sort V fun v => if (openGraph ω).Adj x.val v then extendByZero V g v else 0
    _ = ∑ v ∈ V.filter ((openGraph ω).Adj x.val), extendByZero V g v :=
        (Finset.sum_filter _ _).symm
    _ = ∑ v ∈ ((openGraph ω).neighborFinset x.val).filter (· ∈ V), extendByZero V g v := by
        congr 1; ext v; simp [and_comm]
    _ = _ := Finset.sum_filter_of_ne fun v _ hv => by
        by_contra h; exact hv (by simp [extendByZero, h])

/-- Maximum principle for `Δ_V`: at a positive maximum `x` of `g` over `V` with `Δ_V g (x) = 0`,
every open neighbour of `x` lies in `V` and attains the maximum. -/
theorem toppling_max_propagates {ω : Configuration d} {V : Finset (Vertex d)} {g : V → ℤ}
    {M : ℤ} (hM : 0 < M) (hle : ∀ y, g y ≤ M) {x : V} (hx : g x = M)
    (hΔ : toppling ω V g x = 0) {v : Vertex d} (hv : (openGraph ω).Adj x.val v) :
    ∃ hvV : v ∈ V, g ⟨v, hvV⟩ = M := by
  have hG : ∀ w, extendByZero V g w ≤ M := fun w => by
    unfold extendByZero; split_ifs; exacts [hle _, hM.le]
  rw [toppling_apply_eq, hx, sub_eq_zero] at hΔ
  have hsum : ∑ w ∈ (openGraph ω).neighborFinset x.val, (M - extendByZero V g w) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
      ← hΔ, nsmul_eq_mul, mul_comm, sub_self]
  have hv0 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => sub_nonneg.2 (hG w)).1 hsum v
    (((openGraph ω).mem_neighborFinset _ _).2 hv)
  have hGv : extendByZero V g v = M := by linarith
  by_cases hvV : v ∈ V
  · exact ⟨hvV, by simpa [extendByZero, hvV] using hGv⟩
  · simp only [extendByZero, hvV, dite_false] at hGv
    omega

/-- If `V ⊂ 𝒞_∞` is finite, `Δ_V` is injective on `ℤ^V`. -/
theorem toppling_injective {ω : Configuration d} (h : HasUniqueInfiniteOpenComponent ω)
    {V : Finset (Vertex d)} (hV : ∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) :
    Function.Injective (toppling ω V) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  by_contra hne
  obtain ⟨g, hg, y, hy⟩ : ∃ g, toppling ω V g = 0 ∧ ∃ y, 0 < g y := by
    obtain ⟨y, hy⟩ := Function.ne_iff.1 hne
    rcases lt_or_gt_of_ne hy with hy | hy
    · exact ⟨-f, by simp [hf], y, by simpa using hy⟩
    · exact ⟨f, hf, y, hy⟩
  obtain ⟨x, -, hx⟩ := Finset.exists_max_image Finset.univ g ⟨y, Finset.mem_univ y⟩
  have hM : 0 < g x := hy.trans_le (hx y (Finset.mem_univ y))
  have hwalk : ∀ u w (q : (openGraph ω).Walk u w) (hu : u ∈ V), g ⟨u, hu⟩ = g x →
      ∃ hw : w ∈ V, g ⟨w, hw⟩ = g x := by
    intro u w q
    induction q with
    | nil => exact fun hu h => ⟨hu, h⟩
    | cons hadj q ih =>
      intro hu hgu
      obtain ⟨hv, hgv⟩ := toppling_max_propagates hM (fun z => hx z (Finset.mem_univ z)) hgu
        (congrFun hg _) hadj
      exact ih hv hgv
  refine uniqueInfiniteComponent_infinite h (V.finite_toSet.subset fun w hw => ?_)
  have hxC := hV x.val x.property
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hxC hw
  obtain ⟨q⟩ := SimpleGraph.ConnectedComponent.exact (hxC.trans hw.symm)
  exact (hwalk _ _ q x.property rfl).1

/-- step:6.5-finite-group: the sandpile group of a finite `V ⊂ 𝒞_∞` is finite. -/
theorem finiteGroupStep {d : ℕ} : Steps.S6.FiniteGroupStep d := by
  intro ω h V hV
  have : (toppling ω V).range.FiniteIndex :=
    ⟨Int.addSubgroup_index_ne_zero_iff.2
      ⟨(AddMonoidHom.ofInjective (toppling_injective h hV)).symm⟩⟩
  infer_instance

end Rigidity.Proofs.S6
