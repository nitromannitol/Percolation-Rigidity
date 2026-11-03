import Rigidity.Steps.S6.UpperBound

/-! # Section 6: the wired Laplacian of a finite subset of the infinite cluster

step:6.5-upper, wired Laplacian (paper `paper/percolation-harmonic-corrected.tex` L2829-2830,
L2948-2951). Let `V ⊂ 𝒞_∞` be finite. The `some y` coordinate of `Σ_x g(x) b_x` is
`(Δ_V g)(y)`, so a linear relation between the wired columns `b_x` is a `Δ_V`-harmonic function
on `V`. At a positive maximum of such a function every open neighbour lies in `V` and attains the
maximum (the chips leaving `V` are lost), so the open cluster of the maximizer, which is `𝒞_∞`,
would lie in the finite set `V`; hence the columns are linearly independent. Each column sums to
`deg(x) - #{y ∈ V : y ∼ x} - #(exit edges at x) = 0`, so the `|V|` columns span the hyperplane
`Σ y = 0` of `ℝ^{V ∪ {sink}}`, of dimension `|V|`. This is the real counterpart of the injectivity
of `Δ_V` on `ℤ^V` (`toppling_injective`). -/

open LatticeProb.Percolation Rigidity.Section6 Classical

namespace Rigidity.Proofs.S6

variable {d : ℕ}

/-! ### The maximum principle for `Δ_V` on real functions -/

/-- The extension by zero outside `V` of a real function on `V`. -/
noncomputable def realExtendByZero (V : Finset (Vertex d)) (g : V → ℝ) (v : Vertex d) : ℝ :=
  if hv : v ∈ V then g ⟨v, hv⟩ else 0

theorem realExtendByZero_coe (V : Finset (Vertex d)) (g : V → ℝ) (x : V) :
    realExtendByZero V g x = g x := by
  simp [realExtendByZero]

/-- `Δ_V g` is the open-graph Laplacian of the extension of `g` by zero outside `V`. -/
theorem realToppling_apply_eq (ω : Configuration d) (V : Finset (Vertex d)) (g : V → ℝ)
    (x : V) :
    Steps.S6.realToppling ω V g x = ((openGraph ω).degree x.val : ℝ) * g x -
      ∑ v ∈ (openGraph ω).neighborFinset x.val, realExtendByZero V g v := by
  rw [Steps.S6.realToppling]
  congr 1
  calc ∑ y : V, (if (openGraph ω).Adj x.val y.val then g y else 0)
      = ∑ y : V, (if (openGraph ω).Adj x.val y.val then realExtendByZero V g y else 0) := by
        simp only [realExtendByZero_coe]
    _ = ∑ v ∈ V, (if (openGraph ω).Adj x.val v then realExtendByZero V g v else 0) :=
        Finset.sum_coe_sort V fun v =>
          if (openGraph ω).Adj x.val v then realExtendByZero V g v else 0
    _ = ∑ v ∈ V.filter ((openGraph ω).Adj x.val), realExtendByZero V g v :=
        (Finset.sum_filter _ _).symm
    _ = ∑ v ∈ ((openGraph ω).neighborFinset x.val).filter (· ∈ V), realExtendByZero V g v := by
        congr 1; ext v; simp [and_comm]
    _ = _ := Finset.sum_filter_of_ne fun v _ hv => by
        by_contra h; exact hv (by simp [realExtendByZero, h])

/-- At a positive maximum `x` of `g` over `V` with `Δ_V g (x) = 0`, every open neighbour of `x`
lies in `V` and attains the maximum. -/
theorem realToppling_max_propagates {ω : Configuration d} {V : Finset (Vertex d)} {g : V → ℝ}
    {M : ℝ} (hM : 0 < M) (hle : ∀ y, g y ≤ M) {x : V} (hx : g x = M)
    (hΔ : Steps.S6.realToppling ω V g x = 0) {v : Vertex d} (hv : (openGraph ω).Adj x.val v) :
    ∃ hvV : v ∈ V, g ⟨v, hvV⟩ = M := by
  have hG : ∀ w, realExtendByZero V g w ≤ M := fun w => by
    unfold realExtendByZero; split_ifs; exacts [hle _, hM.le]
  rw [realToppling_apply_eq, hx, sub_eq_zero] at hΔ
  have hsum : ∑ w ∈ (openGraph ω).neighborFinset x.val, (M - realExtendByZero V g w) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
      nsmul_eq_mul]
    linarith
  have hv0 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ => sub_nonneg.2 (hG w)).1 hsum v
    (((openGraph ω).mem_neighborFinset _ _).2 hv)
  have hGv : realExtendByZero V g v = M := by linarith
  by_cases hvV : v ∈ V
  · exact ⟨hvV, by simpa [realExtendByZero, hvV] using hGv⟩
  · simp only [realExtendByZero, hvV, dite_false] at hGv
    linarith

/-- A `Δ_V`-harmonic real function on a finite `V ⊂ 𝒞_∞` is nonpositive. -/
theorem le_zero_of_realToppling_eq_zero {ω : Configuration d}
    (h : HasUniqueInfiniteOpenComponent ω) {V : Finset (Vertex d)}
    (hV : ∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) {g : V → ℝ}
    (hg : ∀ x, Steps.S6.realToppling ω V g x = 0) (y : V) : g y ≤ 0 := by
  rw [← not_lt]
  intro hy
  obtain ⟨x, -, hx⟩ := Finset.exists_max_image Finset.univ g ⟨y, Finset.mem_univ y⟩
  have hM : 0 < g x := hy.trans_le (hx y (Finset.mem_univ y))
  have hwalk : ∀ u w (q : (openGraph ω).Walk u w) (hu : u ∈ V), g ⟨u, hu⟩ = g x →
      ∃ hw : w ∈ V, g ⟨w, hw⟩ = g x := by
    intro u w q
    induction q with
    | nil => exact fun hu h => ⟨hu, h⟩
    | cons hadj q ih =>
      intro hu hgu
      obtain ⟨hv, hgv⟩ := realToppling_max_propagates hM (fun z => hx z (Finset.mem_univ z))
        hgu (hg _) hadj
      exact ih hv hgv
  refine uniqueInfiniteComponent_infinite h (V.finite_toSet.subset fun w hw => ?_)
  have hxC := hV x.val x.property
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hxC hw
  obtain ⟨q⟩ := SimpleGraph.ConnectedComponent.exact (hxC.trans hw.symm)
  exact (hwalk _ _ q x.property rfl).1

theorem realToppling_neg (ω : Configuration d) (V : Finset (Vertex d)) (g : V → ℝ) (x : V) :
    Steps.S6.realToppling ω V (-g) x = -Steps.S6.realToppling ω V g x := by
  have hite : ∀ y : V, (if (openGraph ω).Adj x.val y.val then -g y else 0) =
      -(if (openGraph ω).Adj x.val y.val then g y else 0) := fun y => by
    split_ifs <;> simp
  simp only [Steps.S6.realToppling, Pi.neg_apply, hite, Finset.sum_neg_distrib]
  ring

/-- For a finite `V ⊂ 𝒞_∞`, `Δ_V` is injective on `ℝ^V`. -/
theorem eq_zero_of_realToppling_eq_zero {ω : Configuration d}
    (h : HasUniqueInfiniteOpenComponent ω) {V : Finset (Vertex d)}
    (hV : ∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) {g : V → ℝ}
    (hg : ∀ x, Steps.S6.realToppling ω V g x = 0) (y : V) : g y = 0 := by
  have hneg := le_zero_of_realToppling_eq_zero h hV (g := -g)
    (fun x => by rw [realToppling_neg, hg x, neg_zero]) y
  exact le_antisymm (le_zero_of_realToppling_eq_zero h hV hg y) (by simpa using hneg)

/-! ### The wired columns -/

/-- `b_x(y) = deg(x) 1_{y = x} - 1_{y ∼ x}` for `y ∈ V`. -/
theorem wiredColumn_some_eq (ω : Configuration d) (V : Finset (Vertex d)) (x y : V) :
    Steps.S6.wiredColumn ω V x (some y) =
      (if y = x then ((openGraph ω).degree x.val : ℝ) else 0) -
        if (openGraph ω).Adj x.val y.val then 1 else 0 := by
  rw [Steps.S6.wiredColumn_some]
  by_cases hy : y = x
  · subst hy
    simp
  · by_cases ha : (openGraph ω).Adj x.val y.val <;> simp [hy, ha]

/-- The open edges at `x ∈ V` either stay in `V` or leave it:
`e(x) + #{y ∈ V : y ∼ x} = deg(x)`. -/
theorem card_exitNeighbors_add_card_filter_adj (ω : Configuration d) (V : Finset (Vertex d))
    (x : V) :
    (Steps.S6.exitNeighbors ω V x).card +
        (Finset.univ.filter fun y : V => (openGraph ω).Adj x.val y.val).card =
      (openGraph ω).degree x.val := by
  have h1 : (Finset.univ.filter fun y : V => (openGraph ω).Adj x.val y.val).card =
      (((openGraph ω).neighborFinset x.val).filter (· ∈ V)).card := by
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    congr 1
    ext v
    simp [and_comm]
  have h2 := Finset.card_filter_add_card_filter_not
    (s := (openGraph ω).neighborFinset x.val) (· ∈ V)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h2
  rw [h1, Steps.S6.exitNeighbors]
  omega

/-- Each wired column sums to zero. -/
theorem sum_wiredColumn (ω : Configuration d) (V : Finset (Vertex d)) (x : V) :
    ∑ o, Steps.S6.wiredColumn ω V x o = 0 := by
  have hcard := card_exitNeighbors_add_card_filter_adj ω V x
  rw [Fintype.sum_option]
  simp only [Steps.S6.wiredColumn_none, wiredColumn_some_eq, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_boole]
  have hcard' : ((Steps.S6.exitNeighbors ω V x).card : ℝ) +
      ((Finset.univ.filter fun y : V => (openGraph ω).Adj x.val y.val).card : ℝ) =
        ((openGraph ω).degree x.val : ℝ) := by
    exact_mod_cast hcard
  linarith

/-- The `some y` coordinate of `Σ_x g(x) b_x` is `(Δ_V g)(y)`. -/
theorem sum_mul_wiredColumn_some_wired (ω : Configuration d) (V : Finset (Vertex d)) (g : V → ℝ)
    (y : V) :
    ∑ x, g x * Steps.S6.wiredColumn ω V x (some y) = Steps.S6.realToppling ω V g y := by
  have hterm : ∀ x : V, g x * Steps.S6.wiredColumn ω V x (some y) =
      (if y = x then ((openGraph ω).degree y.val : ℝ) * g y else 0) -
        if (openGraph ω).Adj y.val x.val then g x else 0 := by
    intro x
    rw [wiredColumn_some_eq, (openGraph ω).adj_comm x.val y.val]
    by_cases hy : y = x
    · subst hy
      simp [mul_comm]
    · by_cases ha : (openGraph ω).Adj y.val x.val <;> simp [hy, ha]
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Steps.S6.realToppling]

/-- For a finite `V ⊂ 𝒞_∞` the wired columns are linearly independent. -/
theorem linearIndependent_wiredColumn {ω : Configuration d}
    (h : HasUniqueInfiniteOpenComponent ω) {V : Finset (Vertex d)}
    (hV : ∀ x ∈ V, x ∈ (uniqueInfiniteComponent h).supp) :
    LinearIndependent ℝ (Steps.S6.wiredColumn ω V) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  refine eq_zero_of_realToppling_eq_zero h hV fun y => ?_
  rw [← sum_mul_wiredColumn_some_wired]
  have hy := congrArg (fun z : EuclideanSpace ℝ (Option V) => z (some y)) hg
  simpa [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply] using hy

/-- step:6.5-upper, wired Laplacian: for a finite `V ⊂ 𝒞_∞` the wired columns are linearly
independent and span the hyperplane `Σ y = 0`. -/
theorem wiredLaplacianStep : Steps.S6.WiredLaplacianStep d := by
  intro ω h V hV
  have hli := linearIndependent_wiredColumn h hV
  refine ⟨hli, fun y hy => ?_⟩
  let ℓ : EuclideanSpace ℝ (Option V) →ₗ[ℝ] ℝ :=
    ∑ o, EuclideanSpace.projₗ o
  have hℓ : ∀ z, ℓ z = ∑ o, z o := fun z => by simp [ℓ]
  have hle : Submodule.span ℝ (Set.range (Steps.S6.wiredColumn ω V)) ≤ LinearMap.ker ℓ := by
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hℓ, sum_wiredColumn]
  have hrange : LinearMap.range ℓ = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro r
    refine ⟨WithLp.toLp 2 (Pi.single none r), ?_⟩
    rw [hℓ, Fintype.sum_option]
    simp
  have hker : Module.finrank ℝ (LinearMap.ker ℓ) = V.card := by
    have := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hrange, finrank_top, Module.finrank_self, finrank_euclideanSpace, Fintype.card_option,
      Fintype.card_coe] at this
    omega
  have heq := Submodule.eq_of_le_of_finrank_eq hle
    (by rw [finrank_span_eq_card hli, Fintype.card_coe, hker])
  rw [heq, LinearMap.mem_ker, hℓ]
  exact hy

end Rigidity.Proofs.S6
