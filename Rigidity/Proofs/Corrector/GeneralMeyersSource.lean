import Rigidity.Proofs.Corrector.GeneralCaseThree
import PercolationClusterHomogenization.Proofs.Cluster.GeneralMeyersPartition

/-!
# The Meyers estimate with a divergence source on a cube of `ℤᵈ` (replacing Dario's (3.30))

Let `□ = cube k x` carry the homogeneous Meyers estimate (`MeyersCube ε C ω k x`, Armstrong and
Dario, Proposition 3.8), let `U₀ ⊆ 3□` be closed under the open edges inside `3□`, and let `v`
solve `∇·∇v = ∇·ξ` at the vertices of `U₀` all of whose open neighbours lie in `U₀`. Then, with
`p = 1 + ε/2`, the energy `E_v = |∇v|²` on `U₀` satisfies

`avg_□ E_v^p ≤ K ((avg_{3□} E_v)^p + (S / |3□|)^p + S^p / |□|)`, `S = Σ_{b ⊆ U₀ open} ξ(b)²`

(`meyers_source`). This is the estimate (2) used in place of Dario's Proposition 3.6, which does not
hold as printed. The proof splits `v = h + w`: `w` is the potential of the Green projection
`greenProj` for the configuration `restrictConfig ω U₀` keeping the open edges inside `U₀`
(`IsGradOf`), with `Σ E_w ≤ S` (`sum_clusterEnergy_localSolution_le`); `h = v - w` is harmonic at
the interior vertices of `U₀` (`openLaplacian_sub_eq_zero`), so the homogeneous estimate applies to
`h`. This is the argument of the planar file `DarioMeyersSource` on `ℤᵈ`.
-/

namespace Rigidity.Corrector.GeneralDim

open LatticeProb.Percolation Rigidity.Proofs.Cluster
open scoped InnerProductSpace Classical

variable {d : ℕ}

/-! ### The configuration restricted to a set -/

/-- The configuration keeping the open bonds of `ω` with both endpoints in `U`. -/
noncomputable def restrictConfig (ω : Configuration d) (U : Finset (Vertex d)) : Configuration d :=
  fun b => decide (∀ v ∈ b.1, v ∈ U) && ω b

theorem openGraph_restrictConfig_adj {ω : Configuration d} {U : Finset (Vertex d)}
    {x y : Vertex d} :
    (openGraph (restrictConfig ω U)).Adj x y ↔ (openGraph ω).Adj x y ∧ x ∈ U ∧ y ∈ U := by
  constructor
  · rintro ⟨h, ho⟩
    simp only [restrictConfig, Bool.and_eq_true, decide_eq_true_eq] at ho
    have hval : (bondOfAdjacent h).1 = s(x, y) := rfl
    rw [hval] at ho
    exact ⟨⟨h, ho.2⟩, ho.1 x (Sym2.mem_mk_left x y), ho.1 y (Sym2.mem_mk_right x y)⟩
  · rintro ⟨⟨h, ho⟩, hx, hy⟩
    refine ⟨h, ?_⟩
    simp only [restrictConfig, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨fun v hv => ?_, ho⟩
    have hval : (bondOfAdjacent h).1 = s(x, y) := rfl
    rw [hval, Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    exacts [hx, hy]

theorem edgeOpen_restrictConfig_iff {ω : Configuration d} {U : Finset (Vertex d)}
    {a : LatticeEdge d} :
    EdgeOpen (restrictConfig ω U) a ↔ EdgeOpen ω a ∧ a.1 ∈ U ∧ edgeHead a ∈ U :=
  openGraph_restrictConfig_adj

/-! ### The fields of `gradSpace` vanish on the closed edges -/

theorem apply_eq_inner_single (η : EdgeField d) (a : LatticeEdge d) :
    η a = ⟪lp.single 2 a (1 : ℝ), η⟫_ℝ := by
  rw [lp.inner_single_left]
  simp

theorem gradDelta_apply_of_not_open (ω : Configuration d) (z : Vertex d) {a : LatticeEdge d}
    (ha : ¬ EdgeOpen ω a) : gradDelta ω z a = 0 := by
  unfold gradDelta
  rw [lp.coeFn_sum, Finset.sum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [lp.coeFn_sub, Pi.sub_apply]
  have h1 : ((if EdgeOpen ω (z - LatticeProb.unit i, i) then
      lp.single 2 (z - LatticeProb.unit i, i) (1 : ℝ) else 0 : EdgeField d) a) = 0 := by
    split_ifs with ho
    · rw [lp.single_apply, Pi.single_apply, if_neg]
      rintro rfl
      exact ha ho
    · simp
  have h2 : ((if EdgeOpen ω (z, i) then lp.single 2 (z, i) (1 : ℝ) else 0 : EdgeField d) a) = 0 := by
    split_ifs with ho
    · rw [lp.single_apply, Pi.single_apply, if_neg]
      rintro rfl
      exact ha ho
    · simp
  rw [h1, h2, sub_zero]

/-- **The Green projection vanishes on the closed edges.** -/
theorem greenProj_apply_of_not_open (ω : Configuration d) (ξ : EdgeField d) {a : LatticeEdge d}
    (ha : ¬ EdgeOpen ω a) : greenProj ω ξ a = 0 := by
  have hle : Submodule.span ℝ (Set.range (gradDelta ω)) ≤
      LinearMap.ker (innerSL ℝ (lp.single 2 a (1 : ℝ) : EdgeField d) : EdgeField d →ₗ[ℝ] ℝ) := by
    rw [Submodule.span_le]
    rintro _ ⟨z, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      innerSL_apply_apply]
    rw [← apply_eq_inner_single]
    exact gradDelta_apply_of_not_open ω z ha
  have hcl : gradSpace ω ≤
      LinearMap.ker (innerSL ℝ (lp.single 2 a (1 : ℝ) : EdgeField d) : EdgeField d →ₗ[ℝ] ℝ) :=
    Submodule.topologicalClosure_minimal _ hle (ContinuousLinearMap.isClosed_ker _)
  have := hcl (greenProj_mem ω ξ)
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply] at this
  rw [apply_eq_inner_single]
  exact this

/-! ### The local solution -/

/-- The field `ξ` restricted to the edges open in `ω`. -/
noncomputable def restrictField (ω : Configuration d) (ξ : EdgeField d) : EdgeField d :=
  ⟨fun a => if EdgeOpen ω a then ξ a else 0, (lp.memℓp ξ).mono' fun a => by
    split_ifs <;> simp⟩

theorem restrictField_apply (ω : Configuration d) (ξ : EdgeField d) (a : LatticeEdge d) :
    restrictField ω ξ a = if EdgeOpen ω a then ξ a else 0 := rfl

theorem greenProj_restrictField (ω : Configuration d) (ξ : EdgeField d) :
    greenProj ω (restrictField ω ξ) = greenProj ω ξ := by
  refine (eq_greenProj_of_edgeDiv_eq ω (greenProj_mem ω _) fun z => ?_).symm
  rw [edgeDiv_greenProj]
  refine edgeDiv_congr ω (fun b hb => ?_) z
  rw [restrictField_apply, if_pos hb]

theorem norm_greenProj_le_restrictField (ω : Configuration d) (ξ : EdgeField d) :
    ‖greenProj ω ξ‖ ≤ ‖restrictField ω ξ‖ := by
  rw [← greenProj_restrictField]
  exact norm_greenProj_le ω _

/-- At a vertex of `U` all of whose open neighbours are in `U`, the divergence for the restricted
configuration is the divergence for `ω`. -/
theorem edgeDiv_restrictConfig_eq {ω : Configuration d} {U : Finset (Vertex d)} {z : Vertex d}
    (hz : z ∈ U) (hint : ∀ y, (openGraph ω).Adj z y → y ∈ U) (η : LatticeEdge d → ℝ) :
    edgeDiv (restrictConfig ω U) η z = edgeDiv ω η z := by
  unfold edgeDiv
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : EdgeOpen (restrictConfig ω U) (z, i) ↔ EdgeOpen ω (z, i) := by
    rw [edgeOpen_restrictConfig_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, hz, hint _ h⟩⟩
  have h2 : EdgeOpen (restrictConfig ω U) (z - LatticeProb.unit i, i) ↔
      EdgeOpen ω (z - LatticeProb.unit i, i) := by
    rw [edgeOpen_restrictConfig_iff]
    have hh : edgeHead (z - LatticeProb.unit i, i) = z := by simp [edgeHead]
    rw [hh]
    refine ⟨fun h => h.1, fun h => ⟨h, hint _ ?_, hz⟩⟩
    have h' := h
    unfold EdgeOpen at h'
    rw [hh] at h'
    exact h'.symm
  simp only [h1, h2]

theorem openLaplacian_eq_edgeDiv (ω : Configuration d) (u : Vertex d → ℝ) (z : Vertex d) :
    openLaplacian ω u z = edgeDiv ω (edgeGrad ω u) z :=
  laplacian_openGraph_eq_edgeDiv ω u z

/-- **The local solution solves the equation at the interior vertices.** -/
theorem openLaplacian_localSolution {ω : Configuration d} {U : Finset (Vertex d)}
    {ξ : EdgeField d} {w : Vertex d → ℝ}
    (hw : IsGradOf (restrictConfig ω U) (greenProj (restrictConfig ω U) ξ) w) {z : Vertex d}
    (hz : z ∈ U) (hint : ∀ y, (openGraph ω).Adj z y → y ∈ U) :
    openLaplacian ω w z = edgeDiv ω ξ z := by
  rw [openLaplacian_eq_edgeDiv, ← edgeDiv_restrictConfig_eq hz hint,
    ← edgeDiv_restrictConfig_eq hz hint ξ, ← edgeDiv_greenProj (restrictConfig ω U) ξ]
  refine edgeDiv_congr _ (fun b hb => ?_) z
  have hb' := (edgeOpen_restrictConfig_iff.1 hb).1
  simp only [edgeGrad, if_pos hb']
  exact (hw b hb).symm

/-- **`v - w` is harmonic at the interior vertices.** -/
theorem openLaplacian_sub_eq_zero {ω : Configuration d} {U : Finset (Vertex d)}
    {ξ : EdgeField d} {v w : Vertex d → ℝ}
    (hv : ∀ z ∈ U, (∀ y, (openGraph ω).Adj z y → y ∈ U) → openLaplacian ω v z = edgeDiv ω ξ z)
    (hw : IsGradOf (restrictConfig ω U) (greenProj (restrictConfig ω U) ξ) w) :
    ∀ z ∈ U, (∀ y, (openGraph ω).Adj z y → y ∈ U) →
      openLaplacian ω (fun x => v x - w x) z = 0 := by
  intro z hz hint
  have h1 := hv z hz hint
  have h2 := openLaplacian_localSolution hw hz hint
  have e : openLaplacian ω (fun x => v x - w x) z = openLaplacian ω v z - openLaplacian ω w z := by
    unfold openLaplacian
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [e, h1, h2, sub_self]

/-! ### The energy of the local solution -/

/-- A sum over the open neighbours of `x` as a sum over the directions. -/
theorem sum_neighborFinset_eq (ω : Configuration d) (F : Vertex d → ℝ) (x : Vertex d) :
    ∑ y ∈ (openGraph ω).neighborFinset x, F y =
      ∑ i : Fin d, ((if EdgeOpen ω (x, i) then F (x + LatticeProb.unit i) else 0) +
        (if EdgeOpen ω (x - LatticeProb.unit i, i) then F (x - LatticeProb.unit i) else 0)) := by
  rw [openGraph_neighborFinset_eq_filter, Finset.sum_filter,
    Rigidity.Proofs.Regularity.sum_nbrFinset]
  unfold EdgeOpen edgeHead
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [sub_add_cancel, (openGraph ω).adj_comm (x - LatticeProb.unit i) x]

/-- **The energy of the local solution**: `Σ_{x ∈ D} E_w(x) ≤ ‖Pξ‖²`. -/
theorem sum_clusterEnergy_localSolution_le {ω : Configuration d} {U : Finset (Vertex d)}
    {ξ : EdgeField d} {w : Vertex d → ℝ}
    (hw : IsGradOf (restrictConfig ω U) (greenProj (restrictConfig ω U) ξ) w)
    (D : Finset (Vertex d)) :
    ∑ x ∈ D, clusterEnergy ω U w x ≤ ‖greenProj (restrictConfig ω U) ξ‖ ^ 2 := by
  set η := greenProj (restrictConfig ω U) ξ with hη
  set ωU := restrictConfig ω U with hωU
  have hpt : ∀ x, clusterEnergy ω U w x ≤
      1 / 2 * ∑ i : Fin d, (η (x, i) ^ 2 + η (x - LatticeProb.unit i, i) ^ 2) := by
    intro x
    unfold clusterEnergy
    split_ifs with hx
    · unfold clusterGradSq
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have hfilt : ∑ y ∈ ((openGraph ω).neighborFinset x).filter (· ∈ U), (w x - w y) ^ 2 =
          ∑ y ∈ (openGraph ωU).neighborFinset x, (w x - w y) ^ 2 := by
        refine Finset.sum_congr ?_ fun _ _ => rfl
        ext y
        simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, hωU,
          openGraph_restrictConfig_adj]
        tauto
      rw [hfilt, sum_neighborFinset_eq]
      refine Finset.sum_le_sum fun i _ => add_le_add ?_ ?_
      · split_ifs with ho
        · have := hw (x, i) ho
          rw [this]
          change (w x - w (x + LatticeProb.unit i)) ^ 2 ≤ (w (x + LatticeProb.unit i) - w x) ^ 2
          rw [← neg_sub, neg_sq]
        · exact sq_nonneg _
      · split_ifs with ho
        · have := hw (x - LatticeProb.unit i, i) ho
          rw [this]
          have hh : edgeHead (x - LatticeProb.unit i, i) = x := by simp [edgeHead]
          rw [hh]
        · exact sq_nonneg _
    · positivity
  have h1 : ∑ x ∈ D, ∑ i : Fin d, η (x, i) ^ 2 ≤ ‖η‖ ^ 2 := by
    rw [← Finset.sum_product']
    exact sum_sq_le_norm_sq η _
  have h2 : ∑ x ∈ D, ∑ i : Fin d, η (x - LatticeProb.unit i, i) ^ 2 ≤ ‖η‖ ^ 2 := by
    rw [← Finset.sum_product']
    have hinj : Set.InjOn (fun a : Vertex d × Fin d => (a.1 - LatticeProb.unit a.2, a.2))
        ↑(D ×ˢ (Finset.univ : Finset (Fin d))) := by
      rintro ⟨a, i⟩ - ⟨b, j⟩ - h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, rfl⟩ := h
      simp only [Prod.mk.injEq, and_true]
      simpa using h1
    have := sum_sq_le_norm_sq η ((D ×ˢ Finset.univ).image
      fun a : Vertex d × Fin d => (a.1 - LatticeProb.unit a.2, a.2))
    rwa [Finset.sum_image hinj] at this
  calc ∑ x ∈ D, clusterEnergy ω U w x
      ≤ ∑ x ∈ D, 1 / 2 * ∑ i : Fin d, (η (x, i) ^ 2 + η (x - LatticeProb.unit i, i) ^ 2) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = 1 / 2 * (∑ x ∈ D, ∑ i : Fin d, η (x, i) ^ 2 +
          ∑ x ∈ D, ∑ i : Fin d, η (x - LatticeProb.unit i, i) ^ 2) := by
        rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_add_distrib]
    _ ≤ 1 / 2 * (‖η‖ ^ 2 + ‖η‖ ^ 2) := by gcongr
    _ = ‖η‖ ^ 2 := by ring

/-! ### Elementary inequalities -/

theorem rpow_add_le_two_rpow {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    (a + b) ^ p ≤ 2 ^ (p - 1) * (a ^ p + b ^ p) := by
  have h := (convexOn_rpow hp).2 (Set.mem_Ici.2 ha) (Set.mem_Ici.2 hb)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at h
  have e : a + b = 2 * (1 / 2 * a + 1 / 2 * b) := by ring
  rw [e, Real.mul_rpow (by norm_num) (by positivity)]
  have h2 : (2 : ℝ) ^ p = 2 ^ (p - 1) * 2 := by
    rw [← Real.rpow_add_one (by norm_num)]
    ring_nf
  rw [h2]
  calc 2 ^ (p - 1) * 2 * (1 / 2 * a + 1 / 2 * b) ^ p
      ≤ 2 ^ (p - 1) * 2 * (1 / 2 * a ^ p + 1 / 2 * b ^ p) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 ^ (p - 1) * (a ^ p + b ^ p) := by ring

theorem sum_rpow_le_rpow_sum {S : Finset (Vertex d)} {f : Vertex d → ℝ} (hf : ∀ x, 0 ≤ f x)
    {p : ℝ} (hp : 1 ≤ p) : ∑ x ∈ S, f x ^ p ≤ (∑ x ∈ S, f x) ^ p := by
  set T := ∑ x ∈ S, f x with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun x _ => hf x
  rcases hT0.eq_or_lt with h0 | hpos
  · have hz : ∀ x ∈ S, f x = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hf x).1 h0.symm
    rw [← h0, Real.zero_rpow (by linarith)]
    exact (Finset.sum_congr rfl fun x hx => by rw [hz x hx, Real.zero_rpow (by linarith)]).le.trans
      (by simp)
  · have hle : ∀ x ∈ S, f x ^ p ≤ f x * T ^ (p - 1) := by
      intro x hx
      have hxT : f x ≤ T := Finset.single_le_sum (fun y _ => hf y) hx
      rcases (hf x).eq_or_lt with hx0 | hx0
      · rw [← hx0, Real.zero_rpow (by linarith), zero_mul]
      · rw [show f x ^ p = f x * f x ^ (p - 1) by
          rw [← Real.rpow_one_add' hx0.le (by linarith)]; ring_nf]
        exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx0.le hxT (by linarith)) hx0.le
    calc ∑ x ∈ S, f x ^ p ≤ ∑ x ∈ S, f x * T ^ (p - 1) := Finset.sum_le_sum hle
      _ = T * T ^ (p - 1) := by rw [← Finset.sum_mul]
      _ = T ^ p := by
          rw [← Real.rpow_one_add' hpos.le (by linarith)]
          ring_nf

theorem clusterGradSq_add_le (ω : Configuration d) (U : Finset (Vertex d)) (f g : Vertex d → ℝ)
    (x : Vertex d) :
    clusterGradSq ω U (fun y => f y + g y) x ≤ 2 * clusterGradSq ω U f x + 2 * clusterGradSq ω U g x := by
  unfold clusterGradSq
  beta_reduce
  have hs := Finset.sum_le_sum (s := ((openGraph ω).neighborFinset x).filter (· ∈ U))
    (f := fun y => ((f x + g x) - (f y + g y)) ^ 2)
    (g := fun y => 2 * (f x - f y) ^ 2 + 2 * (g x - g y) ^ 2)
    fun y _ => by nlinarith [sq_nonneg (f x - f y - (g x - g y))]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  linarith

theorem clusterEnergy_add_le (ω : Configuration d) (U : Finset (Vertex d)) (f g : Vertex d → ℝ)
    (x : Vertex d) :
    clusterEnergy ω U (fun y => f y + g y) x ≤
      2 * clusterEnergy ω U f x + 2 * clusterEnergy ω U g x := by
  unfold clusterEnergy
  split_ifs
  · exact clusterGradSq_add_le ω U f g x
  · simp

theorem clusterEnergy_neg (ω : Configuration d) (U : Finset (Vertex d)) (f : Vertex d → ℝ)
    (x : Vertex d) : clusterEnergy ω U (fun y => -f y) x = clusterEnergy ω U f x := by
  unfold clusterEnergy clusterGradSq
  split_ifs
  · congr 1
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  · rfl

theorem clusterEnergy_nonneg' (ω : Configuration d) (U : Finset (Vertex d)) (f : Vertex d → ℝ)
    (x : Vertex d) : 0 ≤ clusterEnergy ω U f x := by
  unfold clusterEnergy clusterGradSq
  split_ifs
  · exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  · rfl

/-! ### The estimate -/

/-- **The Meyers estimate with a divergence source** (the estimate used in place of Dario's
Proposition 3.6): on a cube carrying the homogeneous Meyers estimate, for `p = 1 + ε/2`,
`avg_□ E_v^p ≤ K ((avg_{3□} E_v)^p + (S/|3□|)^p + S^p/|□|)`, with `S` the squared norm of `ξ` on
the open edges inside `U₀` and `K = 4^p (4^p C + 1)`. -/
theorem meyers_source {ω : Configuration d} {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) {k : ℕ}
    {x₀ : Vertex d} (hM : GeneralDim.MeyersCube ε C ω k x₀) {U₀ : Finset (Vertex d)}
    (hU : U₀ ⊆ enl 1 k x₀)
    (hcl : ∀ z ∈ U₀, ∀ y, (openGraph ω).Adj z y → y ∈ enl 1 k x₀ → y ∈ U₀)
    (ξ : EdgeField d) {v : Vertex d → ℝ}
    (hv : ∀ z ∈ U₀, (∀ y, (openGraph ω).Adj z y → y ∈ U₀) → openLaplacian ω v z = edgeDiv ω ξ z) :
    avg (cube k x₀) (fun z => clusterEnergy ω U₀ v z ^ (1 + ε / 2)) ≤
      (2 : ℝ) ^ (2 * (1 + ε / 2)) * (C * (2 : ℝ) ^ (2 * (1 + ε / 2)) + 1) *
        (avg (enl 1 k x₀) (clusterEnergy ω U₀ v) ^ (1 + ε / 2) +
          (‖restrictField (restrictConfig ω U₀) ξ‖ ^ 2 / (enl 1 k x₀).card) ^ (1 + ε / 2) +
          (‖restrictField (restrictConfig ω U₀) ξ‖ ^ 2) ^ (1 + ε / 2) / (cube k x₀).card) := by
  set p : ℝ := 1 + ε / 2 with hp
  have hp1 : 1 ≤ p := by rw [hp]; linarith
  set Q := cube k x₀ with hQ
  set D := enl 1 k x₀ with hD
  set S := ‖restrictField (restrictConfig ω U₀) ξ‖ ^ 2 with hS
  have hS0 : 0 ≤ S := sq_nonneg _
  obtain ⟨w, hw⟩ := exists_isGradOf_greenProj (restrictConfig ω U₀) ξ
  set h : Vertex d → ℝ := fun x => v x - w x with hh
  have hharm := openLaplacian_sub_eq_zero hv hw
  have hMh := hM U₀ hU hcl h hharm
  -- energies
  set Ev := clusterEnergy ω U₀ v with hEv
  set Eh := clusterEnergy ω U₀ h with hEh
  set Ew := clusterEnergy ω U₀ w with hEw
  have hEv0 : ∀ x, 0 ≤ Ev x := clusterEnergy_nonneg' ω U₀ v
  have hEh0 : ∀ x, 0 ≤ Eh x := clusterEnergy_nonneg' ω U₀ h
  have hEw0 : ∀ x, 0 ≤ Ew x := clusterEnergy_nonneg' ω U₀ w
  have hvh : ∀ x, Ev x ≤ 2 * Eh x + 2 * Ew x := by
    intro x
    have := clusterEnergy_add_le ω U₀ h w x
    have e : (fun y => h y + w y) = v := by funext y; simp [hh]
    rw [e] at this
    exact this
  have hhv : ∀ x, Eh x ≤ 2 * Ev x + 2 * Ew x := by
    intro x
    have := clusterEnergy_add_le ω U₀ v (fun y => -w y) x
    have e : (fun y => v y + -w y) = h := by funext y; simp [hh, sub_eq_add_neg]
    rw [e, clusterEnergy_neg] at this
    exact this
  have hSw : ∑ x ∈ D, Ew x ≤ S := by
    refine (sum_clusterEnergy_localSolution_le hw D).trans ?_
    rw [hS]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_greenProj_le_restrictField _ ξ) 2
  have hQD : Q ⊆ D := cube_subset_enl 1 k x₀
  have hQpos : (0 : ℝ) < Q.card := by
    have := card_enl 0 k x₀
    have hc : (Q.card : ℝ) = ((3 : ℝ) ^ k) ^ d := by
      rw [hQ]
      have := card_enl 0 k x₀
      simpa [enl, cube] using this
    rw [hc]
    positivity
  have hDpos : (0 : ℝ) < D.card := by
    rw [hD, card_enl]
    positivity
  -- the average of the energy of `w` over `D` and its `p`-th moment over `Q`
  have hwD : avg D Ew ≤ S / D.card := by
    unfold avg
    exact div_le_div_of_nonneg_right hSw hDpos.le
  have hwQ : avg Q (fun z => Ew z ^ p) ≤ S ^ p / Q.card := by
    unfold avg
    refine div_le_div_of_nonneg_right ?_ hQpos.le
    calc ∑ z ∈ Q, Ew z ^ p ≤ (∑ z ∈ Q, Ew z) ^ p := sum_rpow_le_rpow_sum hEw0 hp1
      _ ≤ S ^ p := by
          refine Real.rpow_le_rpow (Finset.sum_nonneg fun z _ => hEw0 z) ?_ (by linarith)
          exact (Finset.sum_le_sum_of_subset_of_nonneg hQD fun z _ _ => hEw0 z).trans hSw
  -- the pointwise convexity
  have hcv : ∀ x, Ev x ^ p ≤ 2 ^ (2 * p - 1) * (Eh x ^ p + Ew x ^ p) := by
    intro x
    calc Ev x ^ p ≤ (2 * Eh x + 2 * Ew x) ^ p :=
          Real.rpow_le_rpow (hEv0 x) (hvh x) (by linarith)
      _ ≤ 2 ^ (p - 1) * ((2 * Eh x) ^ p + (2 * Ew x) ^ p) :=
          rpow_add_le_two_rpow (by linarith [hEh0 x]) (by linarith [hEw0 x]) hp1
      _ = 2 ^ (2 * p - 1) * (Eh x ^ p + Ew x ^ p) := by
          rw [Real.mul_rpow (by norm_num) (hEh0 x), Real.mul_rpow (by norm_num) (hEw0 x),
            show (2 : ℝ) ^ (2 * p - 1) = 2 ^ (p - 1) * 2 ^ p by
              rw [← Real.rpow_add (by norm_num)]; ring_nf]
          ring
  have havgQ : avg Q (fun z => Ev z ^ p) ≤
      2 ^ (2 * p - 1) * (avg Q (fun z => Eh z ^ p) + avg Q (fun z => Ew z ^ p)) := by
    unfold avg
    rw [← add_div, mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ hQpos.le
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => hcv x
  have havgD : avg D Eh ≤ 2 * avg D Ev + 2 * avg D Ew := by
    unfold avg
    rw [mul_div_assoc', mul_div_assoc', ← add_div]
    refine div_le_div_of_nonneg_right ?_ hDpos.le
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun x _ => hhv x
  have havg0 : ∀ (S' : Finset (Vertex d)) (F : Vertex d → ℝ), (∀ x, 0 ≤ F x) → 0 ≤ avg S' F :=
    fun S' F hF => div_nonneg (Finset.sum_nonneg fun x _ => hF x) (Nat.cast_nonneg _)
  have hEhp : avg D Eh ^ p ≤ 2 ^ (2 * p - 1) * (avg D Ev ^ p + (S / D.card) ^ p) := by
    calc avg D Eh ^ p ≤ (2 * avg D Ev + 2 * avg D Ew) ^ p :=
          Real.rpow_le_rpow (havg0 D Eh hEh0) havgD (by linarith)
      _ ≤ 2 ^ (p - 1) * ((2 * avg D Ev) ^ p + (2 * avg D Ew) ^ p) :=
          rpow_add_le_two_rpow (by linarith [havg0 D Ev hEv0]) (by linarith [havg0 D Ew hEw0]) hp1
      _ = 2 ^ (2 * p - 1) * (avg D Ev ^ p + avg D Ew ^ p) := by
          rw [Real.mul_rpow (by norm_num) (havg0 D Ev hEv0),
            Real.mul_rpow (by norm_num) (havg0 D Ew hEw0),
            show (2 : ℝ) ^ (2 * p - 1) = 2 ^ (p - 1) * 2 ^ p by
              rw [← Real.rpow_add (by norm_num)]; ring_nf]
          ring
      _ ≤ 2 ^ (2 * p - 1) * (avg D Ev ^ p + (S / D.card) ^ p) :=
          mul_le_mul_of_nonneg_left (add_le_add le_rfl
            (Real.rpow_le_rpow (havg0 D Ew hEw0) hwD (by linarith))) (by positivity)
  -- assembly
  have h2a : (2 : ℝ) ^ (2 * p - 1) ≤ 2 ^ (2 * p) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hA0 : 0 ≤ avg D Ev ^ p := Real.rpow_nonneg (havg0 D Ev hEv0) _
  have hB0 : 0 ≤ (S / D.card) ^ p := Real.rpow_nonneg (div_nonneg hS0 hDpos.le) _
  have hC0 : 0 ≤ S ^ p / Q.card := div_nonneg (Real.rpow_nonneg hS0 _) hQpos.le
  have h2p : (0 : ℝ) ≤ 2 ^ (2 * p - 1) := by positivity
  have h2p' : (0 : ℝ) ≤ 2 ^ (2 * p) := by positivity
  calc avg Q (fun z => Ev z ^ p)
      ≤ 2 ^ (2 * p - 1) * (avg Q (fun z => Eh z ^ p) + avg Q (fun z => Ew z ^ p)) := havgQ
    _ ≤ 2 ^ (2 * p - 1) * (C * avg D Eh ^ p + S ^ p / Q.card) := by
        gcongr
    _ ≤ 2 ^ (2 * p - 1) * (C * (2 ^ (2 * p - 1) * (avg D Ev ^ p + (S / D.card) ^ p)) +
          S ^ p / Q.card) := by
        gcongr
    _ ≤ 2 ^ (2 * p) * (C * 2 ^ (2 * p) + 1) *
          (avg D Ev ^ p + (S / D.card) ^ p + S ^ p / Q.card) := by
        have e1 : C * (2 ^ (2 * p - 1) * (avg D Ev ^ p + (S / D.card) ^ p)) ≤
            C * 2 ^ (2 * p) * (avg D Ev ^ p + (S / D.card) ^ p) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2a hC) (by positivity)
        have e2 : 2 ^ (2 * p - 1) * (C * (2 ^ (2 * p - 1) * (avg D Ev ^ p + (S / D.card) ^ p)) +
            S ^ p / Q.card) ≤ 2 ^ (2 * p) * (C * 2 ^ (2 * p) * (avg D Ev ^ p + (S / D.card) ^ p) +
            S ^ p / Q.card) :=
          mul_le_mul h2a (add_le_add e1 le_rfl) (by positivity) h2p'
        have hC2 : 0 ≤ C * 2 ^ (2 * p) := by positivity
        have key : C * 2 ^ (2 * p) * (avg D Ev ^ p + (S / D.card) ^ p) + S ^ p / Q.card ≤
            (C * 2 ^ (2 * p) + 1) * (avg D Ev ^ p + (S / D.card) ^ p + S ^ p / Q.card) := by
          have := mul_nonneg hC2 hC0
          nlinarith
        calc 2 ^ (2 * p - 1) * (C * (2 ^ (2 * p - 1) * (avg D Ev ^ p + (S / D.card) ^ p)) +
              S ^ p / Q.card)
            ≤ 2 ^ (2 * p) * (C * 2 ^ (2 * p) * (avg D Ev ^ p + (S / D.card) ^ p) +
              S ^ p / Q.card) := e2
          _ ≤ 2 ^ (2 * p) * ((C * 2 ^ (2 * p) + 1) *
              (avg D Ev ^ p + (S / D.card) ^ p + S ^ p / Q.card)) :=
            mul_le_mul_of_nonneg_left key h2p'
          _ = _ := by ring

end Rigidity.Corrector.GeneralDim
