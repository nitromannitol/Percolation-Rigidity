import Rigidity.Proofs.Corrector.GeneralClusterGreen
import Rigidity.Proofs.Corrector.GeneralCaseFiniteEnergy

/-!
# Dario's identity (3.22) on `ℤᵈ`: the change of the corrector is a multiple of `∇∇G(e, ·)`

Case 3 of Step 2 of Dario's proof of Lemma 3.3: the endpoints `x, y` of the bond `e` are in the
infinite cluster, which does not change when `e` is resampled. By (3.21) the difference `v` of the
two correctors solves `-∇·a∇v = c(δ_x - δ_y)` on the cluster, with
`c = (a - a^e)(e)(p·(x - y) + χ_p^e(x) - χ_p^e(y))`, and Dario asserts (3.22),
`∇v = c ∇∇G(e, ·)`: the function `v - c ∇G(e, ·)` is `a`-harmonic and "one can show" that it has
sublinear growth, so it is constant.

Here, for a configuration in which the oriented edge `a` is open, `∇∇G(e, ·)` is
`greenProj ω (1_a)` (Propositions 2.11-2.12, `GeneralClusterGreen`), and (the argument of the
planar file `DarioCaseThree` on `ℤᵈ`)

* `laplacian_openGraph_eq_edgeDiv`: the Laplacian of the open graph is `∇·∇`;
* `edgeDiv_single`: `∇·1_a = δ_x - δ_y`;
* `edgeGrad_eq_smul_greenProj_of_liouville`: if `∇·∇v = c(δ_x - δ_y)` on a set `C` of vertices on
  which the harmonic functions of sublinear growth are constant, and `v` and the potentials of
  `greenProj ω (1_a)` grow sublinearly on `C`, then `∇v = c greenProj ω (1_a)` on the open edges
  of `C` ((3.22));
* `localEnergy_le_of_isGradOf`: a potential of `η ∈ ℓ²` has energy at most `2‖η‖²` on every finite
  set, so the potentials of `greenProj ω (1_a)` have energy at most `2`, and grow sublinearly
  almost surely (`ae_abs_sub_partitionAnchor_le_of_finiteEnergy`).
-/

namespace Rigidity.Corrector.GeneralDim

open Filter Topology LatticeProb.Percolation Rigidity.Percolation
open scoped InnerProductSpace Classical ENNReal

variable {d : ℕ} (ω : Configuration d)

theorem add_unit_ne_sub_unit (x : Vertex d) (i j : Fin d) :
    x + LatticeProb.unit i ≠ x - LatticeProb.unit j := by
  intro e
  have h := congrArg (fun y : Vertex d => ∑ k, y k) e
  simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    LatticeProb.unit, Finset.sum_pi_single', Finset.mem_univ, if_true] at h
  omega

theorem sub_unit_ne_sub_unit {x : Vertex d} {i j : Fin d} (h : i ≠ j) :
    x - LatticeProb.unit i ≠ x - LatticeProb.unit j := by
  intro e
  have := congrFun e i
  simp [LatticeProb.unit, h] at this

/-- **The Laplacian of the open graph is the divergence of the gradient**:
`Σ_{y ∼ x open} (U(y) - U(x)) = ∇·∇U(x)`. -/
theorem laplacian_openGraph_eq_edgeDiv (U : Vertex d → ℝ) (x : Vertex d) :
    LatticeProb.Graph.laplacian (openGraph ω) U x = edgeDiv ω (edgeGrad ω U) x := by
  rw [laplacian_openGraph_eq_sum_ite, Rigidity.Proofs.Regularity.sum_nbrFinset]
  unfold edgeDiv edgeGrad EdgeOpen edgeHead
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [sub_add_cancel, (openGraph ω).adj_comm (x - LatticeProb.unit i) x]
  split_ifs <;> ring

theorem edgeDiv_congr {η η' : LatticeEdge d → ℝ} (h : ∀ b, EdgeOpen ω b → η b = η' b)
    (z : Vertex d) : edgeDiv ω η z = edgeDiv ω η' z := by
  unfold edgeDiv
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h1 h2 h2
  · rw [h _ h1, h _ h2]
  · rw [h _ h1]
  · rw [h _ h2]
  · rfl

theorem edgeDiv_edgeGrad_sub_smul (u w : Vertex d → ℝ) (c : ℝ) (z : Vertex d) :
    edgeDiv ω (edgeGrad ω (fun y => u y - c * w y)) z =
      edgeDiv ω (edgeGrad ω u) z - c * edgeDiv ω (edgeGrad ω w) z := by
  unfold edgeDiv edgeGrad
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

/-- **`∇·1_a = δ_x - δ_y`** for an open edge `a` from `x` to `y`. -/
theorem edgeDiv_single {a : LatticeEdge d} (ha : EdgeOpen ω a) (z : Vertex d) :
    edgeDiv ω (lp.single 2 a (1 : ℝ) : EdgeField d) z =
      (if z = a.1 then 1 else 0) - (if z = edgeHead a then 1 else 0) := by
  obtain ⟨x, j⟩ := a
  unfold edgeDiv
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single j]
    · by_cases hz : z = x
      · subst hz
        rw [if_pos ha, lp.single_apply, Pi.single_eq_same, if_pos rfl]
      · rw [if_neg hz]
        split_ifs
        · rw [lp.single_apply, Pi.single_eq_of_ne]
          intro e
          exact hz (Prod.mk.inj e).1
        · rfl
    · intro i _ hij
      split_ifs
      · rw [lp.single_apply, Pi.single_eq_of_ne]
        intro e
        exact hij (Prod.mk.inj e).2
      · rfl
    · intro h
      exact absurd (Finset.mem_univ j) h
  · rw [Finset.sum_eq_single j]
    · by_cases hz : z = edgeHead (x, j)
      · have hzx : z - LatticeProb.unit j = x := by
          rw [hz]
          simp [edgeHead]
        rw [hzx, if_pos ha, lp.single_apply, Pi.single_eq_same, if_pos hz]
      · rw [if_neg hz]
        split_ifs
        · rw [lp.single_apply, Pi.single_eq_of_ne]
          intro e
          apply hz
          rw [edgeHead, ← (Prod.mk.inj e).1]
          simp
        · rfl
    · intro i _ hij
      split_ifs
      · rw [lp.single_apply, Pi.single_eq_of_ne]
        intro e
        exact hij (Prod.mk.inj e).2
      · rfl
    · intro h
      exact absurd (Finset.mem_univ j) h

/-- Finite partial sums of the squares of an `ℓ²` field are at most its squared norm. -/
theorem sum_sq_le_norm_sq (η : EdgeField d) (s : Finset (LatticeEdge d)) :
    ∑ a ∈ s, η a ^ 2 ≤ ‖η‖ ^ 2 := by
  have h := lp.sum_rpow_le_norm_rpow (p := 2) (by norm_num) η s
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] at h
  exact h

theorem sum_adj_sq_le (U : Vertex d → ℝ) (F : Finset (Vertex d)) (x : Vertex d) :
    (∑ y ∈ F, if (openGraph ω).Adj x y then (U x - U y) ^ 2 else 0) ≤
      ∑ i : Fin d, ((if EdgeOpen ω (x, i) then (U (edgeHead (x, i)) - U x) ^ 2 else 0) +
        (if EdgeOpen ω (x - LatticeProb.unit i, i) then
          (U (edgeHead (x - LatticeProb.unit i, i)) - U (x - LatticeProb.unit i)) ^ 2 else 0)) := by
  have hsub : F.filter (fun y => (openGraph ω).Adj x y) ⊆
      (LatticeProb.nbrFinset x).filter fun y => (openGraph ω).Adj x y := by
    rw [← openGraph_neighborFinset_eq_filter]
    intro y hy
    exact (SimpleGraph.mem_neighborFinset _ _ _).2 (Finset.mem_filter.1 hy).2
  rw [← Finset.sum_filter]
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)).trans
    (le_of_eq ?_)
  rw [Finset.sum_filter, Rigidity.Proofs.Regularity.sum_nbrFinset]
  unfold EdgeOpen edgeHead
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [sub_add_cancel, (openGraph ω).adj_comm (x - LatticeProb.unit i) x]
  split_ifs <;> ring

/-- **A potential of an `ℓ²` field has finite energy**: `E_F(W) ≤ 2‖η‖²` on every finite set. -/
theorem localEnergy_le_of_isGradOf {η : EdgeField d} {W : Vertex d → ℝ} (h : IsGradOf ω η W)
    (F : Finset (Vertex d)) : localEnergy ω F W ≤ 2 * ‖η‖ ^ 2 := by
  unfold localEnergy
  have hx : ∀ x ∈ F, (∑ y ∈ F, if (openGraph ω).Adj x y then (W x - W y) ^ 2 else 0) ≤
      ∑ i : Fin d, (η (x, i) ^ 2 + η (x - LatticeProb.unit i, i) ^ 2) := by
    intro x _
    refine (sum_adj_sq_le ω W F x).trans (Finset.sum_le_sum fun i _ => ?_)
    refine add_le_add ?_ ?_
    · split_ifs with ho
      · rw [h _ ho]
      · positivity
    · split_ifs with ho
      · rw [h _ ho]
      · positivity
  refine (Finset.sum_le_sum hx).trans ?_
  set g : LatticeEdge d → LatticeEdge d := fun q => (q.1 - LatticeProb.unit q.2, q.2) with hg
  have hginj : Set.InjOn g ↑(F ×ˢ (Finset.univ : Finset (Fin d))) := by
    intro q₁ _ q₂ _ hq
    simp only [hg, Prod.mk.injEq] at hq
    obtain ⟨h1, h2⟩ := hq
    rw [h2] at h1
    exact Prod.ext (sub_left_injective h1) h2
  have e1 : ∑ x ∈ F, ∑ i : Fin d, η (x, i) ^ 2 =
      ∑ q ∈ F ×ˢ (Finset.univ : Finset (Fin d)), η q ^ 2 :=
    (Finset.sum_product F Finset.univ (fun q => η q ^ 2)).symm
  have e2 : ∑ x ∈ F, ∑ i : Fin d, η (x - LatticeProb.unit i, i) ^ 2 =
      ∑ q ∈ (F ×ˢ (Finset.univ : Finset (Fin d))).image g, η q ^ 2 := by
    rw [Finset.sum_image hginj]
    exact (Finset.sum_product F Finset.univ (fun q => η (g q) ^ 2)).symm
  calc ∑ x ∈ F, ∑ i : Fin d, (η (x, i) ^ 2 + η (x - LatticeProb.unit i, i) ^ 2)
      = ∑ x ∈ F, ∑ i : Fin d, η (x, i) ^ 2 +
          ∑ x ∈ F, ∑ i : Fin d, η (x - LatticeProb.unit i, i) ^ 2 := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_add_distrib
    _ ≤ ‖η‖ ^ 2 + ‖η‖ ^ 2 := by
        rw [e1, e2]
        exact add_le_add (sum_sq_le_norm_sq η _) (sum_sq_le_norm_sq η _)
    _ = 2 * ‖η‖ ^ 2 := by ring

/-- Sublinear growth on a set of vertices, `|f(z)| ≤ ε |z|` for `|z|` large. -/
def SublinearOn (C : Set (Vertex d)) (f : Vertex d → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z ∈ C, R ≤ ‖latticeEuclideanEmbedding z‖ →
    |f z| ≤ ε * ‖latticeEuclideanEmbedding z‖

theorem SublinearOn.sub_smul {C : Set (Vertex d)} {f g : Vertex d → ℝ} (hf : SublinearOn C f)
    (hg : SublinearOn C g) (c : ℝ) : SublinearOn C (fun z => f z - c * g z) := by
  intro ε hε
  obtain ⟨R₁, h₁⟩ := hf (ε / 2) (by positivity)
  obtain ⟨R₂, h₂⟩ := hg (ε / (2 * (|c| + 1))) (by positivity)
  refine ⟨max R₁ R₂, fun z hz hR => ?_⟩
  have hR1 := h₁ z hz ((le_max_left _ _).trans hR)
  have hR2 := h₂ z hz ((le_max_right _ _).trans hR)
  have he : 0 ≤ ‖latticeEuclideanEmbedding z‖ := norm_nonneg _
  have hc : |c| * (ε / (2 * (|c| + 1))) ≤ ε / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg c]
  calc |f z - c * g z| ≤ |f z| + |c| * |g z| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ ε / 2 * ‖latticeEuclideanEmbedding z‖ +
        |c| * (ε / (2 * (|c| + 1)) * ‖latticeEuclideanEmbedding z‖) := by
        gcongr
    _ ≤ ε / 2 * ‖latticeEuclideanEmbedding z‖ + ε / 2 * ‖latticeEuclideanEmbedding z‖ := by
        rw [← mul_assoc]
        gcongr
    _ = ε * ‖latticeEuclideanEmbedding z‖ := by ring

/-- **Dario, (3.22)**, deterministic form, for any source field `ξ` with `∇·ξ = δ_x - δ_y`: if
`∇·∇v = c(δ_x - δ_y)` on a set `C` of vertices on which the harmonic functions of sublinear growth
are constant, and `v` and the potentials of `Pξ` grow sublinearly on `C`, then `∇v = c Pξ` on the
open edges of `C`. (For `e` open, `ξ = 1_e`; for `e` closed, `ξ` is the field of a path from `x`
to `y`.) -/
theorem edgeGrad_eq_smul_greenProj_of_div {ξ : EdgeField d} {x y : Vertex d}
    (hξ : ∀ z, edgeDiv ω ξ z = (if z = x then 1 else 0) - (if z = y then 1 else 0))
    {C : Set (Vertex d)}
    (hliou : ∀ h : Vertex d → ℝ, (∀ z ∈ C, edgeDiv ω (edgeGrad ω h) z = 0) →
      SublinearOn C h → ∃ k : ℝ, ∀ z ∈ C, h z = k)
    {v : Vertex d → ℝ} {c : ℝ}
    (hv : ∀ z ∈ C, edgeDiv ω (edgeGrad ω v) z =
      c * ((if z = x then 1 else 0) - (if z = y then 1 else 0)))
    (hvsub : SublinearOn C v)
    (hWsub : ∀ W, IsGradOf ω (greenProj ω ξ) W → SublinearOn C W)
    {b : LatticeEdge d} (hb : EdgeOpen ω b) (hb1 : b.1 ∈ C) (hb2 : edgeHead b ∈ C) :
    edgeGrad ω v b = c * greenProj ω ξ b := by
  obtain ⟨W, hW⟩ := exists_isGradOf_greenProj ω ξ
  have hdivW : ∀ z, edgeDiv ω (edgeGrad ω W) z =
      (if z = x then 1 else 0) - (if z = y then 1 else 0) := by
    intro z
    rw [edgeDiv_congr ω (η' := greenProj ω ξ) (fun b hb => ?_) z, edgeDiv_greenProj, hξ]
    rw [hW b hb]
    simp [edgeGrad, hb]
  have hharm : ∀ z ∈ C, edgeDiv ω (edgeGrad ω (fun y => v y - c * W y)) z = 0 := by
    intro z hz
    rw [edgeDiv_edgeGrad_sub_smul, hv z hz, hdivW z]
    ring
  obtain ⟨k, hk⟩ := hliou _ hharm (hvsub.sub_smul (hWsub W hW) c)
  have h1 := hk _ hb1
  have h2 := hk _ hb2
  simp only [edgeGrad, if_pos hb]
  rw [hW b hb]
  linarith

/-- **Dario, (3.22)**, deterministic form for an open edge `a` (`ξ = 1_a`). -/
theorem edgeGrad_eq_smul_greenProj_of_liouville {a : LatticeEdge d} (ha : EdgeOpen ω a)
    {C : Set (Vertex d)}
    (hliou : ∀ h : Vertex d → ℝ, (∀ z ∈ C, edgeDiv ω (edgeGrad ω h) z = 0) →
      SublinearOn C h → ∃ k : ℝ, ∀ z ∈ C, h z = k)
    {v : Vertex d → ℝ} {c : ℝ}
    (hv : ∀ z ∈ C, edgeDiv ω (edgeGrad ω v) z =
      c * ((if z = a.1 then 1 else 0) - (if z = edgeHead a then 1 else 0)))
    (hvsub : SublinearOn C v)
    (hWsub : ∀ W, IsGradOf ω (greenProj ω (lp.single 2 a 1)) W → SublinearOn C W)
    {b : LatticeEdge d} (hb : EdgeOpen ω b) (hb1 : b.1 ∈ C) (hb2 : edgeHead b ∈ C) :
    edgeGrad ω v b = c * greenProj ω (lp.single 2 a 1) b :=
  edgeGrad_eq_smul_greenProj_of_div ω (edgeDiv_single ω ha) hliou hv hvsub hWsub hb hb1 hb2

end Rigidity.Corrector.GeneralDim
