import Rigidity.Proofs.Cluster.MeyersEstimate
import Rigidity.Proofs.Cluster.ReverseHolderCube

/-!
# The Meyers estimate for harmonic functions on a cluster

We combine the reverse Hölder inequality of Armstrong–Dario, Lemma 3.6
(`reverse_holder_triadic`, with `s = d + 2`) and the Meyers estimate `meyers_triadic` for the energy
density `E = |∇u 1_{𝐚≠0}|²` of a function `u` harmonic on a finite set `U₀` (the cluster
`𝒞_*(□_{m+1})`), extended by zero (`clusterEnergy`). For a cube `□'` of the partition hypothesis,
Lemma 3.6 is applied on a set `U' ⊆ U₀ ∩ 3□'` (the cluster `𝒞_max(3□')`) closed under open edges
inside `3□'` and containing `U₀ ∩ □'`: on `U₀ ∩ □'` the energy densities in `U'` and in `U₀` agree, and
on `U'` the first is at most the second (`reverse_holder_clusterEnergy`). The resulting statement
`meyers_cluster` is Proposition 3.8 with the Sobolev inequality of Proposition 3.4
(`ClusterSobolevTwo`), the moment bounds of the partitions and the cluster geometry as hypotheses.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation
open scoped BigOperators Classical

variable {d : ℕ}

/-- The energy density `|∇u 1_{𝐚≠0}|²` of `u` on `U`, extended by zero outside `U`. -/
noncomputable def clusterEnergy (ω : Configuration d) (U : Finset (Vertex d)) (u : Vertex d → ℝ)
    (x : Vertex d) : ℝ :=
  if x ∈ U then clusterGradSq ω U u x else 0

theorem clusterEnergy_nonneg (ω : Configuration d) (U : Finset (Vertex d)) (u : Vertex d → ℝ)
    (x : Vertex d) : 0 ≤ clusterEnergy ω U u x := by
  unfold clusterEnergy
  split_ifs
  · exact clusterGradSq_nonneg ω U u x
  · exact le_rfl

/-- The energy density decreases when the domain shrinks. -/
theorem clusterGradSq_le_of_subset (ω : Configuration d) {U U' : Finset (Vertex d)}
    (h : U' ⊆ U) (u : Vertex d → ℝ) (x : Vertex d) :
    clusterGradSq ω U' u x ≤ clusterGradSq ω U u x := by
  unfold clusterGradSq
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_
    fun y _ _ => sq_nonneg _) (by norm_num)
  intro y hy
  rw [Finset.mem_filter] at hy ⊢
  exact ⟨hy.1, h hy.2⟩

/-- The energy densities agree at a point all of whose open neighbours in `U` lie in `U' ⊆ U`. -/
theorem clusterGradSq_eq_of_subset (ω : Configuration d) {U U' : Finset (Vertex d)}
    (h : U' ⊆ U) (u : Vertex d → ℝ) {x : Vertex d}
    (hx : ∀ y, (openGraph ω).Adj x y → y ∈ U → y ∈ U') :
    clusterGradSq ω U' u x = clusterGradSq ω U u x := by
  unfold clusterGradSq
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext y
  simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  exact ⟨fun hy => ⟨hy.1, h hy.2⟩, fun hy => ⟨hy.1, hx y hy.1 hy.2⟩⟩

/-- **The reverse Hölder inequality for the energy density** (Armstrong–Dario, Lemma 3.6 with
`s = d + 2`, in the form used by Proposition 3.8). Let `u` be harmonic on `U₀`, and let
`U' ⊆ U₀ ∩ 3□'`, `□' = cube k y`, be closed under open edges inside `3□'` and contain `U₀ ∩ □'`, with
the Sobolev inequality and the moment bound `∑_{U'} size^{2d(d+2)} ≤ C_G |3□'|`. Then
`avg_{□'} E ≤ 8d C_S C_G^{2/((d+2) 2_*)} 3^{d+2} (avg_{3□'} E^{d/(d+1)})^{(d+1)/d}`. -/
theorem reverse_holder_clusterEnergy (ω : Configuration d) (hd : 0 < d) (U₀ : Finset (Vertex d))
    (u : Vertex d → ℝ)
    (hu : ∀ x ∈ U₀, (∀ y, (openGraph ω).Adj x y → y ∈ U₀) → openLaplacian ω u x = 0)
    (k : ℕ) (y : Vertex d) (U' : Finset (Vertex d)) (hU'enl : U' ⊆ enl 1 k y) (hU'U₀ : U' ⊆ U₀)
    (hclosed : ∀ z ∈ U', ∀ w, (openGraph ω).Adj z w → w ∈ enl 1 k y → w ∈ U')
    (hcap : ∀ x ∈ U₀, x ∈ cube k y → x ∈ U') (size : Vertex d → ℝ) (hsize : ∀ x, 0 ≤ size x)
    {CS CG : ℝ} (hCS : 0 ≤ CS) (hCG : 0 ≤ CG) (hSob : ClusterSobolevTwo ω U' size CS)
    (hgood : ∑ x ∈ U', size x ^ (2 * (d : ℝ) * (d + 2)) ≤ CG * (3 : ℝ) ^ ((k + 1) * d)) :
    avg (cube k y) (clusterEnergy ω U₀ u) ≤
      8 * d * CS * CG ^ (2 / (((d : ℝ) + 2) * lowerSobolevTwo d)) * (3 : ℝ) ^ (d + 2) *
        avg (enl 1 k y) (fun x => clusterEnergy ω U₀ u x ^ ((d : ℝ) / (d + 1))) ^
          (((d : ℝ) + 1) / d) := by
  obtain ⟨hst, he1, he2⟩ := reverse_holder_exponents (d := d) hd
  set V := (cube k y).filter (· ∈ U₀) with hV
  have hVU' : V ⊆ U' := fun x hx => hcap x (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hx).1
  have hVcube : V ⊆ cube k y := Finset.filter_subset _ _
  have hu' : ∀ x ∈ U', (∀ w, (openGraph ω).Adj x w → w ∈ U') → openLaplacian ω u x = 0 :=
    fun x hx hall => hu x (hU'U₀ hx) fun w hw => hU'U₀ (hall w hw)
  have hrh := reverse_holder_triadic ω hd k y U' V hVU' hVcube hclosed size hsize hCS hCG hst
    hSob hgood u hu'
  rw [he1, he2] at hrh
  -- the left side
  have hnbr : ∀ x ∈ V, ∀ w, (openGraph ω).Adj x w → w ∈ U₀ → w ∈ U' := by
    intro x hx w hadj _
    refine hclosed x (hVU' hx) w hadj ?_
    have hxc := hVcube hx
    rw [cube, mem_box] at hxc
    rw [enl, mem_box]
    intro i
    have h1 := abs_sub_le_one_of_openGraph_adj hadj i
    have h2 : halfSide (k + 1) = 3 * halfSide k + 1 := rfl
    have h3 := halfSide_nonneg k
    have h4 := abs_sub_le (w i) (x i) (center k y i)
    rw [abs_sub_comm (w i) (x i)] at h4
    linarith [hxc i]
  have hL : ∑ x ∈ cube k y, clusterEnergy ω U₀ u x = ∑ x ∈ V, clusterGradSq ω U' u x := by
    rw [hV, Finset.sum_filter]
    refine Finset.sum_congr rfl fun x hx => ?_
    unfold clusterEnergy
    split_ifs with h
    · exact (clusterGradSq_eq_of_subset ω hU'U₀ u
        (hnbr x (Finset.mem_filter.mpr ⟨hx, h⟩))).symm
    · rfl
  -- the right side
  set θ : ℝ := (d : ℝ) / (d + 1) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hR : ∑ x ∈ U', clusterGradSq ω U' u x ^ θ ≤
      ∑ x ∈ enl 1 k y, clusterEnergy ω U₀ u x ^ θ := by
    calc ∑ x ∈ U', clusterGradSq ω U' u x ^ θ ≤ ∑ x ∈ U', clusterEnergy ω U₀ u x ^ θ := by
          refine Finset.sum_le_sum fun x hx => ?_
          have h1 : clusterEnergy ω U₀ u x = clusterGradSq ω U₀ u x := by
            unfold clusterEnergy
            rw [if_pos (hU'U₀ hx)]
          rw [h1]
          exact Real.rpow_le_rpow (clusterGradSq_nonneg ω U' u x)
            (clusterGradSq_le_of_subset ω hU'U₀ u x) hθ0
      _ ≤ ∑ x ∈ enl 1 k y, clusterEnergy ω U₀ u x ^ θ :=
          Finset.sum_le_sum_of_subset_of_nonneg hU'enl fun x _ _ =>
            Real.rpow_nonneg (clusterEnergy_nonneg ω U₀ u x) _
  have hcube : ((cube k y).card : ℝ) = (3 : ℝ) ^ (k * d) := by rw [card_cube, pow_mul]
  have henl : ((enl 1 k y).card : ℝ) = (3 : ℝ) ^ ((k + 1) * d) := by rw [card_enl, pow_mul]
  have hexp : (0 : ℝ) ≤ ((d : ℝ) + 1) / d := by positivity
  have hC : 0 ≤ 8 * d * CS * CG ^ (2 / (((d : ℝ) + 2) * lowerSobolevTwo d)) * (3 : ℝ) ^ (d + 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hCS) (Real.rpow_nonneg hCG _))
      (by positivity)
  calc avg (cube k y) (clusterEnergy ω U₀ u)
      = (1 / (3 : ℝ) ^ (k * d)) * ∑ x ∈ V, clusterGradSq ω U' u x := by
        rw [avg, hL, hcube]
        ring
    _ ≤ 8 * d * CS * CG ^ (2 / (((d : ℝ) + 2) * lowerSobolevTwo d)) * (3 : ℝ) ^ (d + 2) *
          ((1 / (3 : ℝ) ^ ((k + 1) * d)) * ∑ x ∈ U', clusterGradSq ω U' u x ^ θ) ^
            (((d : ℝ) + 1) / d) := hrh
    _ ≤ 8 * d * CS * CG ^ (2 / (((d : ℝ) + 2) * lowerSobolevTwo d)) * (3 : ℝ) ^ (d + 2) *
          avg (enl 1 k y) (fun x => clusterEnergy ω U₀ u x ^ θ) ^ (((d : ℝ) + 1) / d) := by
        refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ?_ ?_ hexp) hC
        · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ =>
            Real.rpow_nonneg (clusterGradSq_nonneg ω U' u x) _)
        · rw [avg, henl, one_div_mul_eq_div]
          exact div_le_div_of_nonneg_right hR (by positivity)

/-- **The Meyers estimate on a cluster** (Armstrong–Dario, Proposition 3.8, deterministic part, with
the Sobolev inequality of Proposition 3.4 as hypothesis). For `d ≥ 1` and constants `C_S, C_G, K ≥ 0`
there are `ε > 0`, `t > 0` and `C < ∞` with the following property. Let `u` be harmonic on `U₀`, let
the cells `cube (s x) x` of a partition of `ℤ^d` have comparable neighbours and tile `3□`,
`□ = cube n x₀`, let every triadic cube `□'` containing a cell with `3□' ⊆ 3□` carry a set
`U' ⊆ U₀ ∩ 3□'` closed under open edges inside `3□'`, containing `U₀ ∩ □'`, with the Sobolev inequality
of constant `C_S` and `∑_{U'} size^{2d(d+2)} ≤ C_G |3□'|`, and let `∑_{x ∈ □} size(cell(x))^t ≤ K |□|`.
Then, with `E = |∇u 1_{𝐚≠0}|²` on `U₀` (zero outside),
`avg_□ E^{1+ε/2} ≤ C (avg_{3□} E)^{1+ε/2}`. -/
theorem meyers_cluster (hd : 1 ≤ d) {CS CG K : ℝ} (hCS : 0 ≤ CS) (hCG : 0 ≤ CG) (hK : 0 ≤ K) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t : ℝ, 0 < t ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ω : Configuration d) (n : ℕ) (x₀ : Vertex d) (U₀ : Finset (Vertex d))
        (u : Vertex d → ℝ) (s : Vertex d → ℕ) (size : Vertex d → ℝ),
        (∀ x ∈ U₀, (∀ y, (openGraph ω).Adj x y → y ∈ U₀) → openLaplacian ω u x = 0) →
        (∀ x, 0 ≤ size x) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          ∃ U' : Finset (Vertex d), U' ⊆ enl 1 k y ∧ U' ⊆ U₀ ∧
            (∀ z ∈ U', ∀ w, (openGraph ω).Adj z w → w ∈ enl 1 k y → w ∈ U') ∧
            (∀ x ∈ U₀, x ∈ cube k y → x ∈ U') ∧ ClusterSobolevTwo ω U' size CS ∧
            ∑ x ∈ U', size x ^ (2 * (d : ℝ) * (d + 2)) ≤ CG * (3 : ℝ) ^ ((k + 1) * d)) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x => clusterEnergy ω U₀ u x ^ (1 + ε / 2)) ≤
          C * avg (enl 1 n x₀) (clusterEnergy ω U₀ u) ^ (1 + ε / 2) := by
  set A₀ : ℝ := max 1 (8 * d * CS * CG ^ (2 / (((d : ℝ) + 2) * lowerSobolevTwo d)) *
    (3 : ℝ) ^ (d + 2)) with hA₀
  obtain ⟨ε, hε, t, ht, C, hC, hM⟩ := meyers_triadic (d := d) hd (le_max_left 1 _) hK (A₀ := A₀)
  refine ⟨ε, hε, t, ht, C, hC, ?_⟩
  intro ω n x₀ U₀ u s size hu hsize hcell hnb hΩ hcubes hmom
  refine hM n x₀ (clusterEnergy ω U₀ u) s (clusterEnergy_nonneg ω U₀ u) hcell hnb hΩ ?_ hmom
  intro k y hk hsub
  obtain ⟨U', h1, h2, h3, h4, h5, h6⟩ := hcubes k y hk hsub
  have hrh := reverse_holder_clusterEnergy ω (by omega) U₀ u hu k y U' h1 h2 h3 h4 size hsize hCS
    hCG h5 h6
  refine hrh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg ?_ _))
  exact div_nonneg (Finset.sum_nonneg fun x _ =>
    Real.rpow_nonneg (clusterEnergy_nonneg ω U₀ u x) _) (Nat.cast_nonneg _)

end Rigidity.Proofs.Cluster
