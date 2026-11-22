import Rigidity.Proofs.Cluster.PlanarRestrictFieldQuad
import Rigidity.Proofs.Cluster.PlanarHolderAway
import Rigidity.Proofs.Percolation.PlanarSolenoidalPairing

/-!
# The sum of the subcube pairings with the solenoidal field

Steps 1–3 of the proof of Lemma 5.7 of Armstrong and Dario, up to display (5.30), in dimension two.
Let `g` be the solenoidal field of scale `n` in direction `e` (equal to `e` near `□_n`, bounded by
`10 |e|₁`, divergence free and supported in `□_{n+1}`), and let `V` run over the nine subcubes of
scale `n` of `□_{n+1}`.
* The pairing of `g` with the gradient of any function over the edges of `□_{n+1}` vanishes
  (`edgePairing_solenoidalField_eq_zero`, display (5.28)).
* Hence `∑_V ⟨∇[u(·, V, q)]_𝒫, g⟩_V` is minus the sum of the crossing term of Step 2 and of the
  differences `⟨∇[u(·, □_{n+1}, q)]_𝒫 - ∇[u(·, V, q)]_𝒫, g⟩_V` of Lemma 5.5.
* With Step 2 (`exists_lintegral_edgePairing_sub_sum_subcubes_le`) and Lemma 5.5 for the pairings
  with a bounded field (`exists_lintegral_planarMuRestrictFieldError_le`, with `m = n + 1`):
  `E[|∑_V |□_n|⁻¹ ⟨∇[u(·, V, q)]_𝒫, g⟩_V|²] ≤ C |e|₁² |q|² (τ_n + 3^{-n/4})`
  (`exists_lintegral_sum_subcube_solenoidal_sq_le`, display (5.30)), for `n ≥ 9`.
The pairings over the subcubes are measurable (`measurable_edgePairing_coarsen_planarMuMinimizer`).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

variable {ω : Configuration 2}

/-- The vertices of the triadic cube of scale `n + 1` centred at the origin. -/
theorem mem_originCube_vertices {n : ℕ} {x : Vertex 2} :
    x ∈ (⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices ↔ ∀ i, |2 * x i| < 3 ^ (n + 1) := by
  rw [TriadicCube.mem_toIntegerCube_vertices]
  change (∀ i, |2 * (x i - (3 : ℤ) ^ (n + 1) * 0)| < 3 ^ (n + 1)) ↔ _
  simp

theorem le_supNorm (x : Vertex 2) (i : Fin 2) : |(x i : ℝ)| ≤ supNorm x := by
  unfold supNorm
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

/-- The solenoidal field of scale `n ≥ 2` vanishes on the edges of `ℤ²` which are not edges of
`□_{n+1}`. -/
theorem solenoidalField_eq_zero_of_edge_not_mem {n : ℕ} (hn : 2 ≤ n) (e : Fin 2 → ℝ)
    {x : Vertex 2} {i : Fin 2}
    (h : ¬ (x ∈ (⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices ∧
      x + unitVertex i ∈ (⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices)) :
    solenoidalField n e x i = 0 := by
  apply solenoidalField_eq_zero
  have h9 : (9 : ℤ) ≤ 3 ^ n := by
    calc (9 : ℤ) = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ n := pow_le_pow_right₀ (by norm_num) hn
  have key : ∃ j : Fin 2, 3 * 3 ^ n ≤ 2 * |x j| + 2 := by
    rw [not_and_or, mem_originCube_vertices, mem_originCube_vertices] at h
    rcases h with h | h
    · push Not at h
      obtain ⟨j, hj⟩ := h
      refine ⟨j, ?_⟩
      rw [abs_mul, abs_two, pow_succ] at hj
      linarith
    · push Not at h
      obtain ⟨j, hj⟩ := h
      refine ⟨j, ?_⟩
      rw [pow_succ] at hj
      have h1 : |2 * (x + unitVertex i) j| ≤ 2 * |x j| + 2 := by
        have : (x + unitVertex i) j = x j + unitVertex i j := rfl
        rw [this, abs_mul, abs_two]
        have hu : |unitVertex i j| ≤ 1 := by
          by_cases hij : j = i
          · subst hij
            simp [unitVertex]
          · simp [unitVertex, hij]
        have := abs_add_le (x j) (unitVertex i j)
        linarith
      linarith
  obtain ⟨j, hj⟩ := key
  have hj' : (3 * 3 ^ n : ℝ) ≤ 2 * |(x j : ℝ)| + 2 := by exact_mod_cast hj
  have h9' : (9 : ℝ) ≤ 3 ^ n := by exact_mod_cast h9
  have := le_supNorm x j
  linarith

/-- **The pairing with the solenoidal field vanishes** (Armstrong and Dario, display (5.28) with
right side `0`, in dimension two): over the edges of `□_{n+1}`, `⟨∇f, g⟩ = 0` for every `f`. -/
theorem edgePairing_solenoidalField_eq_zero {n : ℕ} (hn : 2 ≤ n) (e : Fin 2 → ℝ)
    (f : Vertex 2 → ℝ) :
    edgePairing (⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices (solenoidalField n e) f = 0 := by
  set W := (⟨n + 1, 0⟩ : TriadicCube 2).toIntegerCube.vertices with hW
  have h := tsum_sum_grad_mul_solenoidalField n e f
  rw [tsum_eq_sum (s := W) fun x hx => Finset.sum_eq_zero fun i _ => by
    rw [solenoidalField_eq_zero_of_edge_not_mem hn e (fun h => hx h.1), mul_zero]] at h
  rw [edgePairing]
  refine (Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun i _ => ?_).trans h
  split_ifs with hi
  · ring
  · rw [solenoidalField_eq_zero_of_edge_not_mem hn e (fun h => hi h.2), mul_zero]

/-- The field `g` restricted to the edges inside `D`. -/
noncomputable def restrictField (D : Finset (Vertex 2)) (g : Vertex 2 → Fin 2 → ℝ) :
    Vertex 2 → Fin 2 → ℝ :=
  fun x i => if x ∈ D ∧ x + unitVertex i ∈ D then g x i else 0

/-- The pairing of a field over the edges of a subset `D` of `U` is the field pairing with the
restricted field. -/
theorem edgePairing_coarsen_eq_fieldPairing {U : TriadicCube 2} {D : Finset (Vertex 2)}
    (hDU : D ⊆ U.toIntegerCube.vertices) (g : Vertex 2 → Fin 2 → ℝ) (w : ClusterFun ω U) :
    edgePairing D g (coarsen ω U w) = fieldPairing ω U (restrictField D g) w := by
  rw [fieldPairing_apply, edgePairing]
  symm
  have hterm : ∀ x ∈ U.toIntegerCube.vertices, (∑ i : Fin 2,
      if x + unitVertex i ∈ U.toIntegerCube.vertices then
        restrictField D g x i * (clusterExtend ω U w (planarCoarseAnchor ω (x + unitVertex i)) -
          clusterExtend ω U w (planarCoarseAnchor ω x)) else 0) =
      if x ∈ D then ∑ i : Fin 2, (if x + unitVertex i ∈ D then
        g x i * (coarsen ω U w (x + unitVertex i) - coarsen ω U w x) else 0) else 0 := by
    intro x _
    by_cases hxD : x ∈ D
    · rw [if_pos hxD]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hxi : x + unitVertex i ∈ D
      · rw [if_pos (hDU hxi), if_pos hxi, restrictField, if_pos ⟨hxD, hxi⟩]
        rfl
      · rw [if_neg hxi, restrictField,
          if_neg (show ¬(x ∈ D ∧ x + unitVertex i ∈ D) from fun h => hxi h.2)]
        split_ifs <;> ring
    · rw [if_neg hxD]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [restrictField, if_neg (show ¬(x ∈ D ∧ x + unitVertex i ∈ D) from fun h => hxD h.1)]
      split_ifs <;> ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_mem, Finset.inter_eq_right.2 hDU]

/-- The pairings of a field with the coarsened gradients of the minimizers over a subset of the cube
are measurable. -/
theorem measurable_edgePairing_coarsen_planarMuMinimizer {U : TriadicCube 2}
    {D : Finset (Vertex 2)} (hDU : D ⊆ U.toIntegerCube.vertices) (g : Vertex 2 → Fin 2 → ℝ)
    (q : Fin 2 → ℝ) :
    Measurable fun ω => edgePairing D g (coarsen ω U (planarMuMinimizer ω U q)) := by
  simp only [edgePairing_coarsen_eq_fieldPairing hDU]
  exact measurable_fieldPairing_planarMuMinimizer U q _

theorem measurable_planarMuRestrictFieldError (U : TriadicCube 2) {n : ℕ} (hn : n ≤ U.scale)
    (q : Fin 2 → ℝ) (g : Vertex 2 → Fin 2 → ℝ) :
    Measurable fun ω => planarMuRestrictFieldError ω U n q g := by
  unfold planarMuRestrictFieldError restrictFieldError
  refine measurable_const.mul (Finset.measurable_sum _ fun V hV =>
    ((Measurable.sub ?_ ?_).div_const _).pow_const 2)
  · exact measurable_edgePairing_coarsen_planarMuMinimizer
      (toIntegerCube_vertices_subset_of_mem_subcubesAt hn hV) g q
  · exact measurable_edgePairing_coarsen_planarMuMinimizer subset_rfl g q

end Rigidity.Proofs.Cluster
