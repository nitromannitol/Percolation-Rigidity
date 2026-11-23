import Rigidity.Proofs.Cluster.PlanarReachErrors

/-!
# The subcubes of scale `n` of `□_{n+3+j}` grouped by their position modulo `27`

The subcubes of scale `n` of the triadic cube `□_{n+3+j}` centred at the origin are the cubes
`⟨n, a + 27 b⟩` with `a` an index of `□_3` and `b` an index of `□_j`, each exactly once
(`sum_subcubesAt_eq_sum_sum`). This is the grouping of the subcubes used in Step 2 of the proof
of Lemma 5.11 (`planar_SIupgrade_step2`): cubes with the same `a` are `27 · 3ⁿ` apart, so their
local regions are disjoint.
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped BigOperators Classical

theorem mem_originCube_toIntegerCube_iff {k : ℕ} {a : Vertex 2} :
    a ∈ (⟨k, 0⟩ : TriadicCube 2).toIntegerCube.vertices ↔ ∀ i, |2 * a i| < 3 ^ k := by
  rw [TriadicCube.mem_toIntegerCube_vertices]
  simp only [TriadicCube.vertices, TriadicCube.side, Set.mem_setOf_eq, Pi.zero_apply, mul_zero,
    sub_zero]

/-- The cube `⟨n, a + 27 b⟩` is a subcube of `□_{n+3+j}`. -/
theorem mem_subcubesAt_of_mem {n j : ℕ} {a b : Vertex 2}
    (ha : a ∈ (⟨3, 0⟩ : TriadicCube 2).toIntegerCube.vertices)
    (hb : b ∈ (⟨j, 0⟩ : TriadicCube 2).toIntegerCube.vertices) :
    (⟨n, a + (27 : ℤ) • b⟩ : TriadicCube 2) ∈ subcubesAt ⟨n + 3 + j, 0⟩ n := by
  rw [mem_originCube_toIntegerCube_iff] at ha hb
  set c : Vertex 2 := a + (27 : ℤ) • b with hc
  set x : Vertex 2 := fun i => 3 ^ n * c i with hx
  have hxc : x ∈ (⟨n, c⟩ : TriadicCube 2).vertices := by
    intro i
    simp only [TriadicCube.side, hx, sub_self, mul_zero, abs_zero]
    positivity
  have hxU : x ∈ (⟨n + 3 + j, 0⟩ : TriadicCube 2).toIntegerCube.vertices := by
    rw [mem_originCube_toIntegerCube_iff]
    intro i
    have hbi := hb i
    simp only [hx, hc, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h3 : (0 : ℤ) < 3 ^ n := by positivity
    have e : (3 : ℤ) ^ (n + 3 + j) = 3 ^ n * (27 * 3 ^ j) := by
      rw [pow_add, pow_add]; ring
    rw [e, show 2 * (3 ^ n * (a i + 27 * b i)) = 3 ^ n * (2 * (a i + 27 * b i)) by ring,
      abs_mul, abs_of_pos h3]
    refine mul_lt_mul_of_pos_left ?_ h3
    have h33 : |2 * a i| < 27 := by
      have h' := ha i
      rwa [show ((3 : ℤ) ^ 3) = 27 by norm_num] at h'
    rw [abs_lt] at h33 hbi ⊢
    constructor <;> nlinarith
  refine Finset.mem_image.2 ⟨x, hxU, ?_⟩
  exact TriadicCube.eq_of_mem_of_scale_eq (by rw [scale_scaleCube]) (mem_scaleCube n x) hxc

theorem eq_of_add_smul_eq {a a' b b' : Vertex 2}
    (ha : a ∈ (⟨3, 0⟩ : TriadicCube 2).toIntegerCube.vertices)
    (ha' : a' ∈ (⟨3, 0⟩ : TriadicCube 2).toIntegerCube.vertices)
    (h : a + (27 : ℤ) • b = a' + (27 : ℤ) • b') : a = a' ∧ b = b' := by
  rw [mem_originCube_toIntegerCube_iff] at ha ha'
  have key : ∀ i, a i = a' i ∧ b i = b' i := by
    intro i
    have hi := congrFun h i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    have h1 := ha i
    have h2 := ha' i
    have e : (3 : ℤ) ^ 3 = 27 := by norm_num
    rw [e, abs_lt] at h1 h2
    omega
  exact ⟨funext fun i => (key i).1, funext fun i => (key i).2⟩

/-- **The subcubes of `□_{n+3+j}` of scale `n`, grouped modulo `27`.** -/
theorem sum_subcubesAt_eq_sum_sum (n j : ℕ) (f : TriadicCube 2 → ℝ) :
    ∑ V ∈ subcubesAt ⟨n + 3 + j, 0⟩ n, f V =
      ∑ a ∈ (⟨3, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
        ∑ b ∈ (⟨j, 0⟩ : TriadicCube 2).toIntegerCube.vertices, f ⟨n, a + (27 : ℤ) • b⟩ := by
  set A := (⟨3, 0⟩ : TriadicCube 2).toIntegerCube.vertices with hA
  set B := (⟨j, 0⟩ : TriadicCube 2).toIntegerCube.vertices with hB
  set φ : Vertex 2 × Vertex 2 → TriadicCube 2 := fun q => ⟨n, q.1 + (27 : ℤ) • q.2⟩ with hφ
  have hinj : Set.InjOn φ ↑(A ×ˢ B) := by
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hab hab'
    have h := congrArg TriadicCube.index heq
    obtain ⟨h1, h2⟩ := eq_of_add_smul_eq hab.1 hab'.1 h
    exact Prod.ext h1 h2
  have hsub : (A ×ˢ B).image φ ⊆ subcubesAt ⟨n + 3 + j, 0⟩ n := by
    intro V hV
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hV
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hab
    exact mem_subcubesAt_of_mem ha hb
  have hcard : (subcubesAt ⟨n + 3 + j, 0⟩ n).card ≤ ((A ×ˢ B).image φ).card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product]
    have h1 := card_subcubesAt_mul (U := ⟨n + 3 + j, 0⟩) (n := n) (show n ≤ n + 3 + j by omega)
    have h2 : (A.card : ℝ) = 9 ^ 3 := card_toIntegerCube_vertices_eq _
    have h3 : (B.card : ℝ) = 9 ^ j := card_toIntegerCube_vertices_eq _
    have hvol : (⟨n + 3 + j, 0⟩ : TriadicCube 2).volume = (9 : ℝ) ^ (n + 3 + j) := rfl
    rw [hvol] at h1
    have e : ((subcubesAt ⟨n + 3 + j, 0⟩ n).card : ℝ) = ((A.card * B.card : ℕ) : ℝ) := by
      push_cast
      rw [h2, h3]
      have h9 : (0 : ℝ) < 9 ^ n := by positivity
      have : ((subcubesAt ⟨n + 3 + j, 0⟩ n).card : ℝ) * 9 ^ n = 9 ^ 3 * 9 ^ j * 9 ^ n := by
        rw [h1, ← pow_add, ← pow_add]; ring_nf
      exact mul_right_cancel₀ h9.ne' this
    exact_mod_cast e.le
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  rw [← heq, Finset.sum_image hinj, Finset.sum_product]

end Rigidity.Proofs.Cluster
