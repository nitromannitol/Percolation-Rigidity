import Rigidity.Proofs.Corrector.DarioStepTwoFiniteMoments
import PercolationClusterHomogenization.Proofs.Cluster.BoundedChernoff
import PercolationClusterHomogenization.Proofs.Cluster.PlanarSubcubeIndex

/-!
# Concentration of local bounded variables over a triadic cube

* `indepFun_sum_of_local`: a variable depending only on the bonds inside `U i` is independent
  of the sum of variables depending only on the bonds inside regions `U j` disjoint from `U i`;
* `sum_vertices_add_smul_eq`: the vertices of the cube `⟨m + j, c⟩` are the points
  `3^{m+j} c + a + 3^m b` with `a` a vertex of `⟨m, 0⟩` and `b` a vertex of `⟨j, 0⟩`, each once;
* `measureReal_sum_cube_gt_le`: for variables `X(u)` with values in `[0, A]`, expectations at most
  `ε` and depending only on the bonds inside `B(u, ρ)` with `2ρ + 1 ≤ 3^m`, the points with the
  same `a` are `3^m` apart, so the Chernoff bound applies to each group
  (`measureReal_sum_ge_le_of_bounded`) and
  `P[|Q| t < Σ_{u ∈ Q} X(u)] ≤ 9^m exp(-9^j (t - (e - 1) ε) / A)` for `Q = ⟨m + j, c⟩`.
-/

namespace Rigidity.Corrector

open MeasureTheory ProbabilityTheory Filter LatticeProb.Percolation Rigidity.Percolation
  Rigidity.Proofs.Cluster Rigidity.Proofs.Section5 Rigidity.Poincare Rigidity.External
open scoped Classical ENNReal

/-- **Independence of a local variable from a sum of local variables on disjoint regions.** -/
theorem indepFun_sum_of_local (p : unitInterval) {ι : Type*} (U : ι → Set (Vertex 2))
    (X : ι → Configuration 2 → ℝ) (hXm : ∀ i, Measurable (X i))
    (hloc : ∀ i (ω ω' : Configuration 2), (∀ e ∈ localBonds (U i), ω e = ω' e) →
      X i ω = X i ω')
    {s : Finset ι} (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (U i) (U j))
    {i : ι} (hi : i ∈ s) {T : Finset ι} (hT : T ⊆ s) (hiT : i ∉ T) :
    IndepFun (X i) (fun ω => ∑ j ∈ T, X j ω) (latticeBondLaw 2 p) := by
  set R : Set (Vertex 2) := ⋃ j ∈ T, U j with hR
  have hdR : Disjoint (U i) R := by
    rw [hR, Set.disjoint_iUnion_right]
    intro j
    rw [Set.disjoint_iUnion_right]
    intro hj
    exact hdisj i hi j (hT hj) fun h => hiT (h ▸ hj)
  have hmi : Measurable[localBondSigma (U i)] (X i) :=
    measurable_localBondSigma_of_eq _ (hXm i) (hloc i)
  have hmT : Measurable[localBondSigma R] (fun ω => ∑ j ∈ T, X j ω) := by
    refine measurable_localBondSigma_of_eq _ (Finset.measurable_sum T fun j _ => hXm j)
      fun ω ω' h => Finset.sum_congr rfl fun j hj => ?_
    have hsub : U j ⊆ R := by
      rw [hR]
      exact fun x hx => Set.mem_iUnion₂.2 ⟨j, hj, hx⟩
    exact hloc j ω ω' fun e he => h e (localBonds_mono hsub he)
  exact (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
    (indep_of_indep_of_le_left (indep_localBondSigma p hdR) hmi.comap_le) hmT.comap_le)

theorem mem_cube_toIntegerCube_iff {n : ℕ} {c x : Vertex 2} :
    x ∈ (⟨n, c⟩ : TriadicCube 2).toIntegerCube.vertices ↔
      ∀ i, |2 * (x i - 3 ^ n * c i)| < 3 ^ n := by
  rw [TriadicCube.mem_toIntegerCube_vertices]
  simp only [TriadicCube.vertices, TriadicCube.side, Set.mem_setOf_eq]

/-- The point of `⟨m + j, c⟩` with offset `a` and block `b`. -/
def blockPoint (m j : ℕ) (c a b : Vertex 2) : Vertex 2 :=
  (3 : ℤ) ^ (m + j) • c + a + (3 : ℤ) ^ m • b

theorem blockPoint_apply (m j : ℕ) (c a b : Vertex 2) (i : Fin 2) :
    blockPoint m j c a b i = 3 ^ (m + j) * c i + a i + 3 ^ m * b i := by
  simp [blockPoint]

theorem eq_of_blockPoint_eq {m j : ℕ} {c a a' b b' : Vertex 2}
    (ha : a ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices)
    (ha' : a' ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices)
    (h : blockPoint m j c a b = blockPoint m j c a' b') : a = a' ∧ b = b' := by
  rw [mem_originCube_toIntegerCube_iff] at ha ha'
  have key : ∀ i, a i = a' i ∧ b i = b' i := by
    intro i
    have hi := congrFun h i
    rw [blockPoint_apply, blockPoint_apply] at hi
    have h1 := ha i
    have h2 := ha' i
    have hd : (3 : ℤ) ^ m ∣ a i - a' i := ⟨b' i - b i, by linarith⟩
    have hlt : |a i - a' i| < 3 ^ m := by
      rw [abs_lt] at h1 h2 ⊢
      constructor <;> linarith
    have h0 := Int.eq_zero_of_abs_lt_dvd hd hlt
    have hb : (3 : ℤ) ^ m * (b' i - b i) = 0 := by linarith
    have h3 : (3 : ℤ) ^ m ≠ 0 := by positivity
    have := (mul_eq_zero.1 hb).resolve_left h3
    constructor <;> linarith
  exact ⟨funext fun i => (key i).1, funext fun i => (key i).2⟩

theorem blockPoint_mem {m j : ℕ} {c a b : Vertex 2}
    (ha : a ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices)
    (hb : b ∈ (⟨j, 0⟩ : TriadicCube 2).toIntegerCube.vertices) :
    blockPoint m j c a b ∈ (⟨m + j, c⟩ : TriadicCube 2).toIntegerCube.vertices := by
  rw [mem_originCube_toIntegerCube_iff] at ha hb
  rw [mem_cube_toIntegerCube_iff]
  intro i
  rw [blockPoint_apply]
  have e : 3 ^ (m + j) * c i + a i + 3 ^ m * b i - 3 ^ (m + j) * c i = a i + 3 ^ m * b i := by
    ring
  rw [e, pow_add]
  have h1 := ha i
  have h2 := hb i
  have hs : (0 : ℤ) < 3 ^ m := by positivity
  rw [abs_lt] at h1 h2 ⊢
  have h2a : 2 * b i ≤ 3 ^ j - 1 := by omega
  have h2b : -(3 ^ j - 1) ≤ 2 * b i := by omega
  have h1a : 2 * a i ≤ 3 ^ m - 1 := by omega
  have h1b : -(3 ^ m - 1) ≤ 2 * a i := by omega
  have m1 := mul_le_mul_of_nonneg_left h2a hs.le
  have m2 := mul_le_mul_of_nonneg_left h2b hs.le
  constructor <;> nlinarith

/-- **The vertices of `⟨m + j, c⟩` grouped by their offset in `⟨m, 0⟩`.** -/
theorem sum_vertices_add_smul_eq (m j : ℕ) (c : Vertex 2) (f : Vertex 2 → ℝ) :
    ∑ x ∈ (⟨m + j, c⟩ : TriadicCube 2).toIntegerCube.vertices, f x =
      ∑ a ∈ (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices,
        ∑ b ∈ (⟨j, 0⟩ : TriadicCube 2).toIntegerCube.vertices, f (blockPoint m j c a b) := by
  set A := (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices with hA
  set B := (⟨j, 0⟩ : TriadicCube 2).toIntegerCube.vertices with hB
  set φ : Vertex 2 × Vertex 2 → Vertex 2 := fun q => blockPoint m j c q.1 q.2 with hφ
  have hinj : Set.InjOn φ ↑(A ×ˢ B) := by
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hab hab'
    obtain ⟨h1, h2⟩ := eq_of_blockPoint_eq hab.1 hab'.1 heq
    exact Prod.ext h1 h2
  have hsub : (A ×ˢ B).image φ ⊆ (⟨m + j, c⟩ : TriadicCube 2).toIntegerCube.vertices := by
    intro x hx
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hab
    exact blockPoint_mem ha hb
  have hcard : (⟨m + j, c⟩ : TriadicCube 2).toIntegerCube.vertices.card ≤
      ((A ×ˢ B).image φ).card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_product]
    have h1 : (((⟨m + j, c⟩ : TriadicCube 2).toIntegerCube.vertices.card : ℕ) : ℝ) =
        9 ^ (m + j) := card_toIntegerCube_vertices_eq _
    have h2 : ((A.card : ℕ) : ℝ) = 9 ^ m := card_toIntegerCube_vertices_eq _
    have h3 : ((B.card : ℕ) : ℝ) = 9 ^ j := card_toIntegerCube_vertices_eq _
    have e : (((⟨m + j, c⟩ : TriadicCube 2).toIntegerCube.vertices.card : ℕ) : ℝ) =
        ((A.card * B.card : ℕ) : ℝ) := by
      push_cast
      rw [h1, h2, h3, pow_add]
    exact_mod_cast e.le
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  rw [← heq, Finset.sum_image hinj, Finset.sum_product]

theorem disjoint_supBox_blockPoint {m j ρ : ℕ} (hm : 2 * ρ + 1 ≤ 3 ^ m) {c a b b' : Vertex 2}
    (hbb : b ≠ b') :
    Disjoint (↑(supBox (blockPoint m j c a b) ρ) : Set (Vertex 2))
      ↑(supBox (blockPoint m j c a b') ρ) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hbb
  rw [Set.disjoint_left]
  intro y hy hy'
  rw [Finset.mem_coe, mem_supBox] at hy hy'
  have h1 := hy i
  have h2 := hy' i
  rw [blockPoint_apply] at h1 h2
  have hd : 1 ≤ |b i - b' i| := Int.one_le_abs (sub_ne_zero.2 hi)
  have hs : (0 : ℤ) < 3 ^ m := by positivity
  have hm' : (2 * ρ + 1 : ℤ) ≤ 3 ^ m := by exact_mod_cast hm
  have key : |(3 : ℤ) ^ m * (b i - b' i)| ≤ 2 * ρ := by
    calc |(3 : ℤ) ^ m * (b i - b' i)|
        = |(y i - (3 ^ (m + j) * c i + a i + 3 ^ m * b' i)) -
            (y i - (3 ^ (m + j) * c i + a i + 3 ^ m * b i))| := by ring_nf
      _ ≤ |y i - (3 ^ (m + j) * c i + a i + 3 ^ m * b' i)| +
            |y i - (3 ^ (m + j) * c i + a i + 3 ^ m * b i)| := abs_sub _ _
      _ ≤ ρ + ρ := add_le_add h2 h1
      _ = 2 * ρ := by ring
  rw [abs_mul, abs_of_pos hs] at key
  nlinarith

/-- **The Chernoff bound for local bounded variables over a triadic cube.** -/
theorem measureReal_sum_cube_gt_le (p : unitInterval) (X : Vertex 2 → Configuration 2 → ℝ)
    (hXm : ∀ u, Measurable (X u)) {ρ : ℕ}
    (hloc : ∀ u (ω ω' : Configuration 2),
      (∀ e ∈ localBonds (↑(supBox u ρ) : Set (Vertex 2)), ω e = ω' e) → X u ω = X u ω')
    {A ε : ℝ} (hA : 0 < A) (h0 : ∀ u ω, 0 ≤ X u ω) (h1 : ∀ u ω, X u ω ≤ A)
    (hε : ∀ u, ∫ ω, X u ω ∂latticeBondLaw 2 p ≤ ε) {m j : ℕ} (hm : 2 * ρ + 1 ≤ 3 ^ m)
    (c : Vertex 2) (t : ℝ) :
    (latticeBondLaw 2 p).real {ω |
        (((⟨m + j, c⟩ : TriadicCube 2).toIntegerCube.vertices.card : ℕ) : ℝ) * t <
          ∑ u ∈ (⟨m + j, c⟩ : TriadicCube 2).toIntegerCube.vertices, X u ω} ≤
      9 ^ m * Real.exp (-((9 : ℝ) ^ j * (t - (Real.exp 1 - 1) * ε)) / A) := by
  set Aₘ := (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.vertices with hAₘ
  set B := (⟨j, 0⟩ : TriadicCube 2).toIntegerCube.vertices with hB
  have hcA : ((Aₘ.card : ℕ) : ℝ) = 9 ^ m := card_toIntegerCube_vertices_eq _
  have hcB : ((B.card : ℕ) : ℝ) = 9 ^ j := card_toIntegerCube_vertices_eq _
  have hcQ : (((⟨m + j, c⟩ : TriadicCube 2).toIntegerCube.vertices.card : ℕ) : ℝ) =
      9 ^ m * 9 ^ j := by
    rw [card_toIntegerCube_vertices_eq, pow_add]
  have hgroup : ∀ a ∈ Aₘ, (latticeBondLaw 2 p).real
      {ω | ((B.card : ℕ) : ℝ) * t ≤ ∑ b ∈ B, X (blockPoint m j c a b) ω} ≤
        Real.exp (-(((B.card : ℕ) : ℝ) * (t - (Real.exp 1 - 1) * ε)) / A) := by
    intro a _
    refine measureReal_sum_ge_le_of_bounded B (fun b => X (blockPoint m j c a b))
      (fun b => hXm _) hA (fun b ω => h0 _ ω) (fun b ω => h1 _ ω) (fun b _ => hε _)
      (fun b hb T hT hbT => ?_) t
    exact indepFun_sum_of_local p (fun b => (↑(supBox (blockPoint m j c a b) ρ) : Set (Vertex 2)))
      (fun b => X (blockPoint m j c a b)) (fun b => hXm _) (fun b => hloc _)
      (fun b _ b' _ hbb => disjoint_supBox_blockPoint hm hbb) hb hT hbT
  have hsub : {ω | (((⟨m + j, c⟩ : TriadicCube 2).toIntegerCube.vertices.card : ℕ) : ℝ) * t <
      ∑ u ∈ (⟨m + j, c⟩ : TriadicCube 2).toIntegerCube.vertices, X u ω} ⊆
      ⋃ a ∈ Aₘ, {ω | ((B.card : ℕ) : ℝ) * t ≤ ∑ b ∈ B, X (blockPoint m j c a b) ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rw [sum_vertices_add_smul_eq, hcQ] at hω
    by_contra hne
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_le] at hne
    have : ∑ a ∈ Aₘ, ∑ b ∈ B, X (blockPoint m j c a b) ω ≤
        ∑ _a ∈ Aₘ, ((B.card : ℕ) : ℝ) * t :=
      Finset.sum_le_sum fun a ha => (hne a ha).le
    rw [Finset.sum_const, nsmul_eq_mul, hcA, hcB] at this
    have e : (9 : ℝ) ^ m * 9 ^ j * t = 9 ^ m * (9 ^ j * t) := by ring
    rw [e] at hω
    exact absurd hω (not_lt.2 this)
  calc _ ≤ (latticeBondLaw 2 p).real
        (⋃ a ∈ Aₘ, {ω | ((B.card : ℕ) : ℝ) * t ≤ ∑ b ∈ B, X (blockPoint m j c a b) ω}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ a ∈ Aₘ, (latticeBondLaw 2 p).real
        {ω | ((B.card : ℕ) : ℝ) * t ≤ ∑ b ∈ B, X (blockPoint m j c a b) ω} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _a ∈ Aₘ, Real.exp (-(((B.card : ℕ) : ℝ) * (t - (Real.exp 1 - 1) * ε)) / A) :=
        Finset.sum_le_sum hgroup
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hcA, hcB]

end Rigidity.Corrector
