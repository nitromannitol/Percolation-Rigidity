import Rigidity.Proofs.Cluster.PlanarRHMeyers
import Rigidity.Proofs.Cluster.PlanarReachConcentrationHolds
import Rigidity.Proofs.Partition.GeneralPartition

/-!
# The partition `𝓡` of Definition 3.7 of Armstrong and Dario, in dimension two

`PlanarRHFailureBound p A₀` is the bound (2.2) for the local family `planarRHGood A₀` of the cubes
on whose children the reverse Hölder inequality holds: the failure probability at scale `n` is at
most `C exp(-c 3^{n s})`, `0 < s ≤ 1`. The family satisfies (2.1) (`measurableSet_not_mem_planarRHGood_local`),
so Propositions 2.1 and 2.4 (`partition_estimates_general`, `exists_measure_sum_stoppingSize_gt_le`)
apply to it as printed: the maximal stopping cubes of the family form almost surely a partition
`𝓡` of `ℤ²` with comparable neighbours, every predecessor of a cell is in the family, and for every
exponent `t` and every `B` the cells near a triadic cube `□` of scale `k` are small and
`∑_{x ∈ □} size(cell(x))^t ≤ K |□|`, off an event of probability at most `C 3^{-B k}`
(`planarRHPartition_of_failureBound`, the partition `𝓡` of Definition 3.7 with its minimal
scales).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

/-- **The bound (2.2) for the local family of reverse Hölder cubes.** -/
def PlanarRHFailureBound (p : unitInterval) (A₀ : ℝ) : Prop :=
  ∃ C1 c s0 : ℝ, 0 ≤ C1 ∧ 0 < c ∧ 0 < s0 ∧ s0 ≤ 1 ∧ ∀ T : TriadicCube 2,
    latticeBondLaw 2 p {ω | T ∉ planarRHGood A₀ ω} ≤
      ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0))

/-- **The partition `𝓡` of Definition 3.7 with its minimal scales** (Armstrong and Dario,
Definition 3.7 with Propositions 2.1 and 2.4, in dimension two): a cell scale `s` whose cells
`cube (s x) x` form a partition with comparable neighbours, whose predecessors are in the local
family of reverse Hölder cubes, with the moment bounds of Proposition 2.4. -/
def PlanarRHPartition (p : unitInterval) : Prop :=
  ∃ A₀ : ℝ, ∃ s : Configuration 2 → Vertex 2 → ℕ,
    (∀ᵐ ω ∂(latticeBondLaw 2 p),
      (∀ x, ∀ z ∈ cube (s ω x) x, s ω z = s ω x) ∧
      (∀ x y, supDist x y ≤ 1 → s ω y ≤ s ω x + 1) ∧
      ∀ (k : ℕ) (y : Vertex 2), s ω y ≤ k →
        (⟨k, idx k y⟩ : TriadicCube 2) ∈ planarRHGood A₀ ω) ∧
    ∀ t : ℝ, 0 < t → ∃ K : ℝ, 0 ≤ K ∧ ∀ B : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (y : Vertex 2),
      latticeBondLaw 2 p {ω | (∃ z ∈ enl 1 k y, k < s ω z) ∨
          K * (cube k y).card < ∑ x ∈ cube k y, ((3 : ℝ) ^ s ω x) ^ t} ≤
        ENNReal.ofReal (C * ((3 : ℝ) ^ k)⁻¹ ^ B)

/-- The scale of the maximal stopping cube of a family containing a vertex. -/
noncomputable def stoppingScale (G : Set (TriadicCube 2)) (x : Vertex 2) : ℕ :=
  if h : ∃ Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping G then
    (Classical.choose h).scale
  else 0

section Deterministic

variable {G : Set (TriadicCube 2)}
  (hu : ∀ x : Vertex 2, ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping G)

include hu

theorem stoppingScale_spec (x : Vertex 2) :
    (⟨stoppingScale G x, idx (stoppingScale G x) x⟩ : TriadicCube 2).IsMaximalStopping G ∧
      ∀ Q : TriadicCube 2, x ∈ Q.vertices → Q.IsMaximalStopping G →
        Q = ⟨stoppingScale G x, idx (stoppingScale G x) x⟩ := by
  have h : ∃ Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping G := (hu x).exists
  have hQ := Classical.choose_spec h
  have hs : stoppingScale G x = (Classical.choose h).scale := by rw [stoppingScale, dif_pos h]
  have heq : Classical.choose h = ⟨stoppingScale G x, idx (stoppingScale G x) x⟩ := by
    refine TriadicCube.eq_of_mem_of_scale_eq (by rw [hs]) hQ.1 ?_
    exact mem_triadicCube_idx_iff.2 (mem_cube_self _ x)
  refine ⟨heq ▸ hQ.2, fun Q hxQ hQm => ?_⟩
  rw [← heq]
  exact (hu x).unique ⟨hxQ, hQm⟩ hQ

theorem stoppingScale_eq_of_mem_cube {x z : Vertex 2} (hz : z ∈ cube (stoppingScale G x) x) :
    stoppingScale G z = stoppingScale G x := by
  have hzQ : z ∈ (⟨stoppingScale G x, idx (stoppingScale G x) x⟩ : TriadicCube 2).vertices :=
    mem_triadicCube_idx_iff.2 hz
  have h := (stoppingScale_spec hu z).2 _ hzQ (stoppingScale_spec hu x).1
  have := congrArg TriadicCube.scale h
  simp only at this
  exact this.symm

theorem stoppingScale_le_of_supDist {x y : Vertex 2} (hxy : supDist x y ≤ 1) :
    stoppingScale G y ≤ stoppingScale G x + 1 := by
  have hnear : ∀ i, |x i - y i| ≤ 1 := by
    intro i
    have h1 : (x i - y i).natAbs ≤ supDist x y :=
      Finset.le_sup (f := fun i => (x i - y i).natAbs) (Finset.mem_univ i)
    have h2 : (x i - y i).natAbs ≤ 1 := h1.trans hxy
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h2
  have hx := mem_triadicCube_idx_iff.2 (mem_cube_self (stoppingScale G x) x)
  have hy := mem_triadicCube_idx_iff.2 (mem_cube_self (stoppingScale G y) y)
  exact ((stoppingScale_spec hu x).1.1.scales_close_of_near (stoppingScale_spec hu y).1.1 hx hy
    hnear).2

theorem mem_of_stoppingScale_le {y : Vertex 2} {k : ℕ} (hk : stoppingScale G y ≤ k) :
    (⟨k, idx k y⟩ : TriadicCube 2) ∈ G := by
  set Q : TriadicCube 2 := ⟨stoppingScale G y, idx (stoppingScale G y) y⟩ with hQ
  have hQm := (stoppingScale_spec hu y).1
  have hA := TriadicCube.ancestor_mem_stableGood hQm.1.1 (k - stoppingScale G y)
  have hyQ : y ∈ Q.vertices := mem_triadicCube_idx_iff.2 (mem_cube_self _ y)
  have hyA := Q.vertices_subset_ancestor (k - stoppingScale G y) hyQ
  have hsc : (Q.ancestor (k - stoppingScale G y)).scale = k := by
    rw [TriadicCube.scale_ancestor]
    change stoppingScale G y + (k - stoppingScale G y) = k
    omega
  have heq : Q.ancestor (k - stoppingScale G y) = ⟨k, idx k y⟩ :=
    TriadicCube.eq_of_mem_of_scale_eq hsc hyA (mem_triadicCube_idx_iff.2 (mem_cube_self k y))
  rw [← heq]
  exact hA (TriadicCube.mem_influence_self _)

theorem stoppingSize_eq_stoppingScale (x : Vertex 2) :
    TriadicCube.stoppingSize G x = (3 : ℝ) ^ stoppingScale G x :=
  TriadicCube.stoppingSize_eq_of_mem (mem_triadicCube_idx_iff.2 (mem_cube_self _ x))
    (stoppingScale_spec hu x).1

end Deterministic

/-- A stretched exponential times `9^{k+1}` is at most a constant times `(3^{-k})^B`. -/
theorem exists_nine_pow_mul_exp_le {c s : ℝ} (hc : 0 < c) (hs : 0 < s) (B : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ,
      (9 : ℝ) ^ (k + 1) * Real.exp (-c * ((3 : ℝ) ^ k) ^ s) ≤ K * ((3 : ℝ) ^ k)⁻¹ ^ B := by
  obtain ⟨K, hK, h⟩ := exists_exp_neg_rpow_le_inv_pow hc hs (B + 2)
  refine ⟨9 * K, by positivity, fun k => ?_⟩
  have h3 : (0 : ℝ) < 3 ^ k := by positivity
  have e : (9 : ℝ) ^ (k + 1) = 9 * ((3 : ℝ) ^ k) ^ 2 := by
    rw [pow_succ, ← pow_mul, mul_comm, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, mul_comm k 2]
  rw [e]
  calc 9 * ((3 : ℝ) ^ k) ^ 2 * Real.exp (-c * ((3 : ℝ) ^ k) ^ s)
      ≤ 9 * ((3 : ℝ) ^ k) ^ 2 * (K * ((3 : ℝ) ^ k)⁻¹ ^ (B + 2)) :=
        mul_le_mul_of_nonneg_left (h k) (by positivity)
    _ = 9 * K * ((3 : ℝ) ^ k)⁻¹ ^ B * (((3 : ℝ) ^ k) ^ 2 * ((3 : ℝ) ^ k)⁻¹ ^ 2) := by
        rw [pow_add]; ring
    _ = 9 * K * ((3 : ℝ) ^ k)⁻¹ ^ B := by
        rw [← mul_pow, mul_inv_cancel₀ h3.ne', one_pow, mul_one]

/-- **Definition 3.7 with Propositions 2.1 and 2.4 of Armstrong and Dario** for the local family
of reverse Hölder cubes, in dimension two, from the bound (2.2). -/
theorem planarRHPartition_of_failureBound {p : unitInterval} {A₀ : ℝ}
    (hq : PlanarRHFailureBound p A₀) : PlanarRHPartition p := by
  obtain ⟨C1, c, s0, hC1, hc, hs0, hs1, hfail⟩ := hq
  set μ := latticeBondLaw 2 p with hμ
  set G : Configuration 2 → Set (TriadicCube 2) := planarRHGood A₀ with hG
  have hGm : ∀ T : TriadicCube 2, MeasurableSet {ω | T ∈ G ω} := measurableSet_mem_planarRHGood A₀
  have hloc := measurableSet_not_mem_planarRHGood_local A₀
  obtain ⟨hae, ⟨θ, hθ, hmom⟩, -⟩ := partition_estimates_general (d := 2) (by norm_num) μ G hGm
    hC1 hc hs0 hfail
  refine ⟨A₀, fun ω => stoppingScale (G ω), ?_, fun t ht => ?_⟩
  · filter_upwards [hae] with ω hu
    exact ⟨fun x z hz => stoppingScale_eq_of_mem_cube hu hz,
      fun x y hxy => stoppingScale_le_of_supDist hu hxy,
      fun k y hk => mem_of_stoppingScale_le hu hk⟩
  -- the moment bound
  set τ : ℕ := ⌈t⌉₊ with hτ
  have htτ : t ≤ τ := Nat.le_ceil t
  obtain ⟨Cfin, Ctot, hCtot, c', hc', hsum⟩ := exists_measure_sum_stoppingSize_gt_le (d := 2)
    (by norm_num) p G hGm hloc hC1 hc hs0 hs1 hfail τ
  set s' : ℝ := s0 / ((2 * (2 + τ + 1) : ℕ) : ℝ) with hs'
  have hs'0 : 0 < s' := by positivity
  refine ⟨max Cfin 0, le_max_right _ _, fun B => ?_⟩
  obtain ⟨K1, hK1, hK1B⟩ := exists_nine_pow_mul_exp_le (c := θ⁻¹ ^ s0) (by positivity) hs0 B
  obtain ⟨K2, hK2, hK2B⟩ := exists_exp_neg_rpow_le_inv_pow hc' hs'0 B
  refine ⟨2 * K1 + Ctot.toReal * K2, by positivity, fun k y => ?_⟩
  set R : TriadicCube 2 := ⟨k, idx k y⟩ with hR
  have hverts : R.toIntegerCube.vertices = cube k y := Finset.ext fun x => by
    rw [TriadicCube.mem_toIntegerCube_vertices, mem_triadicCube_idx_iff]
  set N₀ := {ω : Configuration 2 | ¬ ∀ x : Vertex 2,
    ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω)} with hN₀
  have hN₀0 : μ N₀ = 0 := ae_iff.1 hae
  set E₁ := ⋃ z ∈ enl 1 k y, {ω : Configuration 2 |
    (3 : ℝ) ^ k < TriadicCube.stoppingSize (G ω) z} with hE₁
  set E₂ := {ω : Configuration 2 | Cfin * 3 ^ (2 * R.scale) <
    ∑ x ∈ R.toIntegerCube.vertices, TriadicCube.stoppingSize (G ω) x ^ τ} with hE₂
  have hsub : {ω | (∃ z ∈ enl 1 k y, k < stoppingScale (G ω) z) ∨
      max Cfin 0 * (cube k y).card < ∑ x ∈ cube k y, ((3 : ℝ) ^ stoppingScale (G ω) x) ^ t} ⊆
      N₀ ∪ (E₁ ∪ E₂) := by
    intro ω hω
    by_cases hu : ∀ x : Vertex 2, ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (G ω)
    · right
      rcases hω with ⟨z, hz, hkz⟩ | hω
      · left
        refine Set.mem_biUnion hz ?_
        change (3 : ℝ) ^ k < TriadicCube.stoppingSize (G ω) z
        rw [stoppingSize_eq_stoppingScale hu]
        exact pow_lt_pow_right₀ (by norm_num) hkz
      · right
        change Cfin * 3 ^ (2 * k) < _
        rw [hverts]
        have hcard : ((cube k y).card : ℝ) = (3 : ℝ) ^ (2 * k) := by
          rw [card_cube, ← pow_mul, mul_comm]
        have h1 : ∑ x ∈ cube k y, ((3 : ℝ) ^ stoppingScale (G ω) x) ^ t ≤
            ∑ x ∈ cube k y, TriadicCube.stoppingSize (G ω) x ^ τ := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [stoppingSize_eq_stoppingScale hu]
          calc ((3 : ℝ) ^ stoppingScale (G ω) x) ^ t
              ≤ ((3 : ℝ) ^ stoppingScale (G ω) x) ^ (τ : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)) htτ
            _ = ((3 : ℝ) ^ stoppingScale (G ω) x) ^ τ := Real.rpow_natCast _ τ
        have h2 : Cfin * (3 : ℝ) ^ (2 * k) ≤ max Cfin 0 * ((cube k y).card : ℝ) := by
          rw [hcard]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        linarith
    · left
      exact hu
  have hE₁ : μ E₁ ≤ ENNReal.ofReal (2 * K1 * ((3 : ℝ) ^ k)⁻¹ ^ B) := by
    have hz : ∀ z, μ {ω : Configuration 2 | (3 : ℝ) ^ k < TriadicCube.stoppingSize (G ω) z} ≤
        ENNReal.ofReal (2 * Real.exp (-(θ⁻¹ ^ s0) * ((3 : ℝ) ^ k) ^ s0)) := by
      intro z
      refine (measure_lt_le_of_exp_rpow_moment μ hθ hs0 (hmom z).1 (hmom z).2
        (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [Real.div_rpow (by positivity) hθ.le, Real.inv_rpow hθ.le]
      apply le_of_eq
      congr 2
      field_simp
    calc μ E₁ ≤ ∑ z ∈ enl 1 k y, μ {ω : Configuration 2 |
          (3 : ℝ) ^ k < TriadicCube.stoppingSize (G ω) z} := measure_biUnion_finset_le _ _
      _ ≤ ∑ _z ∈ enl 1 k y, ENNReal.ofReal (2 * Real.exp (-(θ⁻¹ ^ s0) * ((3 : ℝ) ^ k) ^ s0)) :=
          Finset.sum_le_sum fun z _ => hz z
      _ = ENNReal.ofReal (((enl 1 k y).card : ℝ) *
            (2 * Real.exp (-(θ⁻¹ ^ s0) * ((3 : ℝ) ^ k) ^ s0))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hcard : ((enl 1 k y).card : ℝ) = (9 : ℝ) ^ (k + 1) := by
            rw [card_enl, ← pow_mul, mul_comm, pow_mul]; norm_num
          rw [hcard]
          have := hK1B k
          nlinarith [Real.exp_pos (-(θ⁻¹ ^ s0) * ((3 : ℝ) ^ k) ^ s0)]
  have hE₂ : μ E₂ ≤ ENNReal.ofReal (Ctot.toReal * K2 * ((3 : ℝ) ^ k)⁻¹ ^ B) := by
    refine (hsum R).trans ?_
    conv_lhs => rw [← ENNReal.ofReal_toReal hCtot]
    rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg, mul_assoc]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hK2B k) ENNReal.toReal_nonneg)
  calc μ _ ≤ μ (N₀ ∪ (E₁ ∪ E₂)) := measure_mono hsub
    _ ≤ μ N₀ + (μ E₁ + μ E₂) := (measure_union_le _ _).trans (add_le_add le_rfl
        (measure_union_le _ _))
    _ ≤ 0 + (ENNReal.ofReal (2 * K1 * ((3 : ℝ) ^ k)⁻¹ ^ B) +
          ENNReal.ofReal (Ctot.toReal * K2 * ((3 : ℝ) ^ k)⁻¹ ^ B)) := by
        rw [hN₀0]
        exact add_le_add le_rfl (add_le_add hE₁ hE₂)
    _ = ENNReal.ofReal ((2 * K1 + Ctot.toReal * K2) * ((3 : ℝ) ^ k)⁻¹ ^ B) := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

end Rigidity.Proofs.Cluster
