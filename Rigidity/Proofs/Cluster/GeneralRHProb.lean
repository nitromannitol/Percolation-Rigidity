import Rigidity.Proofs.Cluster.GeneralRHEvent
import Rigidity.Proofs.Cluster.GeneralReachDomination
import Rigidity.Proofs.Cluster.PartitionReachSupercritical
import Rigidity.Proofs.Partition.GeneralMinimalScaleMain
import Rigidity.Percolation.PolynomialExponential
import Rigidity.Proofs.Partition.GeneralPartition

/-!
# The failure bound of the local reverse Hölder cubes, in every dimension

As Armstrong and Dario bound `P[RH_s(□) > C]` through the minimal scale of the partition `𝒫`
((3.11)–(3.12)), a cube `T` of scale `n` is in the local family `rhGood A₀` as soon as the
partition cubes of the vertices of `3T` have scale at most `n - 3` and
`∑_{3T'} partitionReach^{2d(d+2)} ≤ C_G |3T'|` for every child `T'` (`rhCube_of_scales` on each
child). The first condition fails with probability at most `C |3T| exp(-a 3ⁿ)`, by the exponential
moment of the size of the partition cubes (Proposition 2.1)
(`exists_measure_partitionCube_scale_ge_le`);
the second with a stretched exponential bound, since the reach is dominated by the stopping size of
the partition into coarsely good cubes, whose sums of powers concentrate (Proposition 2.4)
(`exists_measure_sum_reach_enl_gt_le`). The planar case is `PlanarRHProb`.
-/

namespace Rigidity.Proofs.Cluster.GeneralDim

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
open scoped BigOperators Classical ENNReal

variable {d : ℕ}

/-- **Tail of the scale of the partition cubes.** -/
theorem exists_measure_partitionCube_scale_ge_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ a : ℝ, 0 < a ∧ ∀ (n : ℕ) (z : Vertex d),
      latticeBondLaw d p {ω | PartitionEvent ω ∧ n ≤ (partitionCube ω z).scale + 2} ≤
        ENNReal.ofReal (2 * Real.exp (-a * (3 : ℝ) ^ n)) := by
  obtain ⟨θ, hθ, hmom⟩ := exists_partition_size_moment hd hpc
  refine ⟨1 / (27 * θ), by positivity, fun n z => ?_⟩
  have hsub : {ω | PartitionEvent ω ∧ n ≤ (partitionCube ω z).scale + 2} ⊆
      {ω | (3 : ℝ) ^ n / 9 ≤ TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z} := by
    rintro ω ⟨hP, hn⟩
    change (3 : ℝ) ^ n / 9 ≤ TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z
    rw [TriadicCube.stoppingSize_eq_of_mem (partitionCube_spec hP z).1
      (partitionCube_spec hP z).2]
    have h1 : (3 : ℝ) ^ n ≤ 3 ^ ((partitionCube ω z).scale + 2) :=
      pow_le_pow_right₀ (by norm_num) hn
    have h2 : (3 : ℝ) ^ ((partitionCube ω z).scale + 2) = 9 * 3 ^ (partitionCube ω z).scale := by
      ring
    linarith
  have hsub' : {ω | (3 : ℝ) ^ n / 9 ≤ TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z} ⊆
      {ω | (3 : ℝ) ^ n / 9 / 3 < TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z} := by
    intro ω hω
    change (3 : ℝ) ^ n / 9 ≤ _ at hω
    change (3 : ℝ) ^ n / 9 / 3 < _
    have : (0 : ℝ) < 3 ^ n := by positivity
    linarith
  have hint : Integrable (fun ω => Real.exp
      ((TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z / θ) ^ (1 : ℝ)))
      (latticeBondLaw d p) := by
    simpa only [Real.rpow_one] using (hmom z).1
  have hle : (∫ ω, Real.exp ((TriadicCube.stoppingSize (TriadicCube.goodCubes ω) z / θ) ^ (1 : ℝ))
      ∂(latticeBondLaw d p)) ≤ 2 := by
    simpa only [Real.rpow_one] using (hmom z).2
  refine (measure_mono (hsub.trans hsub')).trans ((measure_lt_le_of_exp_rpow_moment _ hθ one_pos
    hint hle (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_))
  rw [Real.rpow_one]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (le_of_eq ?_)) (by norm_num)
  field_simp
  norm_num

/-- The exponent of the reach in the reverse Hölder cubes. -/
def rhReachExp (d : ℕ) : ℕ := 2 * d * (d + 2)

/-- The stretched exponent of the concentration of the reach. -/
noncomputable def rhConcExp (d : ℕ) : ℝ := 1 / ((2 * (d + rhReachExp d + 1) : ℕ) : ℝ)

/-- **Concentration of the powers of the reach on a triple**, stretched exponential. -/
theorem exists_measure_sum_reach_enl_gt_le [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ CG : ℝ, 0 ≤ CG ∧ ∃ Cb b : ℝ, 0 ≤ Cb ∧ 0 < b ∧ ∀ (n : ℕ) (c : Vertex d),
      latticeBondLaw d p {ω | ENNReal.ofReal CG * 3 ^ ((n + 1) * d) <
          ∑ z ∈ enl 1 n c, partitionReach ω z ^ (2 * d * (d + 2))} ≤
        ENNReal.ofReal (Cb * Real.exp (-b * ((3 : ℝ) ^ n) ^ rhConcExp d)) := by
  obtain ⟨C₀, hC₀, c₀, hc₀, hq⟩ := exists_measure_not_mem_coarseGood_le hd hpc
  obtain ⟨Cfin, Ctot, hCtot, c', hc', hsum⟩ := exists_measure_sum_stoppingSize_gt_le (d := d)
    (by omega) p coarseGood measurableSet_mem_coarseGood measurableSet_not_mem_coarseGood_localEdge
    hC₀ hc₀ one_pos le_rfl hq (2 * d * (d + 2))
  have hH : ∀ᵐ ω ∂(latticeBondLaw d p), ∀ x : Vertex d,
      ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (coarseGood ω) :=
    TriadicCube.ae_existsUnique_maximal_stopping_of_side_stretched (latticeBondLaw d p)
      coarseGood (ENNReal.ofReal C₀) ENNReal.ofReal_ne_top 1 c₀ one_pos hc₀ fun R => by
        rw [← ENNReal.ofReal_mul hC₀]
        exact hq R
  have hs : (1 : ℝ) / ((2 * (d + 2 * d * (d + 2) + 1) : ℕ) : ℝ) = rhConcExp d := rfl
  rw [hs] at hsum
  set N : ℕ := d * (2 * (d + rhReachExp d + 1)) with hNdef
  set KN : ℝ := (Nat.factorial N : ℝ) / (c' / 2) ^ N with hKN
  refine ⟨max Cfin 0, le_max_right _ _, 3 ^ d * Ctot.toReal * KN, c' / 2, by positivity,
    by positivity, fun n c => ?_⟩
  set N₀ := {ω : Configuration d | ¬ ∀ x : Vertex d,
    ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (coarseGood ω)} with hN₀
  have hN₀0 : latticeBondLaw d p N₀ = 0 := ae_iff.1 hH
  set E := ⋃ z ∈ enl 1 n c, {ω : Configuration d | Cfin * 3 ^ (d * n) <
    ∑ x ∈ (⟨n, idx n z⟩ : TriadicCube d).toIntegerCube.vertices,
      TriadicCube.stoppingSize (coarseGood ω) x ^ (2 * d * (d + 2))} with hE
  have hcardE : ((enl 1 n c).card : ℝ) = ((3 : ℝ) ^ (n + 1)) ^ d := card_enl 1 n c
  have hsub : {ω | ENNReal.ofReal (max Cfin 0) * 3 ^ ((n + 1) * d) <
      ∑ z ∈ enl 1 n c, partitionReach ω z ^ (2 * d * (d + 2))} ⊆ N₀ ∪ E := by
    intro ω hω
    by_cases hg : ∀ x : Vertex d,
        ∃! Q : TriadicCube d, x ∈ Q.vertices ∧ Q.IsMaximalStopping (coarseGood ω)
    · right
      by_contra hnot
      simp only [hE, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt] at hnot
      rw [Set.mem_setOf_eq] at hω
      refine absurd hω (not_lt.2 ?_)
      have hverts : ∀ z, (⟨n, idx n z⟩ : TriadicCube d).toIntegerCube.vertices = cube n z :=
        fun z => Finset.ext fun x => by
          rw [TriadicCube.mem_toIntegerCube_vertices, mem_triadicCube_idx_iff]
      have hT : ∀ y ∈ enl 1 n c, cube n y ⊆ enl 1 n c := fun y hy => cube_subset_enl_of_mem hy
      set f : Vertex d → ℝ := fun x =>
        TriadicCube.stoppingSize (coarseGood ω) x ^ (2 * d * (d + 2))
      have hf0 : ∀ x, 0 ≤ f x := fun x => pow_nonneg (TriadicCube.stoppingSize_nonneg _ x) _
      have h1 : ∑ z ∈ enl 1 n c, partitionReach ω z ^ (2 * d * (d + 2)) ≤
          ENNReal.ofReal (∑ z ∈ enl 1 n c, f z) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun x _ => hf0 x]
        refine Finset.sum_le_sum fun x _ => ?_
        rw [ENNReal.ofReal_pow (TriadicCube.stoppingSize_nonneg _ x)]
        exact pow_le_pow_left₀ zero_le (partitionReach_le_stoppingSize_coarseGood hg x) _
      have h2 : ∑ z ∈ enl 1 n c, f z ≤ max Cfin 0 * ((3 : ℝ) ^ (n + 1)) ^ d := by
        rw [sum_eq_sum_cube_avg hT f]
        calc ∑ y ∈ enl 1 n c, (∑ x ∈ cube n y, f x) / (cube n y).card
            ≤ ∑ _y ∈ enl 1 n c, max Cfin 0 := Finset.sum_le_sum fun y hy => by
              have hcy : ((cube n y).card : ℝ) = (3 : ℝ) ^ (d * n) := by
                rw [card_cube, ← pow_mul, mul_comm]
              rw [div_le_iff₀ (card_cube_pos n y), hcy]
              have := hnot y hy
              rw [hverts y] at this
              have h3 : Cfin * (3 : ℝ) ^ (d * n) ≤ max Cfin 0 * (3 : ℝ) ^ (d * n) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
              linarith
          _ = max Cfin 0 * ((3 : ℝ) ^ (n + 1)) ^ d := by
              rw [Finset.sum_const, nsmul_eq_mul, hcardE]; ring
      refine h1.trans ?_
      have e : ENNReal.ofReal (max Cfin 0) * 3 ^ ((n + 1) * d) =
          ENNReal.ofReal (max Cfin 0 * ((3 : ℝ) ^ (n + 1)) ^ d) := by
        rw [ENNReal.ofReal_mul (le_max_right _ _), ← pow_mul, ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [e]
      exact ENNReal.ofReal_le_ofReal h2
    · left; exact hg
  have hz : ∀ z, latticeBondLaw d p {ω : Configuration d | Cfin * 3 ^ (d * n) <
      ∑ x ∈ (⟨n, idx n z⟩ : TriadicCube d).toIntegerCube.vertices,
        TriadicCube.stoppingSize (coarseGood ω) x ^ (2 * d * (d + 2))} ≤
      ENNReal.ofReal (Ctot.toReal * Real.exp (-c' * ((3 : ℝ) ^ n) ^ rhConcExp d)) := by
    intro z
    refine (hsum ⟨n, idx n z⟩).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCtot]
  have habs : ((3 : ℝ) ^ (n + 1)) ^ d * Real.exp (-c' * ((3 : ℝ) ^ n) ^ rhConcExp d) ≤
      3 ^ d * KN * Real.exp (-(c' / 2) * ((3 : ℝ) ^ n) ^ rhConcExp d) := by
    set Y : ℝ := ((3 : ℝ) ^ n) ^ rhConcExp d with hY
    have hY0 : 0 ≤ Y := by positivity
    have hpow : ((3 : ℝ) ^ (n + 1)) ^ d = 3 ^ d * Y ^ N := by
      have hr : rhConcExp d * (N : ℝ) = d := by
        rw [rhConcExp, hNdef]
        have hX : (2 * ((d : ℝ) + (rhReachExp d : ℝ) + 1)) ≠ 0 := by positivity
        push_cast
        field_simp
      rw [hY, ← Real.rpow_natCast (((3 : ℝ) ^ n) ^ rhConcExp d) N,
        ← Real.rpow_mul (by positivity), hr, Real.rpow_natCast, pow_succ, mul_pow, mul_comm]
    rw [hpow, mul_assoc]
    have := pow_mul_exp_neg_le N hc' hY0
    calc 3 ^ d * (Y ^ N * Real.exp (-c' * Y)) ≤ 3 ^ d * (KN * Real.exp (-(c' / 2) * Y)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  calc latticeBondLaw d p _ ≤ latticeBondLaw d p (N₀ ∪ E) := measure_mono hsub
    _ ≤ latticeBondLaw d p N₀ + latticeBondLaw d p E := measure_union_le _ _
    _ ≤ 0 + ∑ z ∈ enl 1 n c,
          ENNReal.ofReal (Ctot.toReal * Real.exp (-c' * ((3 : ℝ) ^ n) ^ rhConcExp d)) := by
        rw [hN₀0]
        exact add_le_add le_rfl ((measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun z _ => hz z))
    _ = ENNReal.ofReal (((3 : ℝ) ^ (n + 1)) ^ d *
          (Ctot.toReal * Real.exp (-c' * ((3 : ℝ) ^ n) ^ rhConcExp d))) := by
        rw [zero_add, Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, hcardE,
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hC0 : 0 ≤ Ctot.toReal := ENNReal.toReal_nonneg
        calc ((3 : ℝ) ^ (n + 1)) ^ d * (Ctot.toReal * Real.exp (-c' * ((3 : ℝ) ^ n) ^ rhConcExp d))
            = Ctot.toReal * (((3 : ℝ) ^ (n + 1)) ^ d *
                Real.exp (-c' * ((3 : ℝ) ^ n) ^ rhConcExp d)) := by ring
          _ ≤ Ctot.toReal * (3 ^ d * KN * Real.exp (-(c' / 2) * ((3 : ℝ) ^ n) ^ rhConcExp d)) :=
              mul_le_mul_of_nonneg_left habs hC0
          _ = _ := by ring

/-- **The bound (2.2) for the local family of reverse Hölder cubes.** -/
def RHFailureBound (d : ℕ) (p : unitInterval) (A₀ : ℝ) : Prop :=
  ∃ C1 c s0 : ℝ, 0 ≤ C1 ∧ 0 < c ∧ 0 < s0 ∧ s0 ≤ 1 ∧ ∀ T : TriadicCube d,
    latticeBondLaw d p {ω | T ∉ rhGood A₀ ω} ≤
      ENNReal.ofReal (C1 * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ s0))

theorem triadicCube_eq_idx_center' (T : TriadicCube d) : T = ⟨T.scale, idx T.scale T.center⟩ :=
  TriadicCube.eq_of_mem_of_scale_eq rfl T.center_mem
    (mem_triadicCube_idx_iff.2 (mem_cube_self _ _))

theorem rhConcExp_pos (d : ℕ) : 0 < rhConcExp d := by
  unfold rhConcExp
  positivity

theorem rhConcExp_le_one (d : ℕ) : rhConcExp d ≤ 1 := by
  unfold rhConcExp
  rw [div_le_one (by positivity)]
  have : (1 : ℝ) ≤ ((2 * (d + rhReachExp d + 1) : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * (d + rhReachExp d + 1) by omega)
  exact this

/-- **The bound (2.2) for the local reverse Hölder cubes** (Armstrong and Dario, Lemma 3.6 and
(3.12), in every dimension `d ≥ 2`). -/
theorem rhFailureBound_holds [NeZero d] (hd : 2 ≤ d) {p : unitInterval}
    (hpc : criticalProbability d < (p : ℝ)) :
    ∃ A₀ : ℝ, RHFailureBound d p A₀ := by
  obtain ⟨CS, hCS, hRH⟩ := rhCube_of_scales hd
  obtain ⟨a, ha, hcell⟩ := exists_measure_partitionCube_scale_ge_le hd hpc
  obtain ⟨CG, hCG, Cb, b, hCb, hb, hreach⟩ := exists_measure_sum_reach_enl_gt_le hd hpc
  set A₀ := rhConst d CS (3 ^ d * CG) with hA₀
  set Kd : ℝ := (Nat.factorial d : ℝ) / (a / 2) ^ d with hKd
  have hKd' : 0 ≤ Kd := by positivity
  refine ⟨A₀, 2 * (3 ^ d * Kd) + Cb, min (a / 2) b, rhConcExp d, by positivity,
    lt_min (by positivity) hb, rhConcExp_pos d, rhConcExp_le_one d, fun T => ?_⟩
  rcases Nat.eq_zero_or_pos T.scale with h0 | hpos
  · have hempty : {ω : Configuration d | T ∉ rhGood A₀ ω} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not, rhGood]
      intro k hk
      omega
    rw [hempty, measure_empty]
    exact zero_le
  obtain ⟨k, hk⟩ : ∃ k, T.scale = k + 1 := ⟨T.scale - 1, by omega⟩
  set n := T.scale with hn
  set c : Vertex d := T.center with hc
  have hT := triadicCube_eq_idx_center' T
  set S₁ := {ω : Configuration d | ¬ PartitionEvent ω} with hS₁
  set S₂ := ⋃ z ∈ enl 1 n c, {ω : Configuration d |
    PartitionEvent ω ∧ n ≤ (partitionCube ω z).scale + 2} with hS₂
  set S₃ := {ω : Configuration d | ENNReal.ofReal CG * 3 ^ ((n + 1) * d) <
    ∑ z ∈ enl 1 n c, partitionReach ω z ^ (2 * d * (d + 2))} with hS₃
  have hsub : {ω : Configuration d | T ∉ rhGood A₀ ω} ⊆ S₁ ∪ S₂ ∪ S₃ := by
    intro ω hω
    by_contra hnot
    simp only [hS₁, hS₂, hS₃, Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, not_or,
      not_not, not_exists, not_and, not_le, not_lt] at hnot
    obtain ⟨⟨hP, hcells⟩, hsum⟩ := hnot
    apply hω
    intro k' hk' x hx
    have hkk : k' = k := by omega
    subst hkk
    have hxc : x ∈ cube n c := by
      rw [hT] at hx
      exact mem_triadicCube_idx_iff.1 hx
    have henl : enl 1 k' x ⊆ enl 1 n c :=
      (enl_subset_enl (by omega : k' ≤ n) 1 x).trans (enl_eq_of_mem hxc).le
    refine hRH (CG := 3 ^ d * CG) (by positivity) ω hP k' x (fun z hz => ?_) ?_
    · have := hcells z (henl hz) hP
      omega
    · refine (Finset.sum_le_sum_of_subset henl).trans (hsum.trans (le_of_eq ?_))
      rw [ENNReal.ofReal_mul (by positivity), hk, ENNReal.ofReal_pow (by norm_num),
        ENNReal.ofReal_ofNat, show (k' + 1 + 1) * d = d + (k' + 1) * d by ring, pow_add]
      ring
  have h2 : latticeBondLaw d p S₂ ≤
      ENNReal.ofReal (2 * (3 ^ d * Kd) * Real.exp (-(a / 2) * (3 : ℝ) ^ n)) := by
    calc latticeBondLaw d p S₂ ≤ ∑ z ∈ enl 1 n c, latticeBondLaw d p {ω : Configuration d |
          PartitionEvent ω ∧ n ≤ (partitionCube ω z).scale + 2} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _z ∈ enl 1 n c, ENNReal.ofReal (2 * Real.exp (-a * (3 : ℝ) ^ n)) :=
          Finset.sum_le_sum fun z _ => hcell n z
      _ = ENNReal.ofReal (((3 : ℝ) ^ (n + 1)) ^ d * (2 * Real.exp (-a * (3 : ℝ) ^ n))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast, card_enl,
            ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h9 := pow_mul_exp_neg_le d ha (by positivity : (0 : ℝ) ≤ 3 ^ n)
          rw [← hKd] at h9
          have e : ((3 : ℝ) ^ (n + 1)) ^ d = 3 ^ d * ((3 : ℝ) ^ n) ^ d := by
            rw [pow_succ, mul_pow, mul_comm]
          rw [e]
          calc 3 ^ d * ((3 : ℝ) ^ n) ^ d * (2 * Real.exp (-a * (3 : ℝ) ^ n))
              = 2 * 3 ^ d * (((3 : ℝ) ^ n) ^ d * Real.exp (-a * (3 : ℝ) ^ n)) := by ring
            _ ≤ 2 * 3 ^ d * (Kd * Real.exp (-(a / 2) * (3 : ℝ) ^ n)) :=
                mul_le_mul_of_nonneg_left h9 (by positivity)
            _ = _ := by ring
  have h1 : latticeBondLaw d p S₁ = 0 := ae_iff.1 (ae_partitionEvent hd hpc)
  have hY : ((3 : ℝ) ^ n) ^ rhConcExp d ≤ (3 : ℝ) ^ n := by
    calc ((3 : ℝ) ^ n) ^ rhConcExp d ≤ ((3 : ℝ) ^ n) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (rhConcExp_le_one d)
      _ = (3 : ℝ) ^ n := Real.rpow_one _
  have hY0 : 0 ≤ ((3 : ℝ) ^ n) ^ rhConcExp d := by positivity
  have hm1 : min (a / 2) b ≤ a / 2 := min_le_left _ _
  have hm2 : min (a / 2) b ≤ b := min_le_right _ _
  have hm0 : 0 ≤ min (a / 2) b := le_min (by positivity) hb.le
  have he1 : Real.exp (-(a / 2) * (3 : ℝ) ^ n) ≤
      Real.exp (-min (a / 2) b * ((3 : ℝ) ^ n) ^ rhConcExp d) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul hm1 hY hY0 (by positivity)
    linarith
  have he2 : Real.exp (-b * ((3 : ℝ) ^ n) ^ rhConcExp d) ≤
      Real.exp (-min (a / 2) b * ((3 : ℝ) ^ n) ^ rhConcExp d) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hm2 hY0
    linarith
  calc latticeBondLaw d p {ω | T ∉ rhGood A₀ ω}
      ≤ latticeBondLaw d p (S₁ ∪ S₂ ∪ S₃) := measure_mono hsub
    _ ≤ latticeBondLaw d p S₁ + latticeBondLaw d p S₂ + latticeBondLaw d p S₃ :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ 0 + ENNReal.ofReal (2 * (3 ^ d * Kd) * Real.exp (-(a / 2) * (3 : ℝ) ^ n)) +
          ENNReal.ofReal (Cb * Real.exp (-b * ((3 : ℝ) ^ n) ^ rhConcExp d)) := by
        rw [h1]
        exact add_le_add (add_le_add le_rfl h2) (hreach n c)
    _ = ENNReal.ofReal (2 * (3 ^ d * Kd) * Real.exp (-(a / 2) * (3 : ℝ) ^ n) +
          Cb * Real.exp (-b * ((3 : ℝ) ^ n) ^ rhConcExp d)) := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := mul_le_mul_of_nonneg_left he1 (by positivity : (0 : ℝ) ≤ 2 * (3 ^ d * Kd))
        have := mul_le_mul_of_nonneg_left he2 hCb
        nlinarith

end Rigidity.Proofs.Cluster.GeneralDim
