import Rigidity.Proofs.Cluster.PlanarRHEvent

/-!
# The failure bound of the local reverse Hölder cubes and the partition `𝓡`, in dimension two

As Armstrong and Dario bound `P[RH_s(□) > C]` through the minimal scale of the partition `𝒫`
((3.12), AD18.tex:1459-1466): a cube `T` of scale `n` is in the local family `planarRHGood A₀` as
soon as the planar partition cubes of the vertices of `3T` have scale at most `n - 3` and
`∑_{3T} planarReach^8 ≤ C_G |3T|` (`planarRHCube_of_scales` on each child). The first condition
fails with probability at most `C 9ⁿ exp(-a 3ⁿ)`, by the stretched-exponential moment of the size of
the partition cubes (Proposition 2.1 for the planar partition); the second with probability at most
`C 9ⁿ exp(-b 3^{n/22})`, since the reach is dominated by the size of the partition into coarsely good
cubes, whose sums of powers concentrate (Proposition 2.4). Locality enters only in the
measurability. Hence the bound (2.2) holds (`planarRHFailureBound_holds`), and the partition `𝓡` of
Definition 3.7 exists with its minimal scales (`planarRHPartition_holds`).
-/

namespace Rigidity.Proofs.Cluster

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.External
  Rigidity.Proofs.Section5
open scoped BigOperators Classical ENNReal

/-- A polynomial factor `9^{n+1} = 9 (3ⁿ)²` is absorbed by halving the rate of an exponential. -/
theorem nine_pow_mul_exp_le {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (9 : ℝ) ^ (n + 1) * Real.exp (-a * (3 : ℝ) ^ n) ≤
      9 * ((Nat.factorial 2 : ℝ) / (a / 2) ^ 2) * Real.exp (-(a / 2) * (3 : ℝ) ^ n) := by
  have h := pow_mul_exp_neg_le 2 ha (by positivity : (0 : ℝ) ≤ 3 ^ n)
  have e : (9 : ℝ) ^ (n + 1) = 9 * ((3 : ℝ) ^ n) ^ 2 := by
    rw [pow_succ, ← pow_mul, mul_comm, show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, mul_comm n 2]
  rw [e, mul_assoc]
  calc 9 * (((3 : ℝ) ^ n) ^ 2 * Real.exp (-a * (3 : ℝ) ^ n))
      ≤ 9 * ((Nat.factorial 2 : ℝ) / (a / 2) ^ 2 * Real.exp (-(a / 2) * (3 : ℝ) ^ n)) :=
        mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by ring

/-- **Tail of the scale of the planar partition cubes**, stretched exponential. -/
theorem exists_measure_planarPartCube_scale_ge_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ a : ℝ, 0 < a ∧ ∀ (n : ℕ) (z : Vertex 2),
      latticeBondLaw 2 p {ω | PlanarPartitionEvent ω ∧ n ≤ (planarPartCube ω z).scale + 2} ≤
        ENNReal.ofReal (2 * Real.exp (-a * (3 : ℝ) ^ n)) := by
  obtain ⟨C, hC, c, hc, hgood⟩ := exists_measure_not_mem_planarGoodCubes_le hpc
  have hGm : ∀ T : TriadicCube 2, MeasurableSet {ω : Configuration 2 | T ∈ planarGoodCubes ω} :=
    TriadicCube.measurableSet_mem_goodOfWellConnected planarMeshedFamily
      measurableSet_mem_planarMeshedFamily
  have hq : ∀ T : TriadicCube 2, latticeBondLaw 2 p {ω | T ∉ planarGoodCubes ω} ≤
      ENNReal.ofReal (C.toReal * Real.exp (-c * ((3 : ℝ) ^ T.scale) ^ (1 : ℝ))) := by
    intro T
    rw [Real.rpow_one, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hC]
    exact hgood T
  obtain ⟨-, ⟨θ, hθ, hmom⟩, -⟩ := partition_estimates_general (d := 2) (by norm_num)
    (latticeBondLaw 2 p) (fun ω => planarGoodCubes ω) hGm ENNReal.toReal_nonneg hc one_pos hq
  refine ⟨1 / (81 * θ), by positivity, fun n z => ?_⟩
  have hsub : {ω | PlanarPartitionEvent ω ∧ n ≤ (planarPartCube ω z).scale + 2} ⊆
      {ω | (3 : ℝ) ^ n / 81 < TriadicCube.stoppingSize (planarGoodCubes ω) z} := by
    rintro ω ⟨hP, hn⟩
    change (3 : ℝ) ^ n / 81 < TriadicCube.stoppingSize (planarGoodCubes ω) z
    rw [TriadicCube.stoppingSize_eq_of_mem (planarPartCube_spec hP z).1
      (planarPartCube_spec hP z).2]
    have h1 : (3 : ℝ) ^ n ≤ 3 ^ ((planarPartCube ω z).scale + 2) :=
      pow_le_pow_right₀ (by norm_num) hn
    have h2 : (3 : ℝ) ^ ((planarPartCube ω z).scale + 2) = 9 * 3 ^ (planarPartCube ω z).scale := by
      ring
    have h3 : (0 : ℝ) < 3 ^ (planarPartCube ω z).scale := by positivity
    linarith
  refine (measure_mono hsub).trans ((measure_lt_le_of_exp_rpow_moment _ hθ one_pos (hmom z).1
    (hmom z).2 (by positivity)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  rw [Real.rpow_one]
  congr 2
  field_simp

/-- **Concentration of the eighth powers of the reach on a triple**, stretched exponential. -/
theorem exists_measure_sum_reach_enl_gt_le {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ CG : ℝ, 0 ≤ CG ∧ ∃ Cb b : ℝ, 0 ≤ Cb ∧ 0 < b ∧ ∀ (n : ℕ) (c : Vertex 2),
      latticeBondLaw 2 p {ω | ENNReal.ofReal CG * 3 ^ ((n + 1) * 2) <
          ∑ z ∈ enl 1 n c, planarReach ω z ^ 8} ≤
        ENNReal.ofReal (Cb * Real.exp (-b * ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22))) := by
  obtain ⟨C₀, hC₀, c₀, hc₀, hq⟩ := exists_measure_not_mem_planarCoarseGood_le hpc
  obtain ⟨Cfin, Ctot, hCtot, c', hc', hsum⟩ := exists_measure_sum_stoppingSize_gt_le (d := 2)
    (by norm_num) p planarCoarseGood measurableSet_mem_planarCoarseGood
    measurableSet_not_mem_planarCoarseGood_localEdge hC₀ hc₀ one_pos le_rfl hq 8
  have hH : ∀ᵐ ω ∂(latticeBondLaw 2 p), ∀ x : Vertex 2,
      ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarCoarseGood ω) :=
    TriadicCube.ae_existsUnique_maximal_stopping_of_side_stretched (latticeBondLaw 2 p)
      planarCoarseGood (ENNReal.ofReal C₀) ENNReal.ofReal_ne_top 1 c₀ one_pos hc₀ fun R => by
        rw [← ENNReal.ofReal_mul hC₀]
        exact hq R
  have hs : (1 : ℝ) / ((2 * (2 + 8 + 1) : ℕ) : ℝ) = 1 / 22 := by norm_num
  rw [hs] at hsum
  set K44 : ℝ := (Nat.factorial 44 : ℝ) / (c' / 2) ^ 44 with hK44
  refine ⟨max Cfin 0, le_max_right _ _, 9 * Ctot.toReal * K44, c' / 2, by positivity,
    by positivity, fun n c => ?_⟩
  set N₀ := {ω : Configuration 2 | ¬ ∀ x : Vertex 2,
    ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarCoarseGood ω)} with hN₀
  have hN₀0 : latticeBondLaw 2 p N₀ = 0 := ae_iff.1 hH
  set E := ⋃ z ∈ enl 1 n c, {ω : Configuration 2 | Cfin * 3 ^ (2 * n) <
    ∑ x ∈ (⟨n, idx n z⟩ : TriadicCube 2).toIntegerCube.vertices,
      TriadicCube.stoppingSize (planarCoarseGood ω) x ^ 8} with hE
  have hsub : {ω | ENNReal.ofReal (max Cfin 0) * 3 ^ ((n + 1) * 2) <
      ∑ z ∈ enl 1 n c, planarReach ω z ^ 8} ⊆ N₀ ∪ E := by
    intro ω hω
    by_cases hg : ∀ x : Vertex 2,
        ∃! Q : TriadicCube 2, x ∈ Q.vertices ∧ Q.IsMaximalStopping (planarCoarseGood ω)
    · right
      by_contra hnot
      simp only [hE, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, not_lt] at hnot
      rw [Set.mem_setOf_eq] at hω
      refine absurd hω (not_lt.2 ?_)
      have hverts : ∀ z, (⟨n, idx n z⟩ : TriadicCube 2).toIntegerCube.vertices = cube n z :=
        fun z => Finset.ext fun x => by
          rw [TriadicCube.mem_toIntegerCube_vertices, mem_triadicCube_idx_iff]
      have hT : ∀ y ∈ enl 1 n c, cube n y ⊆ enl 1 n c := fun y hy => cube_subset_enl_of_mem hy
      set f : Vertex 2 → ℝ := fun x => TriadicCube.stoppingSize (planarCoarseGood ω) x ^ 8
      have hf0 : ∀ x, 0 ≤ f x := fun x => pow_nonneg (TriadicCube.stoppingSize_nonneg _ x) 8
      have h1 : ∑ z ∈ enl 1 n c, planarReach ω z ^ 8 ≤ ENNReal.ofReal (∑ z ∈ enl 1 n c, f z) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun x _ => hf0 x]
        refine Finset.sum_le_sum fun x _ => ?_
        rw [ENNReal.ofReal_pow (TriadicCube.stoppingSize_nonneg _ x)]
        exact pow_le_pow_left₀ zero_le (planarReach_le_stoppingSize hg x) 8
      have h2 : ∑ z ∈ enl 1 n c, f z ≤ max Cfin 0 * (9 : ℝ) ^ (n + 1) := by
        rw [sum_eq_sum_cube_avg hT f]
        have hcard : ((enl 1 n c).card : ℝ) = (9 : ℝ) ^ (n + 1) := by
          rw [card_enl, ← pow_mul, mul_comm, pow_mul]; norm_num
        calc ∑ y ∈ enl 1 n c, (∑ x ∈ cube n y, f x) / (cube n y).card
            ≤ ∑ _y ∈ enl 1 n c, max Cfin 0 := Finset.sum_le_sum fun y hy => by
              have hcy : ((cube n y).card : ℝ) = (3 : ℝ) ^ (2 * n) := by
                rw [card_cube, ← pow_mul, mul_comm]
              rw [div_le_iff₀ (card_cube_pos n y), hcy]
              have := hnot y hy
              rw [hverts y] at this
              have h3 : Cfin * (3 : ℝ) ^ (2 * n) ≤ max Cfin 0 * (3 : ℝ) ^ (2 * n) :=
                mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
              linarith
          _ = max Cfin 0 * (9 : ℝ) ^ (n + 1) := by
              rw [Finset.sum_const, nsmul_eq_mul, hcard]; ring
      refine h1.trans ?_
      have e : ENNReal.ofReal (max Cfin 0) * 3 ^ ((n + 1) * 2) =
          ENNReal.ofReal (max Cfin 0 * (9 : ℝ) ^ (n + 1)) := by
        rw [ENNReal.ofReal_mul (le_max_right _ _)]
        congr 1
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul, mul_comm 2 (n + 1),
          ENNReal.ofReal_pow (by norm_num)]
        simp
      rw [e]
      exact ENNReal.ofReal_le_ofReal h2
    · left; exact hg
  have hz : ∀ z, latticeBondLaw 2 p {ω : Configuration 2 | Cfin * 3 ^ (2 * n) <
      ∑ x ∈ (⟨n, idx n z⟩ : TriadicCube 2).toIntegerCube.vertices,
        TriadicCube.stoppingSize (planarCoarseGood ω) x ^ 8} ≤
      ENNReal.ofReal (Ctot.toReal * Real.exp (-c' * ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22))) := by
    intro z
    refine (hsum ⟨n, idx n z⟩).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hCtot]
  have habs : (9 : ℝ) ^ (n + 1) * Real.exp (-c' * ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22)) ≤
      9 * K44 * Real.exp (-(c' / 2) * ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22)) := by
    set Y : ℝ := ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22) with hY
    have hY0 : 0 ≤ Y := by positivity
    have hpow : (9 : ℝ) ^ (n + 1) = 9 * Y ^ 44 := by
      rw [hY, ← Real.rpow_natCast (((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22)) 44,
        ← Real.rpow_mul (by positivity), show (1 : ℝ) / 22 * ((44 : ℕ) : ℝ) = 2 by norm_num,
        show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, pow_succ, ← pow_mul,
        show (9 : ℝ) = 3 ^ 2 by norm_num, ← pow_mul]
      ring
    rw [hpow, mul_assoc]
    have := pow_mul_exp_neg_le 44 hc' hY0
    calc 9 * (Y ^ 44 * Real.exp (-c' * Y)) ≤ 9 * (K44 * Real.exp (-(c' / 2) * Y)) :=
          mul_le_mul_of_nonneg_left this (by norm_num)
      _ = _ := by ring
  calc latticeBondLaw 2 p _ ≤ latticeBondLaw 2 p (N₀ ∪ E) := measure_mono hsub
    _ ≤ latticeBondLaw 2 p N₀ + latticeBondLaw 2 p E := measure_union_le _ _
    _ ≤ 0 + ∑ z ∈ enl 1 n c,
          ENNReal.ofReal (Ctot.toReal * Real.exp (-c' * ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22))) := by
        rw [hN₀0]
        exact add_le_add le_rfl ((measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun z _ => hz z))
    _ = ENNReal.ofReal ((9 : ℝ) ^ (n + 1) *
          (Ctot.toReal * Real.exp (-c' * ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22)))) := by
        rw [zero_add, Finset.sum_const, nsmul_eq_mul]
        have hcard : ((enl 1 n c).card : ℝ≥0∞) = ENNReal.ofReal ((9 : ℝ) ^ (n + 1)) := by
          rw [← ENNReal.ofReal_natCast]
          congr 1
          rw [card_enl, ← pow_mul, mul_comm, pow_mul]
          norm_num
        rw [hcard, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hC0 : 0 ≤ Ctot.toReal := ENNReal.toReal_nonneg
        calc (9 : ℝ) ^ (n + 1) * (Ctot.toReal * Real.exp (-c' * ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22)))
            = Ctot.toReal * ((9 : ℝ) ^ (n + 1) *
                Real.exp (-c' * ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22))) := by ring
          _ ≤ Ctot.toReal * (9 * K44 * Real.exp (-(c' / 2) * ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22))) :=
              mul_le_mul_of_nonneg_left habs hC0
          _ = _ := by ring

theorem triadicCube_eq_idx_center (T : TriadicCube 2) : T = ⟨T.scale, idx T.scale T.center⟩ :=
  TriadicCube.eq_of_mem_of_scale_eq rfl T.center_mem
    (mem_triadicCube_idx_iff.2 (mem_cube_self _ _))

/-- **The bound (2.2) for the local reverse Hölder cubes** (Armstrong and Dario, Lemma 3.6 and
(3.12), in dimension two). -/
theorem planarRHFailureBound_holds {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    ∃ A₀ : ℝ, PlanarRHFailureBound p A₀ := by
  obtain ⟨CS, hCS, hRH⟩ := planarRHCube_of_scales
  obtain ⟨a, ha, hcell⟩ := exists_measure_planarPartCube_scale_ge_le hpc
  obtain ⟨CG, hCG, Cb, b, hCb, hb, hreach⟩ := exists_measure_sum_reach_enl_gt_le hpc
  set A₀ := planarRHConst CS (9 * CG) with hA₀
  set K2 : ℝ := (Nat.factorial 2 : ℝ) / (a / 2) ^ 2 with hK2
  have hK2' : 0 ≤ K2 := by positivity
  refine ⟨A₀, 18 * K2 + Cb, min (a / 2) b, 1 / 22, by positivity, lt_min (by positivity) hb,
    by norm_num, by norm_num, fun T => ?_⟩
  rcases Nat.eq_zero_or_pos T.scale with h0 | hpos
  · have hempty : {ω : Configuration 2 | T ∉ planarRHGood A₀ ω} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not, planarRHGood]
      intro k hk
      omega
    rw [hempty, measure_empty]
    exact zero_le
  obtain ⟨k, hk⟩ : ∃ k, T.scale = k + 1 := ⟨T.scale - 1, by omega⟩
  set n := T.scale with hn
  set c : Vertex 2 := T.center with hc
  have hT := triadicCube_eq_idx_center T
  set S₁ := {ω : Configuration 2 | ¬ PlanarPartitionEvent ω} with hS₁
  set S₂ := ⋃ z ∈ enl 1 n c, {ω : Configuration 2 |
    PlanarPartitionEvent ω ∧ n ≤ (planarPartCube ω z).scale + 2} with hS₂
  set S₃ := {ω : Configuration 2 | ENNReal.ofReal CG * 3 ^ ((n + 1) * 2) <
    ∑ z ∈ enl 1 n c, planarReach ω z ^ 8} with hS₃
  have hsub : {ω : Configuration 2 | T ∉ planarRHGood A₀ ω} ⊆ S₁ ∪ S₂ ∪ S₃ := by
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
    refine hRH (CG := 9 * CG) (by positivity) ω hP k' x (fun z hz => ?_) ?_
    · have := hcells z (henl hz) hP
      omega
    · refine (Finset.sum_le_sum_of_subset henl).trans (hsum.trans (le_of_eq ?_))
      rw [ENNReal.ofReal_mul (by norm_num), hk]
      rw [show (k' + 1 + 1) * 2 = (k' + 1) * 2 + 2 by ring, pow_add]
      norm_num
      ring
  have h2 : latticeBondLaw 2 p S₂ ≤
      ENNReal.ofReal (2 * (9 * K2) * Real.exp (-(a / 2) * (3 : ℝ) ^ n)) := by
    calc latticeBondLaw 2 p S₂ ≤ ∑ z ∈ enl 1 n c, latticeBondLaw 2 p {ω : Configuration 2 |
          PlanarPartitionEvent ω ∧ n ≤ (planarPartCube ω z).scale + 2} :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ _z ∈ enl 1 n c, ENNReal.ofReal (2 * Real.exp (-a * (3 : ℝ) ^ n)) :=
          Finset.sum_le_sum fun z _ => hcell n z
      _ = ENNReal.ofReal ((9 : ℝ) ^ (n + 1) * (2 * Real.exp (-a * (3 : ℝ) ^ n))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          have hcard : ((enl 1 n c).card : ℝ≥0∞) = ENNReal.ofReal ((9 : ℝ) ^ (n + 1)) := by
            rw [← ENNReal.ofReal_natCast]
            congr 1
            rw [card_enl, ← pow_mul, mul_comm, pow_mul]
            norm_num
          rw [hcard, ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          have h9 := nine_pow_mul_exp_le ha n
          rw [← hK2] at h9
          calc (9 : ℝ) ^ (n + 1) * (2 * Real.exp (-a * (3 : ℝ) ^ n))
              = 2 * ((9 : ℝ) ^ (n + 1) * Real.exp (-a * (3 : ℝ) ^ n)) := by ring
            _ ≤ 2 * (9 * K2 * Real.exp (-(a / 2) * (3 : ℝ) ^ n)) :=
                mul_le_mul_of_nonneg_left h9 (by norm_num)
            _ = _ := by ring
  have h1 : latticeBondLaw 2 p S₁ = 0 := ae_iff.1 (ae_planarPartitionEvent hpc)
  have hY : ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22) ≤ (3 : ℝ) ^ n := by
    calc ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22) ≤ ((3 : ℝ) ^ n) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by norm_num)
      _ = (3 : ℝ) ^ n := Real.rpow_one _
  have hY0 : 0 ≤ ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22) := by positivity
  have hm1 : min (a / 2) b ≤ a / 2 := min_le_left _ _
  have hm2 : min (a / 2) b ≤ b := min_le_right _ _
  have hm0 : 0 ≤ min (a / 2) b := le_min (by positivity) hb.le
  have he1 : Real.exp (-(a / 2) * (3 : ℝ) ^ n) ≤
      Real.exp (-min (a / 2) b * ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22)) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul hm1 hY hY0 (by positivity)
    linarith
  have he2 : Real.exp (-b * ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22)) ≤
      Real.exp (-min (a / 2) b * ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22)) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hm2 hY0
    linarith
  calc latticeBondLaw 2 p {ω | T ∉ planarRHGood A₀ ω}
      ≤ latticeBondLaw 2 p (S₁ ∪ S₂ ∪ S₃) := measure_mono hsub
    _ ≤ latticeBondLaw 2 p S₁ + latticeBondLaw 2 p S₂ + latticeBondLaw 2 p S₃ :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ 0 + ENNReal.ofReal (2 * (9 * K2) * Real.exp (-(a / 2) * (3 : ℝ) ^ n)) +
          ENNReal.ofReal (Cb * Real.exp (-b * ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22))) := by
        rw [h1]
        exact add_le_add (add_le_add le_rfl h2) (hreach n c)
    _ = ENNReal.ofReal (2 * (9 * K2) * Real.exp (-(a / 2) * (3 : ℝ) ^ n) +
          Cb * Real.exp (-b * ((3 : ℝ) ^ n) ^ ((1 : ℝ) / 22))) := by
        rw [zero_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have := mul_le_mul_of_nonneg_left he1 (by positivity : (0 : ℝ) ≤ 2 * (9 * K2))
        have := mul_le_mul_of_nonneg_left he2 hCb
        nlinarith

/-- **The partition `𝓡` of Definition 3.7 of Armstrong and Dario with its minimal scales**, in
dimension two, from `p > p_c(2)` alone. -/
theorem planarRHPartition_holds {p : unitInterval} (hpc : criticalProbability 2 < (p : ℝ)) :
    PlanarRHPartition p := by
  obtain ⟨A₀, hq⟩ := planarRHFailureBound_holds hpc
  exact planarRHPartition_of_failureBound hq

end Rigidity.Proofs.Cluster
