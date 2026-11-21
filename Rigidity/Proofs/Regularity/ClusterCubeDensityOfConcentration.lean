import Rigidity.Proofs.S2.ClusterDensityFromDarioGu
import Rigidity.Proofs.Regularity.ClusterBallGeometry

/-!
# The density of the infinite cluster in cubes above a minimal scale

From the concentration of the density of the infinite cluster in triadic cubes (Dario–Gu,
Proposition A.1, `Rigidity.External.ClusterDensityConcentrationAt`), for every centre `z` there is a
minimal scale `M(z) ≤ O_s(C)` such that almost surely every triadic cube of size `3^m ≥ M(z)` inside
the ball `B_{Λ 3^m}(z)` carries at least `θ(p)/2 · 3^{d m}` vertices of the infinite cluster
(`exists_clusterCubeDensity_of_concentration`): the hypothesis `ClusterCubeDensity` of
`Rigidity.Proofs.Regularity.ClusterBallGeometry`, which gives the volume comparison and the cap
density of the balls of the infinite cluster used in the iteration of Armstrong–Dario, Lemma 7.2.

The proof is the union bound of `Rigidity.Proofs.S2.clusterDensityInputFaithfulAt_of_concentration`
over the `(2 W + 1)^d` triadic cubes of size `3^m` whose indices are within `W = ⌈Λ⌉₊ + 1` of
`⌊z / 3^m⌋`, followed by `Rigidity.Proofs.S2.exists_minimalScale_of_summable`.
-/

namespace Rigidity.Proofs.Regularity

open MeasureTheory LatticeProb LatticeProb.Percolation Rigidity.External Rigidity.Proofs.S2

variable {d : ℕ}

/-- The `(2 W + 1)^d` triadic cubes `□_m(3^m k)` with `|kᵢ - ⌊zᵢ / 3^m⌋| ≤ W`. -/
noncomputable def localCubes (W : ℕ) (z : Vertex d) (m : ℕ) : Finset (Vertex d) :=
  Fintype.piFinset fun i => Finset.Icc (z i / 3 ^ m - W) (z i / 3 ^ m + W)

theorem card_localCubes (W : ℕ) (z : Vertex d) (m : ℕ) :
    (localCubes W z m).card = (2 * W + 1) ^ d := by
  rw [localCubes, Fintype.card_piFinset]
  have hc : ∀ i, (Finset.Icc (z i / 3 ^ m - W) (z i / 3 ^ m + W)).card = 2 * W + 1 := by
    intro i
    rw [Int.card_Icc]
    have e : z i / 3 ^ m + W + 1 - (z i / 3 ^ m - W) = ((2 * W + 1 : ℕ) : ℤ) := by
      push_cast; ring
    rw [e, Int.toNat_natCast]
  simp only [hc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- A triadic cube of size `3^m` inside `B_{Λ 3^m}(z)` is one of the `localCubes (⌈Λ⌉₊ + 1) z m`. -/
theorem mem_localCubes_of_dist_lt {Λ : ℝ} {z : Vertex d} {m : ℕ} {k : Vertex d}
    (hk : ∀ y ∈ triadicCube d m k,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z) < Λ * 3 ^ m) :
    k ∈ localCubes (⌈Λ⌉₊ + 1) z m := by
  have h3 : (0 : ℤ) < 3 ^ m := by positivity
  have h3' : (0 : ℝ) < 3 ^ m := by positivity
  have hΛ : Λ ≤ (⌈Λ⌉₊ : ℝ) := Nat.le_ceil Λ
  set y : Vertex d := fun j => 3 ^ m * k j with hy
  have hyQ : y ∈ triadicCube d m k := by
    intro i
    simp only [hy]
    push_cast
    rw [sub_self, abs_zero]
    positivity
  have hdist := hk y hyQ
  rw [localCubes, Fintype.mem_piFinset]
  intro i
  have hi := (abs_sub_le_dist_latticeEuclideanEmbedding y z i).trans_lt hdist
  simp only [hy] at hi
  push_cast at hi
  have hdiv := Int.mul_ediv_add_emod (z i) (3 ^ m)
  have hr0 := Int.emod_nonneg (z i) h3.ne'
  have hr1 := Int.emod_lt_of_pos (z i) h3
  set q := z i / 3 ^ m
  set r := z i % 3 ^ m
  have hzR : (z i : ℝ) = 3 ^ m * q + r := by exact_mod_cast hdiv.symm
  have hr0R : (0 : ℝ) ≤ r := by exact_mod_cast hr0
  have hr1R : (r : ℝ) < 3 ^ m := by exact_mod_cast hr1
  rw [hzR] at hi
  have hb := abs_lt.1 hi
  have hup : ((k i - q : ℤ) : ℝ) < (⌈Λ⌉₊ : ℝ) + 1 := by
    push_cast
    have : 3 ^ m * ((k i : ℝ) - q) < 3 ^ m * ((⌈Λ⌉₊ : ℝ) + 1) := by nlinarith
    exact lt_of_mul_lt_mul_left this h3'.le
  have hlow : -((⌈Λ⌉₊ : ℝ) + 1) < ((k i - q : ℤ) : ℝ) := by
    push_cast
    have : 3 ^ m * (-((⌈Λ⌉₊ : ℝ) + 1)) < 3 ^ m * ((k i : ℝ) - q) := by nlinarith
    exact lt_of_mul_lt_mul_left this h3'.le
  have hup' : k i - q < (⌈Λ⌉₊ : ℤ) + 1 := by exact_mod_cast hup
  have hlow' : -((⌈Λ⌉₊ : ℤ) + 1) < k i - q := by exact_mod_cast hlow
  rw [Finset.mem_Icc]
  push_cast
  constructor <;> omega

/-- The vertices of the infinite cluster in a triadic cube inside `B_ρ(z)` are counted by
`clusterCubePoints`. -/
theorem infiniteClusterCount_le_card_clusterCubePoints {ω : Configuration d}
    (h : HasUniqueInfiniteOpenComponent ω) (z : Vertex d) {ρ : ℝ} {m : ℕ} {k : Vertex d}
    (hk : ∀ y ∈ triadicCube d m k,
      dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding z) < ρ) :
    infiniteClusterCount (triadicCube d m k) ω ≤
      (clusterCubePoints (uniqueInfiniteComponent h) z ρ m k).card := by
  classical
  set S := clusterCubePoints (uniqueInfiniteComponent h) z ρ m k
  rw [infiniteClusterCount]
  have hsub : {y ∈ triadicCube d m k | ω ∈ infiniteComponentEvent y} ⊆
      ((S.image Subtype.val : Finset (Vertex d)) : Set (Vertex d)) := by
    rintro y ⟨hyQ, hyE⟩
    have hsupp := (mem_uniqueInfiniteComponent_iff h y).2 hyE
    rw [Finset.coe_image]
    refine ⟨⟨y, hsupp⟩, ?_, rfl⟩
    simp only [S, clusterCubePoints, Finset.coe_filter, Set.mem_setOf_eq,
      mem_componentEuclideanBall]
    exact ⟨hk y hyQ, hyQ⟩
  calc {y ∈ triadicCube d m k | ω ∈ infiniteComponentEvent y}.ncard
      ≤ ((S.image Subtype.val : Finset (Vertex d)) : Set (Vertex d)).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (S.image Subtype.val).card := Set.ncard_coe_finset _
    _ ≤ S.card := Finset.card_image_le

/-- **Density of the infinite cluster in cubes above a minimal scale**, from Dario–Gu,
Proposition A.1: for every `Λ`, almost surely every triadic cube of size `3^m ≥ M(z)` inside
`B_{Λ 3^m}(z)` carries at least `θ(p)/2 · 3^{d m}` vertices of the infinite cluster. -/
theorem exists_clusterCubeDensity_of_concentration [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hDG : ClusterDensityConcentrationAt d p) (Λ : ℝ) :
    ∃ s C : ℝ, 0 < s ∧ 0 < C ∧ ∀ z : Vertex d,
      ∃ M : Configuration d → ℝ, Measurable M ∧ (∀ ω, 0 ≤ M ω) ∧ IsOsBond d p M s C ∧
      ∀ᵐ ω ∂latticeBondLaw d p, ∀ h : HasUniqueInfiniteOpenComponent ω,
        ClusterCubeDensity (uniqueInfiniteComponent h) z Λ (M ω) (theta d p / 2) := by
  obtain ⟨C, hC, hX⟩ := hDG
  rcases (theta_nonneg d p).eq_or_lt with hθ0 | hθ
  · refine ⟨1, 1 * 3 ^ ((1 : ℝ) / 1), one_pos, by positivity, fun z =>
      ⟨fun _ => 1, measurable_const, fun _ => zero_le_one, isOsBond_const one_pos one_pos,
        Filter.Eventually.of_forall fun ω h m k _ _ => ?_⟩⟩
    rw [← hθ0, zero_div, zero_mul]
    exact Nat.cast_nonneg _
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨s₀, hs₀def⟩ : ∃ s₀ : ℝ,
      s₀ = 2 * ((d : ℝ) - 1) / (3 * (d : ℝ) ^ 2 + 2 * (d : ℝ) - 1) := ⟨_, rfl⟩
  have hX' : ∀ (m : ℕ) (k : Vertex d), IsOsBond d p
      (fun ω => |(infiniteClusterCount (triadicCube d m k) ω : ℝ) /
        ((triadicCube d m k).ncard : ℝ) - theta d p|) s₀
      (C * (3 : ℝ) ^ (-((d : ℝ) * (m : ℝ)) / 2)) := by
    intro m k; rw [hs₀def]; exact hX m k
  have hs₀ : 0 < s₀ := by
    rw [hs₀def]
    exact div_pos (by linarith only [hd2]) (by nlinarith only [hd2])
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = s₀ * d / 4 := ⟨_, rfl⟩
  have hs : 0 < s := by rw [hsdef]; positivity
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = s * Real.log 3 := ⟨_, rfl⟩
  have ht : 0 < t := by rw [htdef]; exact mul_pos hs (Real.log_pos (by norm_num))
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = (theta d p / (2 * C)) ^ s₀ := ⟨_, rfl⟩
  have hB : 0 < B := by rw [hBdef]; exact Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨b, hbdef⟩ : ∃ b : ℕ → ℝ, b = fun m : ℕ =>
      (((2 * (⌈Λ⌉₊ + 1) + 1) ^ d : ℕ) : ℝ) * (2 * Real.exp (-(B * Real.exp (t * m) ^ 2))) :=
    ⟨_, rfl⟩
  have hbm : ∀ m, b m =
      (((2 * (⌈Λ⌉₊ + 1) + 1) ^ d : ℕ) : ℝ) * (2 * Real.exp (-(B * Real.exp (t * m) ^ 2))) :=
    fun m => by rw [hbdef]
  have hb0 : ∀ m, 0 ≤ b m := fun m => by rw [hbm]; positivity
  have hE : ∀ (m : ℕ) (k : Vertex d), latticeBondLaw d p (badCubeEvent d m k (theta d p)) ≤
      ENNReal.ofReal (2 * Real.exp (-(B * Real.exp (t * m) ^ 2))) := by
    intro m k
    have h := measure_badCubeEvent_le hC hs₀ hθ m k (hX' m k)
    rwa [← hsdef, ← htdef, ← hBdef] at h
  have hBad : ∀ z m, latticeBondLaw d p
      (⋃ k ∈ localCubes (⌈Λ⌉₊ + 1) z m, badCubeEvent d m k (theta d p)) ≤
      ENNReal.ofReal (b m) := by
    intro z m
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun k _ => hE m k).trans ?_
    rw [Finset.sum_const, card_localCubes, nsmul_eq_mul, hbm,
      ENNReal.ofReal_mul (p := (((2 * (⌈Λ⌉₊ + 1) + 1) ^ d : ℕ) : ℝ)) (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast]
  have hsum : Summable fun m => b m * Real.exp ((1 * 3 ^ (m + 1)) ^ s) := by
    have h := (summable_exp_mul_sub_sq ((3 * 1) ^ s) B t hB ht).mul_left
      (2 * (((2 * (⌈Λ⌉₊ + 1) + 1) ^ d : ℕ) : ℝ))
    refine h.congr fun m => ?_
    rw [hbm, scale_exponent_eq zero_le_one m, ← htdef, sub_eq_add_neg, Real.exp_add]
    ring
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ,
      A = Real.exp (1 ^ s) + ∑' m, b m * Real.exp ((1 * 3 ^ (m + 1)) ^ s) := ⟨_, rfl⟩
  have hA1 : 1 ≤ A := by
    rw [hAdef]
    exact le_add_of_le_of_nonneg (Real.one_le_exp (Real.rpow_nonneg zero_le_one _))
      (tsum_nonneg fun m => mul_nonneg (hb0 m) (Real.exp_pos _).le)
  refine ⟨s, 1 * A ^ (1 / s), hs, mul_pos one_pos (Real.rpow_pos_of_pos (by linarith) _),
    fun z => ?_⟩
  obtain ⟨M, hMm, hM0, hint, hle, hae⟩ := exists_minimalScale_of_summable (latticeBondLaw d p)
    (fun m => ⋃ k ∈ localCubes (⌈Λ⌉₊ + 1) z m, badCubeEvent d m k (theta d p))
    (fun m => Finset.measurableSet_biUnion _ fun k _ => measurableSet_badCubeEvent m k _)
    one_pos b hb0 (hBad z) hsum
  have e : (fun ω => Real.exp (Real.rpow (max (M ω / 1) 0) s)) = fun ω => Real.exp (M ω ^ s) := by
    funext ω
    rw [div_one, max_eq_left (hM0 ω)]
    rfl
  refine ⟨M, hMm, hM0, isOsBond_of_integral_le (θ := 1) hs hA1 (by rw [e]; exact hint)
    (by rw [e, hAdef]; exact hle), ?_⟩
  filter_upwards [hae] with ω ⟨N, hMN, hgood⟩
  intro h m k hm hk
  rw [hMN, one_mul] at hm
  have hNm : N ≤ m := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).1 hm
  have hkL := mem_localCubes_of_dist_lt hk
  have hgk : ω ∉ badCubeEvent d m k (theta d p) := fun hk' =>
    hgood m hNm (Set.mem_iUnion₂.2 ⟨k, hkL, hk'⟩)
  have hcnt := lt_infiniteClusterCount_of_notMem_badCubeEvent hgk
  have hle' := infiniteClusterCount_le_card_clusterCubePoints h z hk
  exact hcnt.le.trans (by exact_mod_cast hle')

end Rigidity.Proofs.Regularity
