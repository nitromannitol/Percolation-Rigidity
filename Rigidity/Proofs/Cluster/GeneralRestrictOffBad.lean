import Rigidity.Proofs.Cluster.GeneralRestrictErrorGood
import Rigidity.Proofs.Cluster.GeneralRHPartition
import Rigidity.Proofs.Cluster.GeneralRHMeyers

/-!
# Lemma 5.5 off the bad event above the partition `𝓡` of Definition 3.7, in every dimension

For a triadic cube `U` and a scale `2d ≤ n < scale U`, let `j = ⌊n/(2d)⌋`. The bad event
`cubeRestrictBad` of the proof of Lemma 5.5 of Armstrong and Dario is the union of

* some vertex of `U` has a partition cube of scale at least `j` (the event `Γ`);
* for some cell `□'` of scale `j - 1` of the inner cube of a subcube of scale `n`
  (`midCubeCells`), either `∑_{□'} size(□_𝒫)^τ > A_τ |□'|`, or the partition `s` of the
  reverse Hölder cubes (Definition 3.7) has a cell of scale larger than `j - 1` on `3□'`, or
  `∑_{□'} (3^s)^t > K |□'|`.

Off the bad event, the weight `size(□_𝒫)` is at most `3^j` on `U`, its cell averages are bounded,
and the Meyers estimate of Proposition 3.8 above `𝓡` (`meyers_rh_uniform`) holds on the cells for
the harmonic differences `w_V = u_U|_V - u_V`; by `cubeRestrictError_le_of_good`, the quantity of
display (5.12) is at most a constant `Λ₀` (independent of `U`, `n` and the slope) times the
normalized energy of the differences of Lemma 5.4
(`cubeRestrictError_le_of_not_mem_cubeRestrictBad`,
`cubeMuRestrictError_le_of_not_mem_cubeRestrictBad`,
`cubeNuRestrictError_le_of_not_mem_cubeRestrictBad`). This is the two-dimensional
`Rigidity.Proofs.Cluster.planarMuRestrictError_le_of_not_mem_restrictBad_rh`, with the weight the
size of the partition cubes instead of the planar reach, which is what makes the scale
`j = ⌊n/(2d)⌋` (rather than `⌊n/2⌋`) necessary: `3^j size^{2d-1} ≤ 3^{2dj} ≤ 3^n`.
-/

open LatticeProb.Percolation Rigidity.External Rigidity.Proofs.Cluster
  Rigidity.Proofs.Cluster.GeneralDim
open scoped BigOperators Classical

namespace Rigidity.Percolation

variable {d : ℕ}

/-- **The bad event of the proof of Lemma 5.5** for the cube `U` and the scale `n`, with
`j = ⌊n/(2d)⌋`. -/
def cubeRestrictBad (s : Configuration d → Vertex d → ℕ) (t K : ℝ) (τ : ℕ) (Aτ : ℝ)
    (U : TriadicCube d) (n : ℕ) : Set (Configuration d) :=
  {ω | PartitionEvent ω ∧ ∃ x ∈ U.toIntegerCube.vertices,
      n / (2 * d) ≤ (partitionCube ω x).scale} ∪
    ⋃ V ∈ U.subcubesAt n, ⋃ c ∈ midCubeCells V (n / (2 * d)),
      ({ω | Aτ * (cube c.1 c.2).card <
          ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ τ} ∪
        {ω | (∃ z ∈ enl 1 c.1 c.2, c.1 < s ω z) ∨
          K * (cube c.1 c.2).card < ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t})

/-- The constant `Λ₀` of Lemma 5.5 off the bad event. -/
noncomputable def restrictOffBadConst (d : ℕ) (A CM p : ℝ) : ℝ :=
  2 * d * (4 * d * (coarseGradConstant d ^ 2 * (A * (CM ^ (1 / p) * ((3 ^ d : ℕ) : ℝ)))) +
    16 * d ^ 2 * coarseGradConstant d ^ 2)

theorem two_mul_restrictQuadConst_div_le {n j : ℕ} (hd : 0 < d) (h : 2 * d * j ≤ n) {A CM p : ℝ}
    (hA : 0 ≤ A) (hCM : 0 ≤ CM) :
    2 * d * (restrictQuadConst d n j 1 A CM p (3 ^ j) / ((3 : ℝ) ^ n) ^ d) ≤
      restrictOffBadConst d A CM p := by
  set X : ℝ := (3 : ℝ) ^ n with hX
  set Y : ℝ := (3 : ℝ) ^ j with hY
  set K2 := coarseGradConstant d ^ 2 with hK2
  set T1 := K2 * (A * (CM ^ (1 / p) * ((3 ^ d : ℕ) : ℝ))) with hT1
  have hXpos : 0 < X := by positivity
  have hK20 : 0 ≤ K2 := sq_nonneg _
  have hT10 : 0 ≤ T1 := by positivity
  have hXd : X ^ d = X ^ (d - 1) * X := by rw [← pow_succ, Nat.sub_add_cancel hd]
  have hYY : Y * Y ^ (2 * d - 1) ≤ X := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ 2 * d), hY, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by rw [mul_comm]; exact h)
  have hR : restrictQuadConst d n j 1 A CM p Y ≤
      (4 * d * T1 + 16 * d ^ 2 * K2) * X ^ d := by
    rw [restrictQuadConst]
    rw [← hX, ← hK2, ← hT1]
    have h2 : 16 * (d : ℝ) ^ 2 * 1 ^ 2 * X ^ (d - 1) * Y * (K2 * Y ^ (2 * d - 1)) ≤
        16 * (d : ℝ) ^ 2 * K2 * X ^ d := by
      rw [hXd]
      have h3 : 0 ≤ 16 * (d : ℝ) ^ 2 * K2 * X ^ (d - 1) := by positivity
      have e : 16 * (d : ℝ) ^ 2 * 1 ^ 2 * X ^ (d - 1) * Y * (K2 * Y ^ (2 * d - 1)) =
          16 * (d : ℝ) ^ 2 * K2 * X ^ (d - 1) * (Y * Y ^ (2 * d - 1)) := by ring
      rw [e]
      have := mul_le_mul_of_nonneg_left hYY h3
      linarith
    nlinarith
  have hXd0 : 0 < X ^ d := by positivity
  rw [restrictOffBadConst, ← hK2, ← hT1]
  have hd0 : (0 : ℝ) ≤ 2 * d := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hd0
  rw [div_le_iff₀ hXd0]
  exact hR

/-- **Off the bad event, the quantity of Lemma 5.5 is controlled by the energy of the
differences** (every dimension `d ≥ 1`), above the partition `𝓡` of Definition 3.7, for harmonic
functions `u_U` and `u_V`. -/
theorem cubeRestrictError_le_of_not_mem_cubeRestrictBad (hd : 0 < d) {A₀ : ℝ}
    {s : Configuration d → Vertex d → ℕ} {ε t K CM r : ℝ} {τ : ℕ} {Aτ : ℝ}
    (hpq : (1 + ε / 2).HolderConjugate r) (hτr : ((2 * d - 1 : ℕ) : ℝ) * r ≤ τ) (hCM : 0 ≤ CM)
    (hAτ : 0 ≤ Aτ)
    (hMey : ∀ (ω : Configuration d) (U₀ : Finset (Vertex d)) (u : Vertex d → ℝ) (n : ℕ)
        (x₀ : Vertex d) (s : Vertex d → ℕ),
        (∀ a ∈ U₀, ∀ b, (openGraph ω).Adj a b → b ∈ enl 1 n x₀ → b ∈ U₀) →
        (∀ a ∈ U₀, a ∈ enl 1 n x₀ → (∀ b, (openGraph ω).Adj a b → b ∈ U₀) →
          openLaplacian ω u a = 0) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, Rigidity.Proofs.Cluster.supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (⟨k, idx k y⟩ : TriadicCube d) ∈ rhGood A₀ ω) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x => clusterEnergy ω U₀ u x ^ (1 + ε / 2)) ≤
          CM * avg (enl 1 n x₀) (clusterEnergy ω U₀ u) ^ (1 + ε / 2))
    {ω : Configuration d} (hP : PartitionEvent ω)
    (hs : (∀ x, ∀ z ∈ cube (s ω x) x, s ω z = s ω x) ∧
      (∀ x y, Rigidity.Proofs.Cluster.supDist x y ≤ 1 → s ω y ≤ s ω x + 1) ∧
      ∀ (k : ℕ) (y : Vertex d), s ω y ≤ k → (⟨k, idx k y⟩ : TriadicCube d) ∈ rhGood A₀ ω)
    {U : TriadicCube d} {n : ℕ} (hn : 2 * d ≤ n) (hnm : n < U.scale)
    (hgood : ω ∉ cubeRestrictBad s t K τ Aτ U n) (uU : CubeFun ω U)
    (huU : uU ∈ cubeHarmonic ω U) (uV : ∀ V : TriadicCube d, CubeFun ω V)
    (huV : ∀ V ∈ U.subcubesAt n, uV V ∈ cubeHarmonic ω V) :
    cubeRestrictError ω U n uU uV ≤
      restrictOffBadConst d (Aτ ^ (1 / r)) CM (1 + ε / 2) *
        ((∑ V ∈ U.subcubesAt n, cubeForm ω V (cubeRestrictExt V uU - uV V)
          (cubeRestrictExt V uU - uV V) / 2) / U.latticeVolume) := by
  obtain ⟨hcell, hnb, hRH⟩ := hs
  set j := n / (2 * d) with hj
  have hj1 : 1 ≤ j := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hjn : j < n := Nat.div_lt_self (by omega) (by omega)
  have h2dj : 2 * d * j ≤ n := Nat.mul_div_le n (2 * d)
  -- the parts of the good event
  have hres : ∀ x ∈ U.vertices, (partitionCube ω x).scale < j := fun x hx => by
    by_contra h
    exact hgood (Set.mem_union_left _
      ⟨hP, x, (U.mem_toIntegerCube_vertices x).2 hx, not_lt.1 h⟩)
  have hcells : ∀ V ∈ U.subcubesAt n, ∀ c ∈ midCubeCells V j,
      ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ τ ≤ Aτ * (cube c.1 c.2).card ∧
      (∀ z ∈ enl 1 c.1 c.2, s ω z ≤ c.1) ∧
      ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t ≤ K * (cube c.1 c.2).card := by
    intro V hV c hc
    have hnot : ω ∉ ({ω | Aτ * (cube c.1 c.2).card <
          ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ (partitionCube ω x).scale) ^ τ} ∪
        {ω | (∃ z ∈ enl 1 c.1 c.2, c.1 < s ω z) ∨
          K * (cube c.1 c.2).card < ∑ x ∈ cube c.1 c.2, ((3 : ℝ) ^ s ω x) ^ t}) := fun h =>
      hgood (Set.mem_union_right _ (Set.mem_iUnion₂.2 ⟨V, hV, Set.mem_iUnion₂.2 ⟨c, hc, h⟩⟩))
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt, not_exists, not_and] at hnot
    exact ⟨hnot.1, fun z hz => hnot.2.1 z hz, hnot.2.2⟩
  -- the weights
  set Wt : Vertex d → ℝ := fun z => (3 : ℝ) ^ (partitionCube ω z).scale with hWtdef
  have hWt : ∀ z, (3 : ℝ) ^ (partitionCube ω z).scale ≤ Wt z := fun z => le_rfl
  have hW : ∀ z ∈ U.vertices, (3 : ℝ) ^ (partitionCube ω z).scale ≤ 3 ^ j := fun z hz =>
    pow_le_pow_right₀ (by norm_num) (hres z hz).le
  have hr0 : 0 < r := hpq.symm.pos
  have hA : ∀ V ∈ U.subcubesAt n, ∀ c ∈ midCubeCells V j,
      avg (cube c.1 c.2) (fun x => (Wt x ^ (2 * d - 1)) ^ r) ^ (1 / r) ≤ Aτ ^ (1 / r) := by
    intro V hV c hc
    have hsum := (hcells V hV c hc).1
    have hpt : ∀ x, (Wt x ^ (2 * d - 1)) ^ r ≤ ((3 : ℝ) ^ (partitionCube ω x).scale) ^ τ := by
      intro x
      have h1 : (1 : ℝ) ≤ Wt x := one_le_pow₀ (by norm_num)
      rw [← Real.rpow_natCast (Wt x) (2 * d - 1), ← Real.rpow_mul (by positivity),
        ← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le h1 hτr
    have hcpos := card_cube_pos c.1 c.2
    have havg : avg (cube c.1 c.2) (fun x => (Wt x ^ (2 * d - 1)) ^ r) ≤ Aτ := by
      rw [avg, div_le_iff₀ hcpos]
      exact (Finset.sum_le_sum fun x _ => hpt x).trans hsum
    have havg0 : 0 ≤ avg (cube c.1 c.2) (fun x => (Wt x ^ (2 * d - 1)) ^ r) :=
      div_nonneg (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (by positivity) _)
        (Nat.cast_nonneg _)
    exact Real.rpow_le_rpow havg0 havg (by positivity)
  have hM : ∀ V ∈ U.subcubesAt n, ∀ c ∈ midCubeCells V j, avg (cube c.1 c.2) (fun x =>
        clusterEnergy ω (crossingClusterVertices ω V)
          (cubeExtend ω V (cubeRestrictExt V uU - uV V)) x ^ (1 + ε / 2)) ≤
      CM * avg (enl 1 c.1 c.2) (clusterEnergy ω (crossingClusterVertices ω V)
          (cubeExtend ω V (cubeRestrictExt V uU - uV V))) ^ (1 + ε / 2) := by
    intro V hV c hc
    have hVs : V.scale = n := TriadicCube.scale_of_mem_subcubesAt hV
    have hVU : V.vertices ⊆ U.vertices := TriadicCube.subset_of_mem_subcubesAt hnm.le hV
    have hVr : PartitionResolved ω V := fun z hz =>
      (hres z (hVU hz)).le.trans (by omega)
    have hjV : j < V.scale := by omega
    have hw := sub_mem_cubeHarmonic_of_mem_subcubesAt hd hP hnm.le hV hVr huU (huV V hV)
    obtain ⟨-, hsk, hmom⟩ := hcells V hV c hc
    refine hMey ω (crossingClusterVertices ω V) (cubeExtend ω V (cubeRestrictExt V uU - uV V))
      c.1 c.2 (s ω) ?_ ?_ hcell hnb ?_ (fun k y hy _ => hRH k y hy) hmom
    · intro a ha b hadj hb
      have hbV : b ∈ V.vertices := (V.mem_toIntegerCube_vertices b).1
        (midCubeCells_enl_subset hj1 hjV hc hb)
      exact mem_crossingClusterVertices.2
        (mem_crossingCluster_of_adj (mem_crossingClusterVertices.1 ha) hbV hadj)
    · intro a ha haE hall
      exact openLaplacian_cubeExtend_eq_zero hw ha
        (midCubeCells_isLatticeInterior hj1 hjV hc haE) hall
    · intro z hz
      exact (cube_mono (hsk z hz) z).trans (cube_subset_enl_of_mem hz)
  have h := cubeRestrictError_le_of_good hd hP hj1 hjn hnm.le hres uU uV hpq hCM
    (Real.rpow_nonneg hAτ _) Wt hWt hW hA hM
  have hD0 : 0 ≤ (∑ V ∈ U.subcubesAt n, cubeForm ω V (cubeRestrictExt V uU - uV V)
      (cubeRestrictExt V uU - uV V) / 2) / U.latticeVolume :=
    div_nonneg (Finset.sum_nonneg fun V _ => div_nonneg (cubeForm_self_nonneg _) (by norm_num))
      U.latticeVolume_pos.le
  exact h.trans (mul_le_mul_of_nonneg_right
    (two_mul_restrictQuadConst_div_le hd h2dj (Real.rpow_nonneg hAτ _) hCM) hD0)

/-- Off the bad event, the partition cubes of the vertices of `U` have scale less than
`⌊n/(2d)⌋`. -/
theorem scale_lt_of_not_mem_cubeRestrictBad {s : Configuration d → Vertex d → ℕ} {t K : ℝ}
    {τ : ℕ} {Aτ : ℝ} {ω : Configuration d} (hP : PartitionEvent ω) {U : TriadicCube d} {n : ℕ}
    (hgood : ω ∉ cubeRestrictBad s t K τ Aτ U n) :
    ∀ x ∈ U.vertices, (partitionCube ω x).scale < n / (2 * d) := fun x hx => by
  by_contra h
  exact hgood (Set.mem_union_left _
    ⟨hP, x, (U.mem_toIntegerCube_vertices x).2 hx, not_lt.1 h⟩)

/-- **Off the bad event, the quantity of Lemma 5.5 for `μ` is controlled by Lemma 5.4**
(every dimension `d ≥ 1`), above the partition `𝓡` of Definition 3.7. -/
theorem cubeMuRestrictError_le_of_not_mem_cubeRestrictBad (hd : 0 < d) {A₀ : ℝ}
    {s : Configuration d → Vertex d → ℕ} {ε t K CM r : ℝ} {τ : ℕ} {Aτ : ℝ}
    (hpq : (1 + ε / 2).HolderConjugate r) (hτr : ((2 * d - 1 : ℕ) : ℝ) * r ≤ τ) (hCM : 0 ≤ CM)
    (hAτ : 0 ≤ Aτ)
    (hMey : ∀ (ω : Configuration d) (U₀ : Finset (Vertex d)) (u : Vertex d → ℝ) (n : ℕ)
        (x₀ : Vertex d) (s : Vertex d → ℕ),
        (∀ a ∈ U₀, ∀ b, (openGraph ω).Adj a b → b ∈ enl 1 n x₀ → b ∈ U₀) →
        (∀ a ∈ U₀, a ∈ enl 1 n x₀ → (∀ b, (openGraph ω).Adj a b → b ∈ U₀) →
          openLaplacian ω u a = 0) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, Rigidity.Proofs.Cluster.supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (⟨k, idx k y⟩ : TriadicCube d) ∈ rhGood A₀ ω) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x => clusterEnergy ω U₀ u x ^ (1 + ε / 2)) ≤
          CM * avg (enl 1 n x₀) (clusterEnergy ω U₀ u) ^ (1 + ε / 2))
    {ω : Configuration d} (hP : PartitionEvent ω)
    (hs : (∀ x, ∀ z ∈ cube (s ω x) x, s ω z = s ω x) ∧
      (∀ x y, Rigidity.Proofs.Cluster.supDist x y ≤ 1 → s ω y ≤ s ω x + 1) ∧
      ∀ (k : ℕ) (y : Vertex d), s ω y ≤ k → (⟨k, idx k y⟩ : TriadicCube d) ∈ rhGood A₀ ω)
    {U : TriadicCube d} {n : ℕ} (hn : 2 * d ≤ n) (hnm : n < U.scale)
    (hgood : ω ∉ cubeRestrictBad s t K τ Aτ U n) (q : Fin d → ℝ) :
    cubeMuRestrictError ω U n q ≤
      restrictOffBadConst d (Aτ ^ (1 / r)) CM (1 + ε / 2) *
        (cubeMuDefect ω U n q / U.latticeVolume) := by
  have hres := scale_lt_of_not_mem_cubeRestrictBad hP hgood
  have hjn : n / (2 * d) < n := Nat.div_lt_self (by omega) (by omega)
  have hU : PartitionResolved ω U := fun z hz => (hres z hz).le.trans (by omega)
  have hVr : ∀ V ∈ U.subcubesAt n, PartitionResolved ω V := fun V hV z hz => by
    rw [TriadicCube.scale_of_mem_subcubesAt hV]
    exact (hres z (TriadicCube.subset_of_mem_subcubesAt hnm.le hV hz)).le.trans hjn.le
  have h := cubeRestrictError_le_of_not_mem_cubeRestrictBad hd hpq hτr hCM hAτ hMey hP hs hn hnm
    hgood (cubeMuMinimizer ω U q) (cubeMuMinimizer_spec hd hP hU q).1
    (fun V => cubeMuMinimizer ω V q) (fun V hV => (cubeMuMinimizer_spec hd hP (hVr V hV) q).1)
  rw [cubeMuRestrictError, cubeMuDefect, if_pos ⟨hP, hU⟩,
    resolvedSubcubesAt_eq_of_lt hjn hnm.le hres]
  exact h

/-- **Off the bad event, the quantity of Lemma 5.5 for `ν` is controlled by Lemma 5.4**
(every dimension `d ≥ 1`), above the partition `𝓡` of Definition 3.7. -/
theorem cubeNuRestrictError_le_of_not_mem_cubeRestrictBad (hd : 0 < d) {A₀ : ℝ}
    {s : Configuration d → Vertex d → ℕ} {ε t K CM r : ℝ} {τ : ℕ} {Aτ : ℝ}
    (hpq : (1 + ε / 2).HolderConjugate r) (hτr : ((2 * d - 1 : ℕ) : ℝ) * r ≤ τ) (hCM : 0 ≤ CM)
    (hAτ : 0 ≤ Aτ)
    (hMey : ∀ (ω : Configuration d) (U₀ : Finset (Vertex d)) (u : Vertex d → ℝ) (n : ℕ)
        (x₀ : Vertex d) (s : Vertex d → ℕ),
        (∀ a ∈ U₀, ∀ b, (openGraph ω).Adj a b → b ∈ enl 1 n x₀ → b ∈ U₀) →
        (∀ a ∈ U₀, a ∈ enl 1 n x₀ → (∀ b, (openGraph ω).Adj a b → b ∈ U₀) →
          openLaplacian ω u a = 0) →
        (∀ x, ∀ z ∈ cube (s x) x, s z = s x) →
        (∀ x y, Rigidity.Proofs.Cluster.supDist x y ≤ 1 → s y ≤ s x + 1) →
        (∀ z ∈ enl 1 n x₀, cube (s z) z ⊆ enl 1 n x₀) →
        (∀ k y, s y ≤ k → enl 1 k y ⊆ enl 1 n x₀ →
          (⟨k, idx k y⟩ : TriadicCube d) ∈ rhGood A₀ ω) →
        ∑ x ∈ cube n x₀, ((3 : ℝ) ^ s x) ^ t ≤ K * (cube n x₀).card →
        avg (cube n x₀) (fun x => clusterEnergy ω U₀ u x ^ (1 + ε / 2)) ≤
          CM * avg (enl 1 n x₀) (clusterEnergy ω U₀ u) ^ (1 + ε / 2))
    {ω : Configuration d} (hP : PartitionEvent ω)
    (hs : (∀ x, ∀ z ∈ cube (s ω x) x, s ω z = s ω x) ∧
      (∀ x y, Rigidity.Proofs.Cluster.supDist x y ≤ 1 → s ω y ≤ s ω x + 1) ∧
      ∀ (k : ℕ) (y : Vertex d), s ω y ≤ k → (⟨k, idx k y⟩ : TriadicCube d) ∈ rhGood A₀ ω)
    {U : TriadicCube d} {n : ℕ} (hn : 2 * d ≤ n) (hnm : n < U.scale)
    (hgood : ω ∉ cubeRestrictBad s t K τ Aτ U n) (ξ : Fin d → ℝ) :
    cubeNuRestrictError ω U n ξ ≤
      restrictOffBadConst d (Aτ ^ (1 / r)) CM (1 + ε / 2) *
        (cubeNuDefect ω U n ξ / U.latticeVolume) := by
  have hres := scale_lt_of_not_mem_cubeRestrictBad hP hgood
  have hjn : n / (2 * d) < n := Nat.div_lt_self (by omega) (by omega)
  have hU : PartitionResolved ω U := fun z hz => (hres z hz).le.trans (by omega)
  have hVr : ∀ V ∈ U.subcubesAt n, PartitionResolved ω V := fun V hV z hz => by
    rw [TriadicCube.scale_of_mem_subcubesAt hV]
    exact (hres z (TriadicCube.subset_of_mem_subcubesAt hnm.le hV hz)).le.trans hjn.le
  have h := cubeRestrictError_le_of_not_mem_cubeRestrictBad hd hpq hτr hCM hAτ hMey hP hs hn hnm
    hgood (cubeNuMaximizer ω U ξ) (cubeNuMaximizer_spec U ξ).1
    (fun V => cubeNuMaximizer ω V ξ) (fun V _ => (cubeNuMaximizer_spec V ξ).1)
  rw [cubeNuRestrictError_eq hP hU hVr, cubeNuDefect, resolvedSubcubesAt_eq_of_lt hjn hnm.le hres]
  exact h

end Rigidity.Percolation
