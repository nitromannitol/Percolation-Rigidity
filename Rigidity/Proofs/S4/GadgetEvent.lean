import Rigidity.Steps.S4.NonConstantOnGadget
import LatticeProb.Prob.Percolation.CorrectedPlaneAlgebra
import LatticeProb.External.SupercriticalBondCorrectorInput
import LatticeProb.External.ArmstrongDarioOrderZero

/-!
# Lemma 4.8: the event `E_R`

Step `step:4.8-event` (`Rigidity.Steps.S4.EventStep`, paper L1396-1404 of the corrected draft):
the event `E_R` (`Q_R` is well-connected, and every nonconstant function of `𝒜₁(𝒞_∞)` takes more
than one value on `Q_R ∩ 𝒞_∞`) has probability at least `1/2` for every large `R`.

* Well-connectedness: by Proposition 2.3 (`Rigidity.External.WellConnectedInput`) the cube `Q_R`
  fails to be well-connected with probability at most `C exp(-c R^s) → 0`.
* The second property: almost surely the infinite cluster `𝒞_∞` is unique
  (`LatticeProb.External.ArmstrongDarioOrderZero`) and `𝒜₁(𝒞_∞)` is finite-dimensional: by the
  qualitative corrector input (`LatticeProb.External.SupercriticalBondCorrectorInput`, the
  order-one part of Theorem 2.4) every `u ∈ 𝒜₁(𝒞_∞)` is a corrected plane `ℓ_q` of some slope `q`,
  and `u - u(o) = ∑ⱼ qⱼ ℓ_{eⱼ}` by uniqueness of the corrected plane of slope `q` vanishing at `o`.
  The subspaces `K_R ⊆ 𝒜₁(𝒞_∞)` of functions constant on `Q_R ∩ 𝒞_∞` decrease in `R`; at a radius
  `R₀` of minimal dimension they are stationary, so a function of `K_{R₀}` is constant on every
  `Q_R ∩ 𝒞_∞`, hence constant. The second property thus holds from `R₀` on, and its probability
  tends to one (continuity from below, without measurability).
-/

namespace Rigidity.Proofs.S4

open Filter Topology MeasureTheory LatticeProb.Percolation Rigidity.Section4 Rigidity.Steps.S4

variable {d : ℕ}

/-- The cube `Q_R` increases with `R`. -/
theorem cube_mono {R R' : ℕ} (h : R ≤ R') : cube d R ⊆ cube d R' :=
  fun _ hx i => (hx i).trans (by exact_mod_cast h)

/-- Every site lies in some cube `Q_R`. -/
theorem exists_mem_cube (x : Vertex d) : ∃ R : ℕ, x ∈ cube d R := by
  refine ⟨∑ i, (x i).natAbs, fun i => ?_⟩
  rw [Int.abs_eq_natAbs]
  exact_mod_cast Finset.single_le_sum (f := fun j => (x j).natAbs) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)

/-- `𝒜₁(𝒞)` is finite-dimensional when every slope has a unique corrected plane vanishing at `o`
and every element of `𝒜₁(𝒞)` is a corrected plane: `u = ∑ⱼ qⱼ ℓ_{eⱼ} + u(o)`. -/
theorem finiteDimensional_harmonicGrowthSpace_one {ω : Configuration d} (C : OpenComponent ω)
    (o : C) (hplanes : ∀ q : Fin d → ℝ, ∃! u : C → ℝ, IsCorrectedPlane C q u ∧ u o = 0)
    (hslope : ∀ u ∈ harmonicGrowthSpace C 1, ∃ q : Fin d → ℝ, IsCorrectedPlane C q u) :
    FiniteDimensional ℝ (harmonicGrowthSpace C 1) := by
  choose P hP hU using hplanes
  let f : Option (Fin d) → (C → ℝ) := fun i => i.elim (fun _ => 1) fun j => P (Pi.single j 1)
  haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range f)) :=
    FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℝ (Set.range f)) fun u hu => ?_
  obtain ⟨q, hq⟩ := hslope u hu
  have hsum : ∀ s : Finset (Fin d), IsCorrectedPlane C (∑ j ∈ s, q j • Pi.single j (1 : ℝ))
      (∑ j ∈ s, q j • P (Pi.single j 1)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact isCorrectedPlane_const C 0
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj]
      exact isCorrectedPlane_add C (isCorrectedPlane_smul C (hP _).1 (q j)) ih
  have hqsum : ∑ j, q j • Pi.single j (1 : ℝ) = q := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hw := hsum Finset.univ
  rw [hqsum] at hw
  have hsub : IsCorrectedPlane C q (fun x => u x - u o) := by
    have h := isCorrectedPlane_add C hq (isCorrectedPlane_const C (-u o))
    rw [add_zero] at h
    convert h using 1
    funext x
    simp [sub_eq_add_neg]
  have hw0 : (∑ j, q j • P (Pi.single j 1)) o = 0 := by
    simp [Finset.sum_apply, (hP _).2]
  have heq : (fun x => u x - u o) = ∑ j, q j • P (Pi.single j 1) :=
    (hU q _ ⟨hsub, sub_self _⟩).trans (hU q _ ⟨hw, hw0⟩).symm
  have hu' : u = ∑ j, q j • f (some j) + u o • f none := by
    funext x
    have hx := congrFun heq x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx
    simp only [f, Option.elim, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      mul_one]
    linarith
  rw [hu']
  exact Submodule.add_mem _
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨some j, rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨none, rfl⟩))

/-- If `𝒜₁(𝒞)` is finite-dimensional, there is a radius `R₀` such that every nonconstant function
of `𝒜₁(𝒞)` takes two values on `Q_{R₀} ∩ 𝒞`: the subspaces `K_R` of functions constant on
`Q_R ∩ 𝒞` decrease, are stationary from a radius of minimal dimension, and meet in the constants. -/
theorem exists_radius_twoValued {ω : Configuration d} (C : OpenComponent ω)
    [FiniteDimensional ℝ (harmonicGrowthSpace C 1)] :
    ∃ R₀ : ℕ, ∀ u ∈ harmonicGrowthSpace C 1, (∃ x y, u x ≠ u y) →
      ∃ x y : C, x.1 ∈ cube d R₀ ∧ y.1 ∈ cube d R₀ ∧ u x ≠ u y := by
  classical
  let K : ℕ → Submodule ℝ (C → ℝ) := fun R => harmonicGrowthSpace C 1 ⊓
    { carrier := {u | ∀ x y : C, x.1 ∈ cube d R → y.1 ∈ cube d R → u x = u y}
      add_mem' := fun {a b} ha hb x y hx hy => by
        simp only [Pi.add_apply, ha x y hx hy, hb x y hx hy]
      zero_mem' := fun _ _ _ _ => rfl
      smul_mem' := fun c u hu x y hx hy => by
        simp only [Pi.smul_apply, smul_eq_mul, hu x y hx hy] }
  have hmemK : ∀ R u, u ∈ K R ↔ u ∈ harmonicGrowthSpace C 1 ∧
      ∀ x y : C, x.1 ∈ cube d R → y.1 ∈ cube d R → u x = u y := fun R u => Submodule.mem_inf
  have hanti : ∀ R R', R ≤ R' → K R' ≤ K R := by
    intro R R' h u hu
    rw [hmemK] at hu ⊢
    exact ⟨hu.1, fun x y hx hy => hu.2 x y (cube_mono h hx) (cube_mono h hy)⟩
  haveI : ∀ R, FiniteDimensional ℝ (K R) := fun R => Submodule.finiteDimensional_of_le inf_le_left
  have hex : ∃ n, ∃ R, Module.finrank ℝ (K R) = n := ⟨_, 0, rfl⟩
  obtain ⟨R₀, hR₀⟩ := Nat.find_spec hex
  have hmin : ∀ R, Nat.find hex ≤ Module.finrank ℝ (K R) := fun R => Nat.find_min' hex ⟨R, rfl⟩
  have hstab : ∀ R, R₀ ≤ R → K R = K R₀ := fun R hR =>
    Submodule.eq_of_le_of_finrank_le (hanti _ _ hR) (hR₀.le.trans (hmin R))
  refine ⟨R₀, fun u hu ⟨a, b, hab⟩ => ?_⟩
  by_contra hcon
  push Not at hcon
  have huK : u ∈ K R₀ := (hmemK R₀ u).mpr ⟨hu, hcon⟩
  obtain ⟨Ra, ha⟩ := exists_mem_cube a.1
  obtain ⟨Rb, hb⟩ := exists_mem_cube b.1
  have hR : R₀ ≤ max R₀ (max Ra Rb) := le_max_left _ _
  rw [← hstab _ hR, hmemK] at huK
  exact hab (huK.2 a b (cube_mono (by omega) ha) (cube_mono (by omega) hb))

/-- The second property of `E_R`: the infinite cluster is unique and every nonconstant function
of `𝒜₁(𝒞_∞)` takes more than one value on `Q_R ∩ 𝒞_∞`. -/
def twoValuedEvent (d R : ℕ) : Set (Configuration d) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∀ u ∈ harmonicGrowthSpace (uniqueInfiniteComponent h) 1, (∃ x y, u x ≠ u y) →
      ∃ x y : uniqueInfiniteComponent h, x.1 ∈ cube d R ∧ y.1 ∈ cube d R ∧ u x ≠ u y}

/-- The second property of `E_R` is monotone in `R`. -/
theorem twoValuedEvent_mono : Monotone (twoValuedEvent d) := by
  rintro R R' h ω ⟨hh, hu⟩
  refine ⟨hh, fun u hu1 hnc => ?_⟩
  obtain ⟨x, y, hx, hy, hxy⟩ := hu u hu1 hnc
  exact ⟨x, y, cube_mono h hx, cube_mono h hy, hxy⟩

/-- **Step `step:4.8-event`** (`EventStep`, paper L1399-1404): `P[E_R] ≥ 1/2` for every large `R`,
from Proposition 2.3, the uniqueness of the infinite cluster and the qualitative corrector input
(`𝒜₁(𝒞_∞)` is finite-dimensional). -/
theorem eventStep [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (hwc : Rigidity.External.WellConnectedInput)
    (hAD : LatticeProb.External.ArmstrongDarioOrderZero)
    (hcorr : LatticeProb.External.SupercriticalBondCorrectorInput) : EventStep d p := by
  set μ := latticeBondLaw d p with hμ
  -- the second property of `E_R` holds almost surely for some `R`
  have hae : ∀ᵐ ω ∂μ, ω ∈ ⋃ R, twoValuedEvent d R := by
    obtain ⟨_, _, _, _, _, _, X, _, _, _, _, hAD'⟩ := hAD d hd p hpc hp1
    filter_upwards [hAD', hcorr d hd p hpc hp1] with ω hω hcω
    obtain ⟨h, -⟩ := hω
    obtain ⟨hplanes, hslope⟩ := hcω h
    obtain ⟨o, ho⟩ := (uniqueInfiniteComponent_infinite h).nonempty
    haveI := finiteDimensional_harmonicGrowthSpace_one _ ⟨o, ho⟩ (fun q => hplanes q _)
      (fun u hu => (hslope u hu).exists)
    obtain ⟨R₀, hR₀⟩ := exists_radius_twoValued (uniqueInfiniteComponent h)
    exact Set.mem_iUnion.mpr ⟨R₀, h, hR₀⟩
  have hU1 : μ (⋃ R, twoValuedEvent d R) = 1 := by
    rw [measure_congr (ae_eq_univ.mpr (ae_iff.mp hae)), measure_univ]
  have hlim : Tendsto (fun R => (μ (twoValuedEvent d R)).toReal) atTop (𝓝 1) := by
    have h := tendsto_measure_iUnion_atTop (μ := μ) twoValuedEvent_mono
    rw [hU1] at h
    have h' := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h
    rw [ENNReal.toReal_one] at h'
    exact h'
  -- the cube fails to be well-connected with probability `≤ C exp(-c R^s) → 0`
  obtain ⟨c, C₀, s, hc, hC₀, hs, hwcb⟩ := hwc d hd p hpc hp1
  have hdecay : Tendsto (fun N : ℕ => C₀ * Real.exp (-(c * (N : ℝ) ^ s))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => c * (N : ℝ) ^ s) atTop atTop :=
      Tendsto.const_mul_atTop hc ((tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C₀
    simpa using h2
  have hev : ∀ᶠ R in atTop, (3 / 4 : ℝ) < (μ (twoValuedEvent d R)).toReal ∧
      C₀ * Real.exp (-(c * (R : ℝ) ^ s)) < 1 / 4 :=
    (hlim.eventually (lt_mem_nhds (by norm_num))).and
      (hdecay.eventually (gt_mem_nhds (by norm_num)))
  obtain ⟨R₁, hR₁⟩ := eventually_atTop.mp hev
  refine ⟨R₁, fun R hR => ?_⟩
  obtain ⟨h34, h14⟩ := hR₁ R hR
  have hWC : (μ {ω | ¬ Rigidity.External.IsWellConnected ω 0 R}).toReal ≤
      C₀ * Real.exp (-(c * (R : ℝ) ^ s)) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hwcb 0 R)
  have hsub : twoValuedEvent d R ⊆
      goodCubeEvent d R ∪ {ω | ¬ Rigidity.External.IsWellConnected ω 0 R} := by
    intro ω hω
    by_cases hw : Rigidity.External.IsWellConnected ω 0 R
    · exact Or.inl ⟨hw, hω⟩
    · exact Or.inr hw
  have hle : (μ (twoValuedEvent d R)).toReal ≤ (μ (goodCubeEvent d R)).toReal +
      (μ {ω | ¬ Rigidity.External.IsWellConnected ω 0 R}).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
      ((measure_mono hsub).trans (measure_union_le _ _))
  linarith

end Rigidity.Proofs.S4
