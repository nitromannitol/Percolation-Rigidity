import Rigidity.Steps.Section5.DisjointPathsToInfinity

/-!
# Proposition 5.24: the steps of the long paths through the good sites

Proposition 5.24 (`prop:longpathsupercritrenormlatt`, corrected draft L2280-2290, proof L2293-2339)
bounds the probability that a path `γ` of `𝒞_∞` from the origin reaching `|γ(end)| ≥ K` has at most
`c₁ |γ(end)|` of its sites in the event `E_R` (`Rigidity.Section5.badPathEvent`). The proof
coarse-grains `γ` on the renormalized lattice of size `r = ⌊R⌋`: the walk `[γ](i)`, the site whose
cube `(2r + 1) [γ](i) + Q_r` contains `γ(i)` (`renormSite`), is a lazy nearest-neighbour walk from
the origin (`isLazyWalk_renormSite`) with `|γ(end)| ≤ (2r + 1) |[γ](end)| + 2r`
(`l1_le_renormSite`).

**Deterministic half** (eq. `implication-renormalized-cluster`, from the proof of Proposition
5.21): `RenormalizedClusterPathsStep`, `E_r(x)` holds for every `x` in the cube of a site of an
infinite open cluster of the renormalized process of size `r`, for `r ≥ R₁(C_f)`. Each distinct
such site visited by `[γ]` thus gives an index `i` of `γ` with `E_R(γ(i))`
(`clusterSiteCount_le_goodCount_add_one`). The printed proof cites Proposition 5.21; it uses this
inclusion of its proof, not its statement (a bound on `P(E_R(x)ᶜ)` for each `x` does not control a
whole path). The inclusion follows from `MengerRaysStep` and `KestenChannelCutStep`
(`renormalizedClusterPaths_of_cut`).

**Probabilistic half** (`step:5.24-crossings`, eq. `kestenchannelsrenormalized`):
`RenormWalkBound p`, for `r` large some `c₂ > 0` makes the event `RenormWalkDeficient c₂ N₀` (a
lazy walk of the renormalized lattice from the origin to `|z|₁ ≥ N₀` visiting fewer than
`c₂ |z|₁` distinct sites of the infinite open clusters) of probability at most `C exp(-c N₀)`.
Then `c₁ = c₂ / (2 (2r + 1))` gives Proposition 5.24
(`longPathRenormalized_of_renormWalkBound`). Two routes give the probabilistic half.

* The printed route (`renormWalkBound_of_domination`): Lemma 5.23
  (`RenormalizedDominationStmt`) and `SiteWalkStep`, the same bound for Bernoulli site
  percolation of parameter `q ≥ q₀`, for a measurable increasing event. The walk crosses one of
  four rectangles of side lengths `≍ N₀` and `≍ 2N₀` around the origin in the short direction,
  hence meets each of `c₂ N₀` disjoint open crossings in the long direction; outside an event of
  probability `C exp(-c N₀)` these crossings exist at every scale `N ≥ N₀`.
* The route without Liggett-Schonmann-Stacey (`renormWalkBound_of_peierls`): the steps
  `VeryGoodProbabilityStep`, `RenormFieldMeasurableStep`, `RenormFieldOneDependentStep` of Lemma
  5.23 and `OneDependentWalkStep`, the bound for `1`-dependent fields (for the `ℓ^∞` distance)
  whose sites are closed with probability at most `ε₀`. It is a Peierls bound: the missing
  crossings give a dual `*`-path of length `L ≥ N₀` with at least `L - c₂ N₀` closed sites, of
  which `(L - c₂ N₀) / 9` are at pairwise `ℓ^∞` distance at least `2`; the `*`-paths number at
  most `(C N₀) 8^L`. Proposition 5.24 needs no more of Lemma 5.23 than this.

Remarks on the printed proof.
* Kesten's Theorem 11.1 is cited for the dominated Bernoulli *site* percolation; the literature
  input `Rigidity.External.KestenRectangleCrossing` is its bond form, which does not apply to it.
  For `q` close to `1` (all that is used) the site crossings follow from the Peierls bound above,
  so `SiteWalkStep` carries no literature input.
* The printed count is of the sites `[γ](i) ∈ 𝒞_∞` of the infinite renormalized cluster, while
  eq. `kestenchannelsrenormalized` only provides open crossings. Their membership in the infinite
  cluster needs crossings linking consecutive scales (the long-direction crossings of the
  rectangles `[0, 4N] × [0, 2N]` and their rotations meet those of scales `N` and `2N`), also
  outside an event of probability `C exp(-c N₀)`; `SiteWalkStep` and `OneDependentWalkStep`
  include it.
* A renormalized walk from the origin leaving `Q^R_N` need not cross `HR^R_N`, of height `2N`; it
  crosses `[-N, N] × [0, N]` or a rotation of it in the short direction. Only constants change.
-/

open MeasureTheory LatticeProb.Percolation Rigidity.External

namespace Rigidity.Steps.Section5

open Rigidity.Section5

/-- A lazy walk of the renormalized lattice: consecutive sites are equal or nearest neighbours. -/
def IsLazyWalk {n : ℕ} (w : Fin (n + 1) → PlanarCarrier) : Prop :=
  ∀ i : Fin n, |(w i.succ).1 - (w i.castSucc).1| + |(w i.succ).2 - (w i.castSucc).2| ≤ 1

open Classical in
/-- The number of distinct sites of the walk `w` lying in infinite open clusters of `η`. -/
noncomputable def clusterSiteCount (η : PlanarCarrier → Bool) {n : ℕ}
    (w : Fin (n + 1) → PlanarCarrier) : ℕ :=
  ((Finset.univ.filter fun i => InInfiniteSiteCluster η (w i)).image w).card

/-- Some lazy walk of the renormalized lattice from the origin to a site `z` with `|z|₁ ≥ N₀`
visits fewer than `c₂ |z|₁` distinct sites of the infinite open clusters of `η`. -/
def RenormWalkDeficient (c₂ N₀ : ℝ) : Set (PlanarCarrier → Bool) :=
  {η | ∃ (n : ℕ) (w : Fin (n + 1) → PlanarCarrier), IsLazyWalk w ∧ w 0 = 0 ∧
    N₀ ≤ ((|(w (Fin.last n)).1| + |(w (Fin.last n)).2| : ℤ) : ℝ) ∧
    (clusterSiteCount η w : ℝ) < c₂ * ((|(w (Fin.last n)).1| + |(w (Fin.last n)).2| : ℤ) : ℝ)}

/-- Step `step:5.24-crossings` for Bernoulli site percolation (eq. `kestenchannelsrenormalized`
and the crossing of the rectangles by `[γ]`): there are `q₀ < 1` and `c₂, C, c > 0` such that for
every `q ≥ q₀` and `N₀ ≥ 1`, outside an event of probability at most `C exp(-c N₀)` under the
Bernoulli site percolation of parameter `q`, which contains the complement of a measurable
increasing event, every lazy walk from the origin to `|z|₁ ≥ N₀` visits at least `c₂ |z|₁`
distinct sites of the infinite open clusters. -/
def SiteWalkStep : Prop :=
  ∃ q₀ : ℝ, q₀ < 1 ∧ ∃ c₂ C c : ℝ, 0 < c₂ ∧ 0 < C ∧ 0 < c ∧
    ∀ (q : NNReal) (hq : q ≤ 1), q₀ ≤ q → ∀ N₀ : ℝ, 1 ≤ N₀ →
      ∃ A : Set (PlanarCarrier → Bool), MeasurableSet A ∧
        LatticeProb.StrassenAux.IsIncreasingSet A ∧ A ⊆ (RenormWalkDeficient c₂ N₀)ᶜ ∧
          bernoulliFieldPlanar q hq Aᶜ ≤ ENNReal.ofReal (C * Real.exp (-(c * N₀)))

/-- Step `step:5.24-crossings` for `1`-dependent fields (a Peierls bound): there are `ε₀ > 0` and
`c₂, C, c > 0` such that a `1`-dependent field on `ℤ²` (for the `ℓ^∞` distance) whose sites are
closed with probability at most `ε₀` gives `RenormWalkDeficient c₂ N₀` (outer) probability at
most `C exp(-c N₀)` for every `N₀ ≥ 1`. -/
def OneDependentWalkStep : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ c₂ C c : ℝ, 0 < c₂ ∧ 0 < C ∧ 0 < c ∧
    ∀ ν : Measure (PlanarCarrier → Bool), IsProbabilityMeasure ν → KDependentPlanar 1 ν →
      (∀ z : PlanarCarrier, ν {η | η z = false} ≤ ENNReal.ofReal ε₀) → ∀ N₀ : ℝ, 1 ≤ N₀ →
        ν (RenormWalkDeficient c₂ N₀) ≤ ENNReal.ofReal (C * Real.exp (-(c * N₀)))

/-- The probabilistic half of Proposition 5.24: for `r ≥ R₀` there are `c₂, C, c > 0` such that
the renormalized process of size `r` lies in `RenormWalkDeficient c₂ N₀` with (outer)
probability at most `C exp(-c N₀)` for every `N₀ ≥ 1`. -/
def RenormWalkBound (p : unitInterval) : Prop :=
  ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → ∃ c₂ C c : ℝ, 0 < c₂ ∧ 0 < C ∧ 0 < c ∧ ∀ N₀ : ℝ, 1 ≤ N₀ →
    latticeBondLaw 2 p {ω | renormField R ω ∈ RenormWalkDeficient c₂ N₀} ≤
      ENNReal.ofReal (C * Real.exp (-(c * N₀)))

theorem renormSite_zero (R : ℕ) : renormSite R 0 = 0 := by
  have h : (R : ℤ) / (2 * R + 1) = 0 := Int.ediv_eq_zero_of_lt (by positivity) (by omega)
  simp [renormSite, h]

/-- Coordinates at distance at most one have renormalized coordinates at distance at most one. -/
theorem abs_ediv_sub_ediv_le_one {a b : ℤ} (R : ℕ) (hab : |a - b| ≤ 1) :
    |(a + R) / (2 * R + 1) - (b + R) / (2 * R + 1)| ≤ 1 := by
  have ha := abs_le.1 (abs_sub_mul_ediv_le a R)
  have hb := abs_le.1 (abs_sub_mul_ediv_le b R)
  have hab' := abs_le.1 hab
  have hm : (0 : ℤ) < 2 * R + 1 := by positivity
  have hR : (0 : ℤ) ≤ R := by positivity
  rw [abs_le]
  constructor
  · by_contra h
    have h2 : (a + R) / (2 * R + 1) - (b + R) / (2 * R + 1) ≤ -2 := by omega
    nlinarith [mul_le_mul_of_nonneg_left h2 hm.le]
  · by_contra h
    have h2 : 2 ≤ (a + R) / (2 * R + 1) - (b + R) / (2 * R + 1) := by omega
    nlinarith [mul_le_mul_of_nonneg_left h2 hm.le]

theorem abs_ediv_sub_ediv_le {a b : ℤ} (R : ℕ) (hab : |a - b| ≤ 1) :
    |(a + R) / (2 * R + 1) - (b + R) / (2 * R + 1)| ≤ |a - b| := by
  by_cases h : a = b
  · subst h; simp
  · have h1 : 0 < |a - b| := abs_pos.2 (sub_ne_zero.2 h)
    have h2 : |a - b| = 1 := le_antisymm hab (by omega)
    rw [h2]
    exact abs_ediv_sub_ediv_le_one R hab

/-- Adjacent vertices of an open cluster are at `ℓ¹` distance one. -/
theorem abs_sub_add_abs_sub_eq_one_of_adj {ω : Configuration 2} {C : OpenComponent ω} {x y : C}
    (h : (componentGraph C).Adj x y) : |x.val 0 - y.val 0| + |x.val 1 - y.val 1| = 1 := by
  have h1 := lattice_adj_iff_l1Dist.1 ((C.toSimpleGraph_adj x.2 y.2).1 h).1
  simpa only [latticeL1Dist, Fin.sum_univ_two] using h1

/-- The coarse-grained walk `[γ]` of a path of an open cluster is a lazy walk. -/
theorem isLazyWalk_renormSite {ω : Configuration 2} {C : OpenComponent ω} {n : ℕ}
    {γ : Fin (n + 1) → C} (hγ : ∀ i : Fin n, (componentGraph C).Adj (γ i.castSucc) (γ i.succ))
    (R : ℕ) : IsLazyWalk fun i => renormSite R (γ i).val := by
  intro i
  have h := abs_sub_add_abs_sub_eq_one_of_adj (hγ i)
  rw [abs_sub_comm ((γ i.castSucc).val 0), abs_sub_comm ((γ i.castSucc).val 1)] at h
  have h0 := abs_nonneg ((γ i.succ).val 0 - (γ i.castSucc).val 0)
  have h1 := abs_nonneg ((γ i.succ).val 1 - (γ i.castSucc).val 1)
  have e0 := abs_ediv_sub_ediv_le R (show |(γ i.succ).val 0 - (γ i.castSucc).val 0| ≤ 1 by linarith)
  have e1 := abs_ediv_sub_ediv_le R (show |(γ i.succ).val 1 - (γ i.castSucc).val 1| ≤ 1 by linarith)
  simp only [renormSite]
  linarith

theorem abs_le_mul_abs_ediv_add (a : ℤ) (R : ℕ) :
    |a| ≤ (2 * R + 1) * |(a + R) / (2 * R + 1)| + R := by
  have h := abs_sub_mul_ediv_le a R
  have hm : (0 : ℤ) < 2 * R + 1 := by positivity
  calc |a| = |(a - (2 * R + 1) * ((a + R) / (2 * R + 1))) +
        (2 * R + 1) * ((a + R) / (2 * R + 1))| := by congr 1; ring
    _ ≤ |a - (2 * R + 1) * ((a + R) / (2 * R + 1))| +
        |(2 * R + 1) * ((a + R) / (2 * R + 1))| := abs_add_le _ _
    _ ≤ (2 * R + 1) * |(a + R) / (2 * R + 1)| + R := by
        rw [abs_mul, abs_of_pos hm]; linarith

/-- `|x|₁ ≤ (2R + 1) |z|₁ + 2R` for the renormalized site `z` of `x`. -/
theorem l1_le_renormSite (R : ℕ) (x : Vertex 2) :
    l1 x ≤ (2 * R + 1) * ((|(renormSite R x).1| + |(renormSite R x).2| : ℤ) : ℝ) + 2 * R := by
  have h0 := abs_le_mul_abs_ediv_add (x 0) R
  have h1 := abs_le_mul_abs_ediv_add (x 1) R
  have hz : |x 0| + |x 1| ≤
      (2 * R + 1) * (|(renormSite R x).1| + |(renormSite R x).2|) + 2 * R := by
    simp only [renormSite]; linarith
  have hr : l1 x = ((|x 0| + |x 1| : ℤ) : ℝ) := by simp [l1, Fin.sum_univ_two]
  rw [hr]
  exact_mod_cast hz

/-- Distinct sites of the walk `w` in infinite open clusters give distinct indices of `γ` with
`E_R(γ(i))`, all but possibly the index `0` counted by `goodCount`. -/
theorem clusterSiteCount_le_goodCount_add_one {ω : Configuration 2} {Cf : ℕ} {R : ℝ}
    {C : OpenComponent ω} {n : ℕ} (γ : Fin (n + 1) → C) (η : PlanarCarrier → Bool)
    (w : Fin (n + 1) → PlanarCarrier)
    (h : ∀ i, InInfiniteSiteCluster η (w i) → ω ∈ eventE Cf R (γ i).val) :
    clusterSiteCount η w ≤ goodCount ω Cf R γ + 1 := by
  unfold clusterSiteCount goodCount
  refine Finset.card_image_le.trans ((Finset.card_le_card ?_).trans (Finset.card_insert_le 0 _))
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hi ⊢
  by_cases h0 : i = 0
  · exact Or.inl h0
  · exact Or.inr ⟨h0, h i hi⟩

/-- `C exp(-c R^s) ≤ ε` for `R` large. -/
theorem exists_nat_mul_exp_neg_rpow_le (C : ℝ) {c s ε : ℝ} (hc : 0 < c) (hs : 0 < s)
    (hε : 0 < ε) : ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R → C * Real.exp (-(c * (R : ℝ) ^ s)) ≤ ε := by
  have h1 : Filter.Tendsto (fun R : ℕ => c * (R : ℝ) ^ s) Filter.atTop Filter.atTop :=
    ((tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  have h2 : Filter.Tendsto (fun R : ℕ => C * Real.exp (-(c * (R : ℝ) ^ s))) Filter.atTop
      (nhds 0) := by
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C
  exact Filter.eventually_atTop.1 (h2 (Iic_mem_nhds hε))

/-- Proposition 5.24 from the inclusion `implication-renormalized-cluster` and its probabilistic
half. -/
theorem longPathRenormalized_of_renormWalkBound {p : unitInterval}
    (hP : RenormalizedClusterPathsStep) (hB : RenormWalkBound p) : LongPathRenormalizedStmt p := by
  intro Cf
  obtain ⟨R₁, hR₁⟩ := hP Cf
  obtain ⟨R₀, hR₀⟩ := hB
  refine ⟨(max R₁ R₀ : ℕ), fun R hR => ?_⟩
  obtain ⟨c₂, C, c, hc₂, hC, hc, hbound⟩ := hR₀ (max R₁ R₀) (le_max_right _ _)
  have hr₁ : R₁ ≤ max R₁ R₀ := le_max_left _ _
  generalize max R₁ R₀ = r at hR hbound hr₁
  have hm : (0 : ℝ) < 2 * r + 1 := by positivity
  have hm' : (2 * r + 1 : ℝ) ≠ 0 := hm.ne'
  have hc₂' : 0 < 2 / c₂ := div_pos two_pos hc₂
  set K₀ : ℝ := (2 * r + 1) * (2 / c₂ + 1) + 2 * r with hK₀
  refine ⟨c₂ / (2 * (2 * r + 1)), by positivity,
    C * Real.exp (c * (2 * r) / (2 * r + 1)) + Real.exp (c / (2 * r + 1) * K₀),
    c / (2 * r + 1), by positivity, by positivity, fun K _ => ?_⟩
  by_cases hKK : K₀ ≤ K
  · have hN₀ : 2 / c₂ + 1 ≤ (K - 2 * r) / (2 * r + 1) := by
      rw [le_div_iff₀ hm]; linarith
    have hsub : badPathEvent Cf R (c₂ / (2 * (2 * r + 1))) K ⊆
        {ω | renormField r ω ∈ RenormWalkDeficient c₂ ((K - 2 * r) / (2 * r + 1))} := by
      rintro ω ⟨h, n, γ, ⟨-, hadj⟩, h0, hKL, hcount⟩
      have hcs := clusterSiteCount_le_goodCount_add_one γ (renormField r ω)
        (fun i => renormSite r (γ i).val) (fun i hi => eventE_mono hR
          (hR₁ r hr₁ ω _ hi _ (mem_cubeAt_renormSite r _)))
      have hL := l1_le_renormSite r (γ (Fin.last n)).val
      set M : ℝ := ((|(renormSite r (γ (Fin.last n)).val).1| +
        |(renormSite r (γ (Fin.last n)).val).2| : ℤ) : ℝ) with hM
      have hNM : (K - 2 * r) / (2 * r + 1) ≤ M := by
        rw [div_le_iff₀ hm]; linarith
      refine ⟨n, fun i => renormSite r (γ i).val, isLazyWalk_renormSite hadj r, ?_, hNM, ?_⟩
      · simp only [h0, renormSite_zero]
      · have hcs' : (clusterSiteCount (renormField r ω) (fun i => renormSite r (γ i).val) : ℝ) ≤
            goodCount ω Cf R γ + 1 := by exact_mod_cast hcs
        have e1 : c₂ / (2 * (2 * r + 1)) * l1 (γ (Fin.last n)).val ≤
            c₂ / (2 * (2 * r + 1)) * ((2 * r + 1) * M + 2 * r) :=
          mul_le_mul_of_nonneg_left hL (by positivity)
        have e2 : c₂ / (2 * (2 * r + 1)) * ((2 * r + 1) * M + 2 * r) =
            c₂ * M / 2 + c₂ * r / (2 * r + 1) := by field_simp
        have e3 : c₂ * r / (2 * r + 1) < c₂ / 2 := by
          rw [div_lt_iff₀ hm]; nlinarith
        have e4 : 2 / c₂ ≤ M - 1 := by linarith
        rw [div_le_iff₀ hc₂] at e4
        show (clusterSiteCount (renormField r ω) (fun i => renormSite r (γ i).val) : ℝ) < c₂ * M
        linarith
    refine (measure_mono hsub).trans ((hbound _ (by linarith)).trans
      (ENNReal.ofReal_le_ofReal ?_))
    have he : C * Real.exp (-(c * ((K - 2 * r) / (2 * r + 1)))) =
        C * Real.exp (c * (2 * r) / (2 * r + 1)) * Real.exp (-(c / (2 * r + 1) * K)) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; field_simp; ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.exp_pos _).le)
      (Real.exp_pos _).le
  · push Not at hKK
    refine prob_le_one.trans (ENNReal.one_le_ofReal.2 ?_)
    have h1 : c / (2 * r + 1) * K ≤ c / (2 * r + 1) * K₀ :=
      mul_le_mul_of_nonneg_left hKK.le (by positivity)
    have h2 : 1 ≤ Real.exp (c / (2 * r + 1) * K₀) * Real.exp (-(c / (2 * r + 1) * K)) := by
      rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
    have h3 : 0 ≤ C * Real.exp (c * (2 * r) / (2 * r + 1)) * Real.exp (-(c / (2 * r + 1) * K)) := by
      positivity
    linarith

/-- The renormalized process is a.e. measurable once it dominates a Bernoulli field. -/
theorem aemeasurable_renormField_of_domination {p : unitInterval}
    (hD : RenormalizedDominationStmt p) {R : ℕ} (hR : 1 ≤ R) :
    AEMeasurable (renormField R) (latticeBondLaw 2 p) := by
  by_contra hnot
  obtain ⟨C, c, s, -, -, -, hdom⟩ := hD
  have h := hdom R hR Set.univ MeasurableSet.univ (fun _ _ _ _ => trivial)
  simp [Measure.map_of_not_aemeasurable hnot] at h

/-- The probabilistic half of Proposition 5.24 by the printed route: Lemma 5.23 and
`step:5.24-crossings` for Bernoulli site percolation. -/
theorem renormWalkBound_of_domination {p : unitInterval} (hD : RenormalizedDominationStmt p)
    (hS : SiteWalkStep) : RenormWalkBound p := by
  have hmeas := fun R (hR : 1 ≤ R) => aemeasurable_renormField_of_domination hD hR
  obtain ⟨C, c, s, hC, hc, hs, hdom⟩ := hD
  obtain ⟨q₀, hq₀, c₂, C', c', hc₂, hC', hc', hsite⟩ := hS
  obtain ⟨R₀, hR₀⟩ := exists_nat_mul_exp_neg_rpow_le C hc hs (sub_pos.2 hq₀)
  refine ⟨max R₀ 1, fun R hR => ⟨c₂, C', c', hc₂, hC', hc', fun N₀ hN₀ => ?_⟩⟩
  have hR1 : 1 ≤ R := le_of_max_le_right hR
  haveI : IsProbabilityMeasure ((latticeBondLaw 2 p).map (renormField R)) :=
    Measure.isProbabilityMeasure_map (hmeas R hR1)
  have hε := hR₀ R (le_of_max_le_left hR)
  have hCe := mul_pos hC (Real.exp_pos (-(c * (R : ℝ) ^ s)))
  have hq := le_coe_min_one_toNNReal (t := 1 - C * Real.exp (-(c * (R : ℝ) ^ s))) (by linarith)
  obtain ⟨A, hA, hinc, hAsub, hAc⟩ :=
    hsite (min 1 (Real.toNNReal (1 - C * Real.exp (-(c * (R : ℝ) ^ s))))) (min_le_left _ _)
      (by linarith) N₀ hN₀
  calc latticeBondLaw 2 p {ω | renormField R ω ∈ RenormWalkDeficient c₂ N₀}
      ≤ latticeBondLaw 2 p (renormField R ⁻¹' Aᶜ) := measure_mono fun ω hω hωA => hAsub hωA hω
    _ = (latticeBondLaw 2 p).map (renormField R) Aᶜ :=
        (Measure.map_apply_of_aemeasurable (hmeas R hR1) hA.compl).symm
    _ ≤ bernoulliFieldPlanar _ (min_le_left _ _) Aᶜ :=
        measure_compl_le_of_le hA (hdom R hR1 A hA hinc)
    _ ≤ _ := hAc

/-- The probabilistic half of Proposition 5.24 without the Liggett-Schonmann-Stacey domination:
Proposition 2.3, Kesten's crossing estimate, the very good probability, measurability and
`1`-dependence of the renormalized process, and the Peierls bound for `1`-dependent fields. -/
theorem renormWalkBound_of_peierls {p : unitInterval} (hW : WellConnectedInput)
    (hK : KestenRectangleCrossing) (hpc : criticalProbability 2 < (p : ℝ))
    (hV : VeryGoodProbabilityStep) (hM : RenormFieldMeasurableStep)
    (hD : RenormFieldOneDependentStep) (hP : OneDependentWalkStep) : RenormWalkBound p := by
  obtain ⟨C, c, s, hC, hc, hs, hbound⟩ := hV hW hK p hpc
  obtain ⟨ε₀, hε₀, c₂, C', c', hc₂, hC', hc', hpei⟩ := hP
  obtain ⟨R₀, hR₀⟩ := exists_nat_mul_exp_neg_rpow_le C hc hs hε₀
  refine ⟨R₀, fun R hR => ⟨c₂, C', c', hc₂, hC', hc', fun N₀ hN₀ => ?_⟩⟩
  have hmeas := hM R
  haveI : IsProbabilityMeasure ((latticeBondLaw 2 p).map (renormField R)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine (Measure.le_map_apply hmeas.aemeasurable _).trans
    (hpei _ inferInstance (hD p R) (fun z => ?_) N₀ hN₀)
  have hz : MeasurableSet {η : PlanarCarrier → Bool | η z = false} :=
    measurableSet_eq_fun (measurable_pi_apply z) measurable_const
  rw [Measure.map_apply hmeas hz]
  have h1 : latticeBondLaw 2 p (renormField R ⁻¹' {η | η z = false}) ≤
      ENNReal.ofReal (C * Real.exp (-(c * ((11 * R / 10 : ℕ) : ℝ) ^ s))) := by
    convert hbound (renormCentre R z) (11 * R / 10) using 2
    ext ω
    simp [renormField]
  exact h1.trans (ENNReal.ofReal_le_ofReal (hR₀ _ (hR.trans (by omega))))

/-- Proposition 5.24 by the printed route: Lemma 5.23, the inclusion
`implication-renormalized-cluster` of the proof of Proposition 5.21, and `step:5.24-crossings`
for Bernoulli site percolation. The regime `p_c(2) < p` enters through Lemma 5.23, which fails
for `p = 0`. -/
theorem longPathRenormalized_of_steps {p : unitInterval} (hD : RenormalizedDominationStmt p)
    (hP : RenormalizedClusterPathsStep) (hS : SiteWalkStep) : LongPathRenormalizedStmt p :=
  longPathRenormalized_of_renormWalkBound hP (renormWalkBound_of_domination hD hS)

/-- Proposition 5.24 without the Liggett-Schonmann-Stacey domination, for `p_c(2) < p`. -/
theorem longPathRenormalized_of_peierls {p : unitInterval} (hW : WellConnectedInput)
    (hK : KestenRectangleCrossing) (hpc : criticalProbability 2 < (p : ℝ))
    (hV : VeryGoodProbabilityStep) (hM : RenormFieldMeasurableStep)
    (hD : RenormFieldOneDependentStep) (hP : RenormalizedClusterPathsStep)
    (hPW : OneDependentWalkStep) : LongPathRenormalizedStmt p :=
  longPathRenormalized_of_renormWalkBound hP (renormWalkBound_of_peierls hW hK hpc hV hM hD hPW)

end Rigidity.Steps.Section5
