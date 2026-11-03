import Rigidity.Steps.Section5.RenormalizedDomination

/-!
# Proposition 5.21: the steps of the disjoint paths to infinity

Proposition 5.21 (`prop:disjoint-paths-to-infinty-exponential`, corrected draft L2154-2158, proof
L2253-2276) bounds the probability of the complement of the event `E_R(x)`
(`Rigidity.Section5.eventE`). The proof runs through the renormalized percolation process of size
`R` (`renormField R`, the site `z` open when `(2R + 1) z + Q_{11R/10}` is very good) and splits into
a probabilistic and a deterministic half.

**Probabilistic half.** `RenormClusterBound p`: a site of the renormalized lattice misses the
infinite open clusters of the renormalized process of size `R` with probability at most
`C exp(-c R^s)`. Two routes are given.

* The printed route (`renormClusterBound_of_domination`): Lemma 5.23
  (`RenormalizedDominationStmt`) and
  * `InfiniteClusterMeasurableStep`: the event that a site lies in an infinite open cluster is
    measurable (it is increasing: `isIncreasingSet_inInfiniteSiteCluster`), so the domination
    applies to it;
  * `SiteDensityNearOneStep` (`step:5.21-site-density`; the printed proof cites
    Grimmett, *Percolation*, Theorem 8.92): for Bernoulli site percolation of parameter `q` on
    `ℤ²`, `1 - θ_site(q) ≤ C (1 - q)`. A Peierls bound gives it: if the open cluster of the origin
    is finite, a closed `*`-circuit surrounds the origin, and the `*`-circuits of length `n`
    surrounding it number at most `n 8^n`.
* The route without Liggett-Schonmann-Stacey (`renormClusterBound_of_peierls`), from Proposition
  2.3 (`WellConnectedInput`), Kesten's crossing estimate (`KestenRectangleCrossing`),
  `p_c(2) < p`, the steps `VeryGoodProbabilityStep`, `RenormFieldMeasurableStep`,
  `RenormFieldOneDependentStep` of Lemma 5.23, and
  * `OneDependentPeierlsStep`: a `1`-dependent field on `ℤ²` (for the `ℓ^∞` distance) whose sites
    are closed with probability at most `ε` leaves a site outside its infinite open clusters with
    probability at most `C₀ ε^a`. A closed `*`-circuit of length `n` has at least `n / 9` sites
    at pairwise `ℓ^∞` distance at least `2`, all closed with probability at most `ε^{n/9}`.

  Proposition 5.21 needs no more of Lemma 5.23 than this Peierls bound: the stochastic domination
  (Liggett-Schonmann-Stacey, Theorem 1.3) is used in the printed proof only to transfer
  `1 - θ_site(q) ≤ C (1 - q)` to the renormalized process.

**Deterministic half** (`step:5.21-renorm-paths`, eq. `implication-renormalized-cluster`):
`RenormalizedClusterPathsStep`, if the renormalized site `z` lies in an infinite open cluster
and `x ∈ (2R + 1) z + Q_R`, then `E_R(x)` holds, for `R ≥ R₁(C_f)`. It follows
(`renormalizedClusterPaths_of_cut`) from
* `MengerRaysStep` (Menger's theorem for rays, no literature input): in an open cluster, if no
  set of fewer than `k` vertices meets every infinite path starting in the finite set `S`, there
  are `k` disjoint infinite paths starting in `S`. Finite Menger in the ball of radius `n` around
  `S`, with the sphere of radius `n` as target, gives `k` disjoint paths from `S` to that sphere
  for each `n`; truncation at the first visit of a smaller sphere and König's lemma give rays.
* `KestenChannelCutStep` (the cut form of `step:5.21-renorm-paths`): removing at most `C_f`
  vertices of `𝒞_∞` leaves an infinite path of `𝒞_∞` starting in `S` and avoiding them. The
  Kesten channels of one direction of a very good cube are disjoint, so at most `C_f` of them are
  hit. A path of `S` from `x` to the first exit from `x + Q_{⌊R/10⌋}` stays in
  `(2R + 1) z + Q_{⌊11R/10⌋}` and crosses about `√R / 10` channels transversally, each of which
  it meets (a left-right and a top-bottom crossing of a lattice rectangle share a vertex). Along
  an infinite path of open renormalized sites from `z`, an unhit horizontal and an unhit vertical
  channel of one cube meet; the overlap of two neighbouring cubes, of width at least
  `2 ⌊R/10⌋`, contains about `√R / 5` transverse channels of the first cube, one unhit, and it
  meets the unhit parallel channels of both cubes. The unhit channels along the path thus form an
  infinite connected open set avoiding the removed vertices, containing a vertex of `S`.

The printed proof builds the `C_f + 1` disjoint paths directly by gluing matching channels of
consecutive cubes along a path to infinity of the renormalized cluster (L2260-2263). It does not
address cubes of non-consecutive sites of that path which overlap (diagonal neighbours, or
returns of the path next to itself), where the glued paths of different channels may meet. The
cut form above with Menger's theorem avoids this; the inclusion `implication-renormalized-cluster`
and Proposition 5.21 are unchanged.

The well-connectedness of the very good cubes is not used by the deterministic half: planar
crossings of the channels suffice.
-/

open MeasureTheory LatticeProb.Percolation

namespace Rigidity.Steps.Section5

open Rigidity.Section5

/-- The open subgraph of a site configuration `η` of the renormalized lattice `ℤ²`: two nearest
neighbours are adjacent when both are open. -/
def siteOpenGraph (η : PlanarCarrier → Bool) : SimpleGraph PlanarCarrier where
  Adj z w := |z.1 - w.1| + |z.2 - w.2| = 1 ∧ η z = true ∧ η w = true
  symm := ⟨fun z w h => ⟨by rw [abs_sub_comm w.1, abs_sub_comm w.2]; exact h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun z h => by simp at h⟩

/-- The site `z` of the renormalized lattice lies in an infinite open cluster of `η`. -/
def InInfiniteSiteCluster (η : PlanarCarrier → Bool) (z : PlanarCarrier) : Prop :=
  η z = true ∧ {w | (siteOpenGraph η).Reachable z w}.Infinite

/-- Step `step:5.21-cluster-measurable`: the event that a site lies in an infinite open cluster
is measurable. -/
def InfiniteClusterMeasurableStep : Prop :=
  ∀ z : PlanarCarrier, MeasurableSet {η : PlanarCarrier → Bool | InInfiniteSiteCluster η z}

/-- Step `step:5.21-site-density` (Grimmett, *Percolation*, Theorem 8.92 in the printed proof;
a Peierls bound): for Bernoulli site percolation of parameter `q` on `ℤ²`, a site misses the
infinite open clusters with probability at most `C (1 - q)`, i.e. `θ_site(q) ≥ 1 - C (1 - q)`. -/
def SiteDensityNearOneStep : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (q : NNReal) (hq : q ≤ 1) (z : PlanarCarrier),
    bernoulliFieldPlanar q hq {η | ¬ InInfiniteSiteCluster η z} ≤ ENNReal.ofReal (C * (1 - q))

/-- Step `step:5.21-peierls` (a Peierls bound for `1`-dependent fields): there are `C₀, a > 0`
such that a `1`-dependent field on `ℤ²` (for the `ℓ^∞` distance) whose sites are closed with
probability at most `ε` leaves every site outside its infinite open clusters with probability at
most `C₀ ε^a`. -/
def OneDependentPeierlsStep : Prop :=
  ∃ C₀ a : ℝ, 0 < C₀ ∧ 0 < a ∧ ∀ ν : Measure (PlanarCarrier → Bool), IsProbabilityMeasure ν →
    KDependentPlanar 1 ν → ∀ ε : ℝ, 0 ≤ ε → (∀ z : PlanarCarrier, ν {η | η z = false} ≤
      ENNReal.ofReal ε) → ∀ z : PlanarCarrier,
        ν {η | ¬ InInfiniteSiteCluster η z} ≤ ENNReal.ofReal (C₀ * ε ^ a)

/-- Step `step:5.21-menger` (Menger's theorem for rays): in an open cluster, if every set of fewer
than `k` vertices misses some infinite path starting in the finite set `S`, there are `k`
disjoint infinite paths starting in `S`. -/
def MengerRaysStep : Prop :=
  ∀ (ω : Configuration 2) (C : OpenComponent ω) (S : Set C) (k : ℕ), S.Finite →
    (∀ X : Finset C, X.card < k → ∃ γ : ℕ → C, IsInfinitePathIn C (↑X)ᶜ γ ∧ γ 0 ∈ S) →
      HasDisjointPathsToInfinity C S k

/-- Step `step:5.21-renorm-paths`, cut form: for `R ≥ R₁(C_f)`, if the renormalized site `z`
lies in an infinite open cluster of the renormalized process of size `R` and
`x ∈ (2R + 1) z + Q_R`, then for every finite connected `S ⊆ 𝒞_∞` containing `x` of diameter at
least `R` and every set `X` of at most `C_f` vertices of `𝒞_∞`, some infinite path of `𝒞_∞`
starts in `S` and avoids `X`. -/
def KestenChannelCutStep : Prop :=
  ∀ Cf : ℕ, ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → ∀ (ω : Configuration 2) (z : PlanarCarrier),
    InInfiniteSiteCluster (renormField R ω) z → ∀ x ∈ Rigidity.Section5.cubeAt (renormCentre R z) R,
      ∀ h : HasUniqueInfiniteOpenComponent ω, ∀ S : Set (uniqueInfiniteComponent h),
        S.Finite → IsConnectedSet _ S → (∃ y ∈ S, y.val = x) →
        (∃ y ∈ S, ∃ y' ∈ S, (R : ℝ) ≤ l1 (y.val - y'.val)) →
        ∀ X : Finset (uniqueInfiniteComponent h), X.card ≤ Cf →
          ∃ γ : ℕ → uniqueInfiniteComponent h, IsInfinitePathIn _ (↑X)ᶜ γ ∧ γ 0 ∈ S

/-- Step `step:5.21-renorm-paths` (eq. `implication-renormalized-cluster`): for `R ≥ R₁(C_f)`,
if the renormalized site `z` lies in an infinite open cluster of the renormalized process of size
`R`, the event `E_R(x)` holds for every `x ∈ (2R + 1) z + Q_R`. -/
def RenormalizedClusterPathsStep : Prop :=
  ∀ Cf : ℕ, ∃ R₁ : ℕ, ∀ R : ℕ, R₁ ≤ R → ∀ (ω : Configuration 2) (z : PlanarCarrier),
    InInfiniteSiteCluster (renormField R ω) z → ∀ x ∈ Rigidity.Section5.cubeAt (renormCentre R z) R,
      ω ∈ eventE Cf R x

/-- The probabilistic half of Proposition 5.21: a site of the renormalized lattice misses the
infinite open clusters of the renormalized process of size `R` with probability at most
`C exp(-c R^s)`. -/
def RenormClusterBound (p : unitInterval) : Prop :=
  ∃ C c s : ℝ, 0 < C ∧ 0 < c ∧ 0 < s ∧ ∀ R : ℕ, 1 ≤ R → ∀ z : PlanarCarrier,
    (latticeBondLaw 2 p).map (renormField R) {η | ¬ InInfiniteSiteCluster η z} ≤
      ENNReal.ofReal (C * Real.exp (-(c * (R : ℝ) ^ s)))

theorem siteOpenGraph_mono {η η' : PlanarCarrier → Bool} (h : ∀ s, η s = true → η' s = true) :
    siteOpenGraph η ≤ siteOpenGraph η' :=
  fun _ _ hzw => ⟨hzw.1, h _ hzw.2.1, h _ hzw.2.2⟩

/-- Lying in an infinite open cluster is an increasing event. -/
theorem isIncreasingSet_inInfiniteSiteCluster (z : PlanarCarrier) :
    LatticeProb.StrassenAux.IsIncreasingSet
      {η : PlanarCarrier → Bool | InInfiniteSiteCluster η z} :=
  fun _ _ hη h => ⟨h z hη.1, hη.2.mono fun _ hw => hw.mono (siteOpenGraph_mono h)⟩

/-- A measurable event with larger probability under `ν` than under `B` has a complement with
smaller probability. -/
theorem measure_compl_le_of_le {ν B : Measure (PlanarCarrier → Bool)} [IsProbabilityMeasure ν]
    [IsProbabilityMeasure B] {A : Set (PlanarCarrier → Bool)} (hA : MeasurableSet A)
    (h : B A ≤ ν A) : ν Aᶜ ≤ B Aᶜ := by
  rw [prob_compl_eq_one_sub hA, prob_compl_eq_one_sub hA]
  exact tsub_le_tsub_left h 1

theorem le_coe_min_one_toNNReal {t : ℝ} (ht : t ≤ 1) :
    t ≤ ((min 1 (Real.toNNReal t) : NNReal) : ℝ) := by
  rw [NNReal.coe_min, NNReal.coe_one, Real.coe_toNNReal']
  exact le_min ht (le_max_left _ _)

/-- The probabilistic half of Proposition 5.21 by the printed route: Lemma 5.23 and
`θ_site(q) ≥ 1 - C (1 - q)`. -/
theorem renormClusterBound_of_domination {p : unitInterval} (hD : RenormalizedDominationStmt p)
    (hM : RenormFieldMeasurableStep) (hA : InfiniteClusterMeasurableStep)
    (hθ : SiteDensityNearOneStep) : RenormClusterBound p := by
  obtain ⟨C, c, s, hC, hc, hs, hdom⟩ := hD
  obtain ⟨Cθ, hCθ, hθ⟩ := hθ
  refine ⟨Cθ * C, c, s, by positivity, hc, hs, fun R hR z => ?_⟩
  haveI : IsProbabilityMeasure ((latticeBondLaw 2 p).map (renormField R)) :=
    Measure.isProbabilityMeasure_map (hM R).aemeasurable
  have hle := hdom R hR _ (hA z) (isIncreasingSet_inInfiniteSiteCluster z)
  refine (measure_compl_le_of_le (hA z) hle).trans ((hθ _ _ z).trans
    (ENNReal.ofReal_le_ofReal ?_))
  have he := Real.exp_pos (-(c * (R : ℝ) ^ s))
  have hq := le_coe_min_one_toNNReal (t := 1 - C * Real.exp (-(c * (R : ℝ) ^ s)))
    (by nlinarith)
  calc Cθ * (1 - ((min 1 (Real.toNNReal (1 - C * Real.exp (-(c * (R : ℝ) ^ s)))) : NNReal) : ℝ))
      ≤ Cθ * (C * Real.exp (-(c * (R : ℝ) ^ s))) :=
        mul_le_mul_of_nonneg_left (by linarith) hCθ.le
    _ = Cθ * C * Real.exp (-(c * (R : ℝ) ^ s)) := by ring

/-- The probabilistic half of Proposition 5.21 without the Liggett-Schonmann-Stacey domination:
Proposition 2.3, Kesten's crossing estimate, the very good probability, measurability and
`1`-dependence of the renormalized process, and the Peierls bound for `1`-dependent fields. -/
theorem renormClusterBound_of_peierls {p : unitInterval} (hW : Rigidity.External.WellConnectedInput)
    (hK : Rigidity.External.KestenRectangleCrossing) (hpc : criticalProbability 2 < (p : ℝ))
    (hV : VeryGoodProbabilityStep) (hM : RenormFieldMeasurableStep)
    (hD : RenormFieldOneDependentStep) (hP : OneDependentPeierlsStep) : RenormClusterBound p := by
  obtain ⟨C, c, s, hC, hc, hs, hbound⟩ := hV hW hK p hpc
  obtain ⟨C₀, a, hC₀, ha, hpei⟩ := hP
  refine ⟨C₀ * C ^ a, a * c, s, by positivity, by positivity, hs, fun R _ z => ?_⟩
  have hmeas := hM R
  haveI : IsProbabilityMeasure ((latticeBondLaw 2 p).map (renormField R)) :=
    Measure.isProbabilityMeasure_map hmeas.aemeasurable
  refine (hpei _ inferInstance (hD p R) (C * Real.exp (-(c * ((11 * R / 10 : ℕ) : ℝ) ^ s)))
    (by positivity) (fun w => ?_) z).trans (ENNReal.ofReal_le_ofReal ?_)
  · have hw : MeasurableSet {η : PlanarCarrier → Bool | η w = false} :=
      measurableSet_eq_fun (measurable_pi_apply w) measurable_const
    rw [Measure.map_apply hmeas hw]
    convert hbound (renormCentre R w) (11 * R / 10) using 2
    ext ω
    simp [renormField]
  · rw [Real.mul_rpow hC.le (Real.exp_pos _).le, ← Real.exp_mul]
    have hRr : (R : ℝ) ^ s ≤ ((11 * R / 10 : ℕ) : ℝ) ^ s :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show R ≤ 11 * R / 10 by omega))
        hs.le
    have hexp : Real.exp (-(c * ((11 * R / 10 : ℕ) : ℝ) ^ s) * a) ≤
        Real.exp (-(a * c * (R : ℝ) ^ s)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left hRr (mul_pos ha hc).le])
    calc C₀ * (C ^ a * Real.exp (-(c * ((11 * R / 10 : ℕ) : ℝ) ^ s) * a))
        = C₀ * C ^ a * Real.exp (-(c * ((11 * R / 10 : ℕ) : ℝ) ^ s) * a) := by ring
      _ ≤ C₀ * C ^ a * Real.exp (-(a * c * (R : ℝ) ^ s)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)

/-- The deterministic half of Proposition 5.21 from Menger's theorem for rays and the cut form of
the channel gluing. -/
theorem renormalizedClusterPaths_of_cut (hR : MengerRaysStep) (hG : KestenChannelCutStep) :
    RenormalizedClusterPathsStep := by
  intro Cf
  obtain ⟨R₁, hR₁⟩ := hG Cf
  refine ⟨R₁, fun R hRR ω z hz x hx h S hS hconn hxS hdiam => ?_⟩
  exact hR ω _ S (Cf + 1) hS fun X hX =>
    hR₁ R hRR ω z hz x hx h S hS hconn hxS hdiam X (by omega)

/-- `E_R(x)` shrinks as `R` decreases. -/
theorem eventE_mono {Cf : ℕ} {R R' : ℝ} (hRR' : R ≤ R') {x : Vertex 2} :
    eventE Cf R x ⊆ eventE Cf R' x := fun _ hω h S hS hconn hx hdiam =>
  hω h S hS hconn hx (let ⟨y, hy, y', hy', hd⟩ := hdiam; ⟨y, hy, y', hy', hRR'.trans hd⟩)

/-- The site of the renormalized lattice of size `R` whose cube `(2R + 1) z + Q_R` contains `x`. -/
def renormSite (R : ℕ) (x : Vertex 2) : PlanarCarrier :=
  ((x 0 + R) / (2 * R + 1), (x 1 + R) / (2 * R + 1))

theorem abs_sub_mul_ediv_le (a : ℤ) (R : ℕ) :
    |a - (2 * R + 1) * ((a + R) / (2 * R + 1))| ≤ R := by
  have hn : (0 : ℤ) < 2 * R + 1 := by positivity
  have h1 := Int.emod_def (a + R) (2 * R + 1)
  have h2 := Int.emod_nonneg (a + R) hn.ne'
  have h3 := Int.emod_lt_of_pos (a + R) hn
  rw [abs_le]
  constructor <;> linarith

theorem mem_cubeAt_renormSite (R : ℕ) (x : Vertex 2) :
    x ∈ Rigidity.Section5.cubeAt (renormCentre R (renormSite R x)) R := by
  simp only [Rigidity.Section5.cubeAt, Set.mem_setOf_eq]
  intro i
  fin_cases i
  · exact abs_sub_mul_ediv_le (x 0) R
  · exact abs_sub_mul_ediv_le (x 1) R

/-- Proposition 5.21 from its probabilistic and deterministic halves. -/
theorem disjointPathsToInfinity_of_renormClusterBound {p : unitInterval}
    (hB : RenormClusterBound p) (hM : RenormFieldMeasurableStep)
    (hP : RenormalizedClusterPathsStep) : DisjointPathsToInfinityStmt p := by
  obtain ⟨C, c, s, hC, hc, hs, hbound⟩ := hB
  refine ⟨s, hs, fun Cf => ?_⟩
  obtain ⟨R₁, hR₁⟩ := hP Cf
  have h2s : (0 : ℝ) < 2 ^ s := by positivity
  refine ⟨C + Real.exp (c / 2 ^ s * (R₁ : ℝ) ^ s), c / 2 ^ s, by positivity, by positivity,
    fun x R hR => ?_⟩
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hN1 : 1 ≤ ⌊R⌋₊ := Nat.one_le_floor_iff R |>.mpr hR
  have hNR : (⌊R⌋₊ : ℝ) ≤ R := Nat.floor_le hR0
  have hRN : R < ⌊R⌋₊ + 1 := Nat.lt_floor_add_one R
  have hN1' : (1 : ℝ) ≤ ⌊R⌋₊ := by exact_mod_cast hN1
  have he := Real.exp_pos (-(c / 2 ^ s * R ^ s))
  rcases le_or_gt R₁ ⌊R⌋₊ with hbig | hsmall
  · have hsub : (eventE Cf R x)ᶜ ⊆
        renormField ⌊R⌋₊ ⁻¹' {η | ¬ InInfiniteSiteCluster η (renormSite ⌊R⌋₊ x)} :=
      fun ω hω hin => hω (eventE_mono hNR
        (hR₁ ⌊R⌋₊ hbig ω _ hin x (mem_cubeAt_renormSite ⌊R⌋₊ x)))
    refine (measure_mono hsub).trans ((Measure.le_map_apply (hM _).aemeasurable _).trans
      ((hbound _ hN1 _).trans (ENNReal.ofReal_le_ofReal ?_)))
    have hhalf : R / 2 ≤ (⌊R⌋₊ : ℝ) := by linarith
    have hpow : R ^ s / 2 ^ s ≤ (⌊R⌋₊ : ℝ) ^ s := by
      rw [← Real.div_rpow hR0 (by norm_num)]
      exact Real.rpow_le_rpow (by positivity) hhalf hs.le
    have hexp : Real.exp (-(c * (⌊R⌋₊ : ℝ) ^ s)) ≤ Real.exp (-(c / 2 ^ s * R ^ s)) := by
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hpow hc.le
      rw [mul_div_assoc'] at this
      rw [div_mul_eq_mul_div]
      linarith
    have hE := Real.exp_pos (c / 2 ^ s * (R₁ : ℝ) ^ s)
    calc C * Real.exp (-(c * (⌊R⌋₊ : ℝ) ^ s)) ≤ C * Real.exp (-(c / 2 ^ s * R ^ s)) :=
          mul_le_mul_of_nonneg_left hexp hC.le
      _ ≤ (C + Real.exp (c / 2 ^ s * (R₁ : ℝ) ^ s)) * Real.exp (-(c / 2 ^ s * R ^ s)) :=
          mul_le_mul_of_nonneg_right (by linarith) he.le
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    have hRR₁ : R ≤ R₁ := by
      have : (⌊R⌋₊ : ℝ) + 1 ≤ R₁ := by exact_mod_cast hsmall
      linarith
    have hpow : R ^ s ≤ (R₁ : ℝ) ^ s := Real.rpow_le_rpow hR0 hRR₁ hs.le
    have hone : 1 ≤ Real.exp (c / 2 ^ s * (R₁ : ℝ) ^ s) * Real.exp (-(c / 2 ^ s * R ^ s)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have := mul_le_mul_of_nonneg_left hpow (div_pos hc h2s).le
      linarith
    calc (1 : ℝ) ≤ Real.exp (c / 2 ^ s * (R₁ : ℝ) ^ s) * Real.exp (-(c / 2 ^ s * R ^ s)) := hone
      _ ≤ (C + Real.exp (c / 2 ^ s * (R₁ : ℝ) ^ s)) * Real.exp (-(c / 2 ^ s * R ^ s)) :=
          mul_le_mul_of_nonneg_right (by linarith) he.le

/-- Proposition 5.21 by the printed route: Lemma 5.23, the measurability of the renormalized
process and of the infinite-cluster event, `θ_site(q) ≥ 1 - C (1 - q)`, Menger's theorem for rays
and the cut form of the channel gluing. -/
theorem disjointPathsToInfinity_of_steps {p : unitInterval} (hD : RenormalizedDominationStmt p)
    (hM : RenormFieldMeasurableStep) (hA : InfiniteClusterMeasurableStep)
    (hθ : SiteDensityNearOneStep) (hR : MengerRaysStep) (hG : KestenChannelCutStep) :
    DisjointPathsToInfinityStmt p :=
  disjointPathsToInfinity_of_renormClusterBound (renormClusterBound_of_domination hD hM hA hθ) hM
    (renormalizedClusterPaths_of_cut hR hG)

/-- Proposition 5.21 without the Liggett-Schonmann-Stacey domination: Proposition 2.3, Kesten's
crossing estimate, `p_c(2) < p`, the steps of Lemma 5.23 other than the domination, the Peierls
bound for `1`-dependent fields, Menger's theorem for rays and the cut form of the channel
gluing. -/
theorem disjointPathsToInfinity_of_peierls {p : unitInterval}
    (hW : Rigidity.External.WellConnectedInput) (hK : Rigidity.External.KestenRectangleCrossing)
    (hpc : criticalProbability 2 < (p : ℝ))
    (hV : VeryGoodProbabilityStep) (hM : RenormFieldMeasurableStep)
    (hD : RenormFieldOneDependentStep) (hP : OneDependentPeierlsStep) (hR : MengerRaysStep)
    (hG : KestenChannelCutStep) : DisjointPathsToInfinityStmt p :=
  disjointPathsToInfinity_of_renormClusterBound
    (renormClusterBound_of_peierls hW hK hpc hV hM hD hP) hM
    (renormalizedClusterPaths_of_cut hR hG)

end Rigidity.Steps.Section5
