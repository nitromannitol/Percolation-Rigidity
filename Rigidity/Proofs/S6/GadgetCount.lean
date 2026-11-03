import Rigidity.Proofs.S6.SingleExit
import Rigidity.Proofs.Ergodic.TranslateDensity
import LatticeProb.Prob.BernoulliFiniteFlip
import LatticeProb.Prob.Percolation.LatticeBondInfiniteEvent
import LatticeProb.Prob.Percolation.OpenGraphTranslation

/-! # Section 6: a positive density of gadget sites in the largest box cluster

`GadgetCountStep` (step:6.5-gadget-count, paper L2962-2964 of the corrected draft): almost surely,
for every large `n`, every admissible largest open cluster `V` of `Q_n = [-n, n]^d` contains at
least `c n^d` sites of gadget pairs (Fig. slow-mixing-gadget).

Route. Fix two directions `i ≠ j`. The gadget at `x` is the pattern in which the open neighbours of
`x` and of `x + e_i + e_j` are exactly `x + e_i` and `x + e_j`; the event `G` at the origin is the
gadget at `0` with `e_i` in an infinite open cluster.

* Proposition 2.3 (`Rigidity.External.WellConnectedInput`) and Borel-Cantelli: almost surely every
  large cube `Q_N` is well-connected.
* Infinite cluster. On that event the good cubes `Q_k`, `k` large, have their clusters joined to
  one another (a crossing path of `Q_k` is long in `Q_{k+1}`), so the union of these clusters is
  one infinite open cluster; by translation invariance the origin lies in an infinite open
  cluster with positive probability. (`p_c < p` alone does not give this here: the monotonicity
  of `θ` is not available, so it is derived from Proposition 2.3 at `p`.)
* Finite energy. Resetting the bonds of `Q_2` to the gadget pattern (all bonds of `Q_2` open
  except the bonds at `0` and `e_i + e_j` outside the gadget) maps the event that the origin lies
  in an infinite cluster into `G`: an open path from the origin to infinity last leaves `Q_2` at
  a site of the boundary of `Q_2`, and the boundary of `Q_2` is joined to `e_i` by open bonds of
  the pattern. Finite flips preserve null sets (`LatticeProb.BernoulliFiniteFlip.full_product_flip_null_iff`),
  so `P[G] > 0`.
* Multiparameter ergodic theorem (`Rigidity.Proofs.Ergodic.translateDensity`): almost surely the
  proportion of sites `y` of `B_N` with `τ_y ω ∈ G` tends to `P[G]`. A site `y` with `τ_y ω ∈ G`
  carries the gadget pair `x = -y`, `x + e_i + e_j`, both in infinite open clusters.
* Geometry (Proposition 2.3). On a well-connected `Q_n`, a site `x` of an infinite open cluster
  with `|x|_∞ ≤ n - 2m` is joined inside the good cube `x + Q_m` to the cluster of that cube (its
  open path to infinity leaves `x + Q_m` after at least `m` steps), hence to every largest open
  cluster of `Q_n` (`SingleExit.reachable_of_isLargestBoxCluster`). With `N = n - 2m - 1 ≥ n/2`
  this gives at least `P[G]/2 · n^d` gadget sites in `V`. -/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Classical Filter Rigidity.Section6
open Rigidity.External (cubeAt openIn IsGoodSubcube IsWellConnected WellConnectedInput)

namespace Rigidity.Proofs.S6

namespace GadgetCount

open SingleExit

variable {d : ℕ}

/-! ### Sites of infinite open clusters lie in the largest box cluster -/

/-- A walk from a site reachable inside `C` to a site outside `C` passes through a site reachable
inside `C` with an open neighbour outside `C`. -/
theorem exists_exit {ω : Configuration d} {C : Set (Vertex d)} {x w z : Vertex d}
    (W : (openGraph ω).Walk w z) (hz : z ∉ C) (hw : w ∈ C) (hxw : (openIn ω C).Reachable x w) :
    ∃ a ∈ C, (openIn ω C).Reachable x a ∧ ∃ b ∉ C, (openGraph ω).Adj a b := by
  induction W with
  | nil => exact absurd hw hz
  | @cons u v z' hadj W' ih =>
    by_cases hv : v ∈ C
    · exact ih hz hv (hxw.trans (SimpleGraph.Adj.reachable ⟨hadj, hw, hv⟩))
    · exact ⟨u, hw, hxw, v, hv, hadj⟩

theorem cubeAt_finite (x : Vertex d) (m : ℕ) : (cubeAt x m).Finite := by
  refine (Fintype.piFinset fun i => Finset.Icc (x i - m) (x i + m)).finite_toSet.subset ?_
  intro y hy
  refine Finset.mem_coe.mpr (Fintype.mem_piFinset.mpr fun i => Finset.mem_Icc.mpr ?_)
  have := abs_le.mp (hy i)
  constructor <;> linarith [this.1, this.2]

theorem openIn_le_openGraph (ω : Configuration d) (B : Set (Vertex d)) :
    openIn ω B ≤ openGraph ω :=
  fun _ _ h => h.1

theorem mem_cube_two_iff {u : Vertex d} : u ∈ cube d 2 ↔ ∀ k, |u k| ≤ 2 := by
  simp [cube]

theorem mem_cubeAt_self (x : Vertex d) (m : ℕ) : x ∈ cubeAt x m := fun i => by simp

/-- A site `x` of an infinite open cluster is joined, inside a good cube `x + Q_m`, to the cluster
of that cube: an open path from `x` leaves the cube after at least `m` steps. -/
theorem exists_reachable_goodCluster {ω : Configuration d} {x : Vertex d} {m : ℕ}
    (hg : IsGoodSubcube ω x m) (hx : ω ∈ infiniteComponentEvent x) :
    ∃ y ∈ goodCluster ω x m, (openIn ω (cubeAt x m)).Reachable x y := by
  have hfin := cubeAt_finite x m
  obtain ⟨z, hz, hxz⟩ := (mem_infiniteComponentEvent_iff ω x).mp hx hfin.toFinset
  have hzC : z ∉ cubeAt x m := fun h => hz (hfin.mem_toFinset.mpr h)
  obtain ⟨W⟩ := hxz
  obtain ⟨a, -, hxa, b, hbC, hab⟩ :=
    exists_exit W hzC (mem_cubeAt_self x m) SimpleGraph.Reachable.rfl
  obtain ⟨i, hi⟩ : ∃ i, (m : ℤ) < |b i - x i| := by
    by_contra h
    push Not at h
    exact hbC h
  have ham : (m : ℤ) ≤ |a i - x i| := by
    have h1 := abs_sub_le_one_of_adj hab i
    have h2 := abs_sub_le (b i) (a i) (x i)
    have h3 := Int.lt_iff_add_one_le.mp hi
    linarith
  obtain ⟨P⟩ := hxa
  set q := P.bypass with hq
  have hqp : q.IsPath := P.bypass_isPath
  have hlen : (m : ℤ) ≤ q.length := ham.trans (abs_sub_le_length (openIn_adj_le_one i) q)
  let γ : Fin (q.length + 1) → Vertex d := fun j => q.getVert j
  have hinj : Function.Injective γ := by
    intro j k hjk
    exact Fin.ext (hqp.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hjk)
  have hadj : ∀ j : Fin q.length, (openIn ω (cubeAt x m)).Adj (γ j.castSucc) (γ j.succ) :=
    fun j => q.adj_getVert_succ j.2
  have hL : (m : ℝ) / 100 ≤ q.length := by
    have : (m : ℝ) ≤ q.length := by exact_mod_cast hlen
    have h0 : (0 : ℝ) ≤ m := by positivity
    linarith
  obtain ⟨y, hy, hreach⟩ := (goodCluster_spec hg).2.2 q.length γ hinj hadj hL
  have hγ0 : γ 0 = x := by simp [γ]
  rw [hγ0] at hreach
  exact ⟨y, hy, hreach⟩

/-- On a cube all of whose radius-`m` and radius-`2m` subcubes are good, every site `x` of an
infinite open cluster with `|x|_∞ ≤ n - 2m` lies in every largest open cluster of `Q_n`. -/
theorem mem_of_mem_infiniteComponentEvent [NeZero d] (hd : 2 ≤ d) {ω : Configuration d}
    {n m : ℕ} (hg : CubesGood ω n m) (hm : 1 ≤ m) (hnm : 2 * m ≤ n)
    (hK : (2 * m + 1) ^ d < (2 * (n - 2 * m) + 1) / (2 * m + 1)) {V : Finset (Vertex d)}
    (hV : IsLargestBoxCluster ω n V) {x : Vertex d} (hx : ∀ i, |x i| ≤ (n : ℤ) - 2 * m)
    (hinf : ω ∈ infiniteComponentEvent x) : x ∈ V := by
  have hm0 : (0 : ℤ) ≤ m := by positivity
  have h0n : ∀ i, |(0 : Vertex d) i| ≤ n := fun i => by simp
  obtain ⟨x₀, hx₀⟩ := goodCluster_nonempty (hg 0 h0n).1
  obtain ⟨v₀, hv₀, hVv⟩ := hV.1
  have hx₀v₀ := reachable_of_isLargestBoxCluster hd hg hm hnm hK hx₀ hV hv₀ hVv
  have hxn : ∀ i, |x i| ≤ n := fun i => by linarith [hx i]
  obtain ⟨y, hy, hxy⟩ := exists_reachable_goodCluster (hg x hxn).1 hinf
  have hsub : cubeAt x m ⊆ cube d n := cubeAt_subset_cube fun i => by linarith [hx i]
  have hxy' : (boxOpenGraph ω n).Reachable x y := by
    rw [← openIn_cube]
    exact hxy.mono (openIn_mono hsub)
  have hx₀y := reachable_chain hg hm hnm hx₀ _ x rfl hx y hy
  have hv₀x : x ∈ boxCluster ω n v₀ := (hx₀v₀.symm.trans hx₀y).trans hxy'.symm
  have : x ∈ (V : Set (Vertex d)) := by rw [hVv]; exact hv₀x
  exact this

/-! ### The gadget pattern -/

/-- The gadget of Fig. slow-mixing-gadget at `x` in the directions `i, j`: the open neighbours of
`x` and of `x + e_i + e_j` are exactly `x + e_i` and `x + e_j`. -/
def GadgetAt (ω : Configuration d) (i j : Fin d) (x : Vertex d) : Prop :=
  (∀ v, (openGraph ω).Adj x v ↔ v = x + LatticeProb.unit i ∨ v = x + LatticeProb.unit j) ∧
    ∀ v, (openGraph ω).Adj (x + LatticeProb.unit i + LatticeProb.unit j) v ↔
      v = x + LatticeProb.unit i ∨ v = x + LatticeProb.unit j

theorem unit_apply (i k : Fin d) : LatticeProb.unit i k = if k = i then 1 else 0 := by
  simp [LatticeProb.unit, Pi.single_apply]

theorem isGadgetPair_of_gadgetAt {ω : Configuration d} {i j : Fin d} (hij : i ≠ j)
    {x : Vertex d} (h : GadgetAt ω i j x) :
    Steps.S6.IsGadgetPair ω x (x + LatticeProb.unit i + LatticeProb.unit j) := by
  have hne : x + LatticeProb.unit i ≠ x + LatticeProb.unit j := by
    intro he
    have := congrFun he i
    simp [unit_apply, hij] at this
  have hdeg : ∀ u, (∀ v, (openGraph ω).Adj u v ↔
      v = x + LatticeProb.unit i ∨ v = x + LatticeProb.unit j) → (openGraph ω).degree u = 2 := by
    intro u hu
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have : (openGraph ω).neighborFinset u = {x + LatticeProb.unit i, x + LatticeProb.unit j} := by
      ext v
      rw [SimpleGraph.mem_neighborFinset, hu v]
      simp
    rw [this, Finset.card_pair hne]
  refine ⟨?_, hdeg x h.1, hdeg _ h.2, fun v => by rw [h.1 v, h.2 v]⟩
  intro he
  have := congrFun he i
  simp [unit_apply, hij] at this

theorem measurableSet_gadgetAt (i j : Fin d) (x : Vertex d) :
    MeasurableSet {ω : Configuration d | GadgetAt ω i j x} := by
  have key : ∀ (u : Vertex d) (P : Vertex d → Prop),
      MeasurableSet {ω : Configuration d | ∀ v, (openGraph ω).Adj u v ↔ P v} := by
    intro u P
    have : {ω : Configuration d | ∀ v, (openGraph ω).Adj u v ↔ P v} =
        ⋂ v, {ω | (openGraph ω).Adj u v ↔ P v} := by
      ext
      simp
    rw [this]
    refine MeasurableSet.iInter fun v => ?_
    by_cases hP : P v
    · have : {ω : Configuration d | (openGraph ω).Adj u v ↔ P v} =
          {ω | (openGraph ω).Adj u v} := by
        ext
        simp [hP]
      rw [this]
      exact measurableSet_openGraph_adj u v
    · have : {ω : Configuration d | (openGraph ω).Adj u v ↔ P v} =
          {ω | (openGraph ω).Adj u v}ᶜ := by
        ext
        simp [hP]
      rw [this]
      exact (measurableSet_openGraph_adj u v).compl
  exact (key _ _).inter (key _ _)

/-- The event at the origin: the gadget at `0` in the directions `i, j`, with `e_i` in an infinite
open cluster. -/
def gadgetEvent (i j : Fin d) : Set (Configuration d) :=
  {ω | GadgetAt ω i j 0} ∩ infiniteComponentEvent (LatticeProb.unit i)

theorem measurableSet_gadgetEvent (i j : Fin d) : MeasurableSet (gadgetEvent (d := d) i j) :=
  (measurableSet_gadgetAt i j 0).inter (measurableSet_infiniteComponentEvent _)

/-! ### Translations -/

theorem gadgetAt_translation_iff (z : Vertex d) (ω : Configuration d) (i j : Fin d)
    (x : Vertex d) :
    GadgetAt (configurationTranslation z ω) i j (x + z) ↔ GadgetAt ω i j x := by
  have e1 : ∀ k, x + z + LatticeProb.unit k = x + LatticeProb.unit k + z := fun k => by abel
  have key : ∀ u : Vertex d,
      (∀ v, (openGraph (configurationTranslation z ω)).Adj (u + z) v ↔
        v = x + z + LatticeProb.unit i ∨ v = x + z + LatticeProb.unit j) ↔
      (∀ v, (openGraph ω).Adj u v ↔ v = x + LatticeProb.unit i ∨ v = x + LatticeProb.unit j) := by
    intro u
    simp only [e1]
    constructor
    · intro h v
      rw [← openGraph_adj_translation_iff z ω u v, h, add_left_inj, add_left_inj]
    · intro h v
      rw [← sub_add_cancel v z, openGraph_adj_translation_iff, h, add_left_inj, add_left_inj]
  have e2 : x + z + LatticeProb.unit i + LatticeProb.unit j =
      x + LatticeProb.unit i + LatticeProb.unit j + z := by abel
  unfold GadgetAt
  rw [e2]
  exact and_congr (key x) (key _)

theorem infiniteComponentEvent_translation_iff (z : Vertex d) (ω : Configuration d)
    (x : Vertex d) :
    configurationTranslation z ω ∈ infiniteComponentEvent x ↔
      ω ∈ infiniteComponentEvent (x - z) := by
  simp only [mem_infiniteComponentEvent_iff, openGraph_reachable_sub_translation_iff]
  constructor
  · intro h s
    obtain ⟨y, hy, hr⟩ := h (s.image (· + z))
    exact ⟨y - z, fun hs => hy (Finset.mem_image.mpr ⟨y - z, hs, sub_add_cancel y z⟩), hr⟩
  · intro h s
    obtain ⟨y, hy, hr⟩ := h (s.image (· - z))
    refine ⟨y + z, fun hs => hy (Finset.mem_image.mpr ⟨y + z, hs, add_sub_cancel_right y z⟩), ?_⟩
    rwa [add_sub_cancel_right]

theorem mem_infiniteComponentEvent_of_reachable {ω : Configuration d} {x y : Vertex d}
    (h : (openGraph ω).Reachable x y) (hy : ω ∈ infiniteComponentEvent y) :
    ω ∈ infiniteComponentEvent x := by
  change ((openGraph ω).connectedComponentMk x).supp.Infinite
  rw [SimpleGraph.ConnectedComponent.sound h]
  exact hy

theorem measure_infiniteComponentEvent (p : unitInterval) (x : Vertex d) :
    latticeBondLaw d p (infiniteComponentEvent x) =
      latticeBondLaw d p (infiniteComponentEvent 0) := by
  have hpre : configurationTranslation (-x) ⁻¹' infiniteComponentEvent 0 =
      infiniteComponentEvent x := by
    ext ω
    simp only [Set.mem_preimage, infiniteComponentEvent_translation_iff, zero_sub, neg_neg]
  rw [← hpre, (measurePreserving_configurationTranslation p (-x)).measure_preimage
    (measurableSet_infiniteComponentEvent 0).nullMeasurableSet]

/-! ### An infinite open cluster from Proposition 2.3 -/

/-- Almost surely every large cube `Q_N` is well-connected (Proposition 2.3, Borel-Cantelli). -/
theorem ae_eventually_isWellConnected [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hwc : WellConnectedInput) :
    ∀ᵐ ω ∂latticeBondLaw d p, ∀ᶠ N : ℕ in atTop, IsWellConnected ω 0 N := by
  obtain ⟨c, C, s, hc, hC, hs, hbound⟩ := hwc d hd p hpc hp1
  have hfs : Summable fun N : ℕ => C * Real.exp (-(c * (N : ℝ) ^ s)) := by
    simpa using (summable_pow_mul_exp_neg_rpow 0 hc hs).mul_left C
  have hsum : ∑' N, latticeBondLaw d p {ω | ¬ IsWellConnected ω 0 N} ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun N => hbound 0 N)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun N => by positivity) hfs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  filter_upwards [hω] with N hN
  simpa using hN

/-- If every large cube `Q_N` is well-connected, some site lies in an infinite open cluster: the
clusters of the good cubes `Q_k`, `k` large, are joined to one another and cross `Q_k`. -/
theorem exists_mem_infiniteComponentEvent [NeZero d] {ω : Configuration d}
    (h : ∀ᶠ N : ℕ in atTop, IsWellConnected ω 0 N) :
    ∃ x : Vertex d, ω ∈ infiniteComponentEvent x := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp h
  have hgood : ∀ k : ℕ, N₀ < k → IsGoodSubcube ω 0 k := by
    intro k hk
    have hW := hN₀ (10 * k) (by omega)
    have hk0 : (0 : ℝ) ≤ k := by positivity
    refine hW.2.2 0 k ?_ ?_ ⟨0, fun i => by simp, fun i => by simp⟩
    · have := hW.1
      push_cast at this ⊢
      linarith
    · push_cast
      linarith
  obtain ⟨x₀, hx₀⟩ := goodCluster_nonempty (hgood (N₀ + 1) (by omega))
  have hreach : ∀ k, N₀ + 1 ≤ k → ∀ y ∈ goodCluster ω 0 k, (openGraph ω).Reachable x₀ y := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro y hy
      exact (reachable_of_mem_goodCluster (hgood (N₀ + 1) (by omega)) hx₀ hy).mono
        (openIn_le_openGraph ω _)
    | succ k hk ih =>
      intro y hy
      obtain ⟨y', hy'⟩ := goodCluster_nonempty (hgood k (by omega))
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      have hsub : cubeAt (0 : Vertex d) k ⊆ cubeAt 0 (k + 1) := fun v hv i =>
        le_trans (hv i) (by push_cast; omega)
      have := reachable_goodCluster_of_subset (hgood (k + 1) (by omega)) (hgood k (by omega))
        hsub (by push_cast; linarith) hy' hy
      exact (ih y' hy').trans (this.mono (openIn_le_openGraph ω _))
  refine ⟨x₀, (mem_infiniteComponentEvent_iff ω x₀).mpr fun s => ?_⟩
  set K := max (N₀ + 1) (s.sup fun y => (y 0).natAbs) + 1 with hKdef
  obtain ⟨-, ⟨y, hy, hy0⟩⟩ := (goodCluster_spec (hgood K (by omega))).2.1 0
  refine ⟨y, fun hys => ?_, hreach K (by omega) y hy⟩
  have h1 : (y 0).natAbs ≤ s.sup fun y => (y 0).natAbs :=
    Finset.le_sup (f := fun y : Vertex d => (y 0).natAbs) hys
  have h2 : y 0 = K := by simpa using hy0
  rw [h2, Int.natAbs_natCast] at h1
  omega

/-- The origin lies in an infinite open cluster with positive probability. -/
theorem measure_infiniteComponentEvent_ne_zero [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hwc : WellConnectedInput) :
    latticeBondLaw d p (infiniteComponentEvent 0) ≠ 0 := by
  intro h0
  have hnull : latticeBondLaw d p (⋃ x : Vertex d, infiniteComponentEvent x) = 0 :=
    measure_iUnion_null fun x => by rw [measure_infiniteComponentEvent]; exact h0
  have hae : ∀ᵐ ω ∂latticeBondLaw d p, ω ∈ ⋃ x : Vertex d, infiniteComponentEvent x := by
    filter_upwards [ae_eventually_isWellConnected hd p hpc hp1 hwc] with ω hω
    exact Set.mem_iUnion.mpr (exists_mem_infiniteComponentEvent hω)
  have hae' : latticeBondLaw d p (⋃ x : Vertex d, infiniteComponentEvent x)ᶜ = 0 := ae_iff.mp hae
  have := measure_union_null hae' hnull
  rw [Set.compl_union_self, measure_univ] at this
  exact one_ne_zero this

/-! ### Finite energy: resetting the bonds of `Q_2` to the gadget -/

theorem abs_sub_le_one_of_lattice_adj {u v : Vertex d} (h : (nearestNeighborGraph d).Adj u v)
    (k : Fin d) : |v k - u k| ≤ 1 := by
  obtain ⟨l, hl | hl⟩ := h <;> subst hl <;> by_cases hkl : k = l <;> simp [LatticeProb.unit, hkl]

theorem abs_unit_add_unit_le_one {i j : Fin d} (hij : i ≠ j) (k : Fin d) :
    |(LatticeProb.unit i + LatticeProb.unit j : Vertex d) k| ≤ 1 := by
  rw [Pi.add_apply, unit_apply, unit_apply]
  by_cases h1 : k = i
  · subst h1
    simp [hij]
  · by_cases h2 : k = j
    · subst h2
      simp [h1]
    · simp [h1, h2]

/-- The bond `{u, v}` is open in the gadget pattern: it is not a bond at `0` or `e_i + e_j`, or it
is one of the four bonds of the gadget. -/
def GadgetOpen (i j : Fin d) (u v : Vertex d) : Prop :=
  (¬((0 : Vertex d) = u ∨ (0 : Vertex d) = v) ∧
      ¬(LatticeProb.unit i + LatticeProb.unit j = u ∨ LatticeProb.unit i + LatticeProb.unit j = v)) ∨
    (LatticeProb.unit i = u ∨ LatticeProb.unit i = v) ∨
      (LatticeProb.unit j = u ∨ LatticeProb.unit j = v)

/-- The gadget pattern on bonds. -/
noncomputable def gadgetPattern (i j : Fin d) (e : Bond d) : Bool :=
  decide (((0 : Vertex d) ∉ e.1 ∧ LatticeProb.unit i + LatticeProb.unit j ∉ e.1) ∨
    LatticeProb.unit i ∈ e.1 ∨ LatticeProb.unit j ∈ e.1)

theorem gadgetPattern_bondOfAdjacent {i j : Fin d} {u v : Vertex d}
    (h : (nearestNeighborGraph d).Adj u v) :
    gadgetPattern i j (bondOfAdjacent h) = true ↔ GadgetOpen i j u v := by
  simp only [gadgetPattern, decide_eq_true_eq, GadgetOpen]
  show ((0 : Vertex d) ∉ s(u, v) ∧ _ ∉ s(u, v)) ∨ _ ∈ s(u, v) ∨ _ ∈ s(u, v) ↔ _
  simp only [Sym2.mem_iff]

/-- `ω` with the bonds of `Q_2` reset to the gadget pattern (a finite flip of `ω`). -/
noncomputable def setGadget (i j : Fin d) (ω : Configuration d) : Configuration d :=
  LatticeProb.BernoulliFiniteFlip.flip ((insideBonds d 2).filter fun e => ω e ≠ gadgetPattern i j e) ω

theorem setGadget_apply (i j : Fin d) (ω : Configuration d) (e : Bond d) :
    setGadget i j ω e = if e ∈ insideBonds d 2 then gadgetPattern i j e else ω e := by
  unfold setGadget
  rw [LatticeProb.BernoulliFiniteFlip.flip_apply]
  by_cases he : e ∈ insideBonds d 2
  · simp only [Finset.mem_filter, he, true_and, if_true]
    by_cases hω : ω e = gadgetPattern i j e
    · rw [if_neg (not_not_intro hω)]
      exact hω
    · rw [if_pos hω]
      revert hω
      cases ω e <;> cases gadgetPattern i j e <;> simp
  · simp [he]

theorem not_mem_insideBonds {n : ℕ} {u v : Vertex d} (h : (nearestNeighborGraph d).Adj u v)
    (huv : u ∉ cube d n ∨ v ∉ cube d n) : bondOfAdjacent h ∉ insideBonds d n := by
  intro hb
  rw [insideBonds, Finset.mem_subtype] at hb
  obtain ⟨⟨x, y⟩, hxy, heq⟩ := Finset.mem_image.mp hb
  rw [Finset.mem_product] at hxy
  have hx := Steps.S6.mem_cubeFinset.mp hxy.1
  have hy := Steps.S6.mem_cubeFinset.mp hxy.2
  have heq' : s(x, y) = s(u, v) := heq
  rcases Sym2.eq_iff.mp heq' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto

theorem setGadget_adj_iff_of_not_mem {i j : Fin d} {ω : Configuration d} {u v : Vertex d}
    (huv : u ∉ cube d 2 ∨ v ∉ cube d 2) :
    (openGraph (setGadget i j ω)).Adj u v ↔ (openGraph ω).Adj u v := by
  constructor
  · rintro ⟨h, ho⟩
    refine ⟨h, ?_⟩
    rwa [setGadget_apply, if_neg (not_mem_insideBonds h huv)] at ho
  · rintro ⟨h, ho⟩
    refine ⟨h, ?_⟩
    rwa [setGadget_apply, if_neg (not_mem_insideBonds h huv)]

theorem setGadget_adj_iff_of_mem {i j : Fin d} {ω : Configuration d} {u v : Vertex d}
    (hu : u ∈ cube d 2) (hv : v ∈ cube d 2) :
    (openGraph (setGadget i j ω)).Adj u v ↔
      (nearestNeighborGraph d).Adj u v ∧ GadgetOpen i j u v := by
  constructor
  · rintro ⟨h, ho⟩
    rw [setGadget_apply, if_pos (bondOfAdjacent_mem_insideBonds h hu hv)] at ho
    exact ⟨h, (gadgetPattern_bondOfAdjacent h).mp ho⟩
  · rintro ⟨h, ho⟩
    refine ⟨h, ?_⟩
    rw [setGadget_apply, if_pos (bondOfAdjacent_mem_insideBonds h hu hv)]
    exact (gadgetPattern_bondOfAdjacent h).mpr ho

theorem mem_cube_two_of_adj {u v : Vertex d} (h : (nearestNeighborGraph d).Adj u v)
    (hu : ∀ k, |u k| ≤ 1) : v ∈ cube d 2 := by
  intro k
  have h1 := abs_sub_le_one_of_lattice_adj h k
  have h2 := abs_sub_abs_le_abs_sub (v k) (u k)
  have h3 := hu k
  push_cast
  linarith

theorem unit_ne_unit {i j : Fin d} (hij : i ≠ j) :
    (LatticeProb.unit i : Vertex d) ≠ LatticeProb.unit j := by
  intro h
  have := congrFun h i
  simp [unit_apply, hij] at this

theorem unit_ne_unit_add_unit {i j : Fin d} (hij : i ≠ j) :
    (LatticeProb.unit i : Vertex d) ≠ LatticeProb.unit i + LatticeProb.unit j := by
  intro h
  have := congrFun h j
  simp [unit_apply, Ne.symm hij] at this

/-- In the reset configuration, the gadget sits at the origin. -/
theorem gadgetAt_setGadget {i j : Fin d} (hij : i ≠ j) (ω : Configuration d) :
    GadgetAt (setGadget i j ω) i j 0 := by
  set ui : Vertex d := LatticeProb.unit i
  set uj : Vertex d := LatticeProb.unit j
  have hui0 : ui ≠ 0 := LatticeProb.unit_ne_zero i
  have huj0 : uj ≠ 0 := LatticeProb.unit_ne_zero j
  have huib : ui ≠ ui + uj := unit_ne_unit_add_unit hij
  have hujb : uj ≠ ui + uj := by
    rw [add_comm]
    exact unit_ne_unit_add_unit (Ne.symm hij)
  have h0 : ∀ k, |(0 : Vertex d) k| ≤ 1 := fun k => by simp
  have hb : ∀ k, |(ui + uj) k| ≤ 1 := abs_unit_add_unit_le_one hij
  have h0c : (0 : Vertex d) ∈ cube d 2 := fun k => by simp
  have hbc : ui + uj ∈ cube d 2 := fun k => by
    have := hb k
    push_cast
    linarith
  have hadj0i : (nearestNeighborGraph d).Adj 0 ui := ⟨i, Or.inl (zero_add _).symm⟩
  have hadj0j : (nearestNeighborGraph d).Adj 0 uj := ⟨j, Or.inl (zero_add _).symm⟩
  have hadjbi : (nearestNeighborGraph d).Adj (ui + uj) ui := ⟨j, Or.inr rfl⟩
  have hadjbj : (nearestNeighborGraph d).Adj (ui + uj) uj := ⟨i, Or.inr (add_comm _ _)⟩
  simp only [GadgetAt, zero_add]
  constructor
  · intro v
    constructor
    · intro hv
      have hvc := mem_cube_two_of_adj hv.1 h0
      obtain ⟨-, hg⟩ := (setGadget_adj_iff_of_mem h0c hvc).mp hv
      rcases hg with ⟨h1, -⟩ | (h1 | h1) | (h1 | h1)
      · exact absurd (Or.inl rfl) h1
      · exact absurd h1 hui0
      · exact Or.inl h1.symm
      · exact absurd h1 huj0
      · exact Or.inr h1.symm
    · rintro (rfl | rfl)
      · exact (setGadget_adj_iff_of_mem h0c (mem_cube_two_of_adj hadj0i h0)).mpr
          ⟨hadj0i, Or.inr (Or.inl (Or.inr rfl))⟩
      · exact (setGadget_adj_iff_of_mem h0c (mem_cube_two_of_adj hadj0j h0)).mpr
          ⟨hadj0j, Or.inr (Or.inr (Or.inr rfl))⟩
  · intro v
    constructor
    · intro hv
      have hvc := mem_cube_two_of_adj hv.1 hb
      obtain ⟨-, hg⟩ := (setGadget_adj_iff_of_mem hbc hvc).mp hv
      rcases hg with ⟨-, h1⟩ | (h1 | h1) | (h1 | h1)
      · exact absurd (Or.inl rfl) h1
      · exact absurd h1 huib
      · exact Or.inl h1.symm
      · exact absurd h1 hujb
      · exact Or.inr h1.symm
    · rintro (rfl | rfl)
      · exact (setGadget_adj_iff_of_mem hbc (mem_cube_two_of_adj hadjbi hb)).mpr
          ⟨hadjbi, Or.inr (Or.inl (Or.inr rfl))⟩
      · exact (setGadget_adj_iff_of_mem hbc (mem_cube_two_of_adj hadjbj hb)).mpr
          ⟨hadjbj, Or.inr (Or.inr (Or.inr rfl))⟩

/-- The boundary of `Q_2`: sites of `Q_2` with a coordinate of absolute value `2`. -/
def IsRim (u : Vertex d) : Prop := u ∈ cube d 2 ∧ ∃ k, |u k| = 2

theorem setGadget_adj_of_rim {i j : Fin d} (hij : i ≠ j) (ω : Configuration d) {u v : Vertex d}
    (hu : IsRim u) (hv : IsRim v) (h : (nearestNeighborGraph d).Adj u v) :
    (openGraph (setGadget i j ω)).Adj u v := by
  have hn0 : ∀ w : Vertex d, IsRim w → (0 : Vertex d) ≠ w := by
    rintro w ⟨-, k, hk⟩ rfl
    simp at hk
  have hnb : ∀ w : Vertex d, IsRim w → LatticeProb.unit i + LatticeProb.unit j ≠ w := by
    rintro w ⟨-, k, hk⟩ rfl
    have := abs_unit_add_unit_le_one hij k
    linarith
  refine (setGadget_adj_iff_of_mem hu.1 hv.1).mpr ⟨h, Or.inl ⟨?_, ?_⟩⟩
  · rintro (h0 | h0)
    · exact hn0 u hu h0
    · exact hn0 v hv h0
  · rintro (h0 | h0)
    · exact hnb u hu h0
    · exact hnb v hv h0

/-- Moving one coordinate along a segment of sites of `S`, all of whose lattice bonds are edges
of `G`. -/
theorem reachable_segment {G : SimpleGraph (Vertex d)} {S : Set (Vertex d)}
    (hS : ∀ u v, u ∈ S → v ∈ S → (nearestNeighborGraph d).Adj u v → G.Adj u v)
    (v : Vertex d) (k : Fin d) (s : ℤ) (n : ℕ)
    (hmem : ∀ r, s ≤ r → r ≤ s + n → Function.update v k r ∈ S) :
    G.Reachable (Function.update v k s) (Function.update v k (s + n)) := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, add_zero]
    try exact SimpleGraph.Reachable.refl _
  | succ n ih =>
    have h1 := ih fun r h1 h2 => hmem r h1 (by push_cast; omega)
    refine h1.trans (SimpleGraph.Adj.reachable (hS _ _ (hmem _ (by omega) (by push_cast; omega))
      (hmem _ (by omega) le_rfl) ⟨k, Or.inl ?_⟩))
    funext l
    by_cases hl : l = k
    · subst hl
      simp only [Function.update_self, Pi.add_apply, unit_apply, if_true]
      push_cast
      ring
    · simp [unit_apply, hl]

theorem reachable_segment' {G : SimpleGraph (Vertex d)} {S : Set (Vertex d)}
    (hS : ∀ u v, u ∈ S → v ∈ S → (nearestNeighborGraph d).Adj u v → G.Adj u v)
    (v : Vertex d) (k : Fin d) (s t : ℤ)
    (hmem : ∀ r, min s t ≤ r → r ≤ max s t → Function.update v k r ∈ S) :
    G.Reachable (Function.update v k s) (Function.update v k t) := by
  rcases le_total s t with h | h
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, t = s + n := ⟨(t - s).toNat, by omega⟩
    subst hn
    exact reachable_segment hS v k s n fun r h1 h2 => hmem r (by omega) (by omega)
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, s = t + n := ⟨(s - t).toNat, by omega⟩
    subst hn
    exact (reachable_segment hS v k t n fun r h1 h2 => hmem r (by omega) (by omega)).symm

/-- Every site of the boundary of `Q_2` is joined to `e_i` in the reset configuration. -/
theorem reachable_unit_of_rim {i j : Fin d} (hij : i ≠ j) (ω : Configuration d) {u : Vertex d}
    (hu : IsRim u) : (openGraph (setGadget i j ω)).Reachable (LatticeProb.unit i) u := by
  set G := openGraph (setGadget i j ω)
  have hS : ∀ u v, u ∈ {w | IsRim w} → v ∈ {w | IsRim w} →
      (nearestNeighborGraph d).Adj u v → G.Adj u v :=
    fun u v hu hv h => setGadget_adj_of_rim hij ω hu hv h
  set t₀ : Vertex d := LatticeProb.unit i + LatticeProb.unit i
  have ht₀ : ∀ l, t₀ l = if l = i then 2 else 0 := fun l => by
    simp only [t₀, Pi.add_apply, unit_apply]
    split_ifs <;> norm_num
  have hupd : ∀ (w : Vertex d) (l : Fin d) (r : ℤ) (k : Fin d),
      Function.update w l r k = if k = l then r else w k := fun w l r k => by
    by_cases hk : k = l
    · subst hk
      simp
    · simp [hk]
  have ht₀b : ∀ l, 0 ≤ t₀ l ∧ t₀ l ≤ 2 := fun l => by
    rw [ht₀]
    split_ifs <;> norm_num
  -- (L1) a site of `Q_2` with `u_i = 2` is joined to `t₀` through sites with `u_i = 2`
  have L1 : ∀ (s : Finset (Fin d)) (w : Vertex d), w ∈ cube d 2 → w i = 2 →
      (∀ l ∉ s, w l = t₀ l) → G.Reachable w t₀ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro w _ _ hl
      rw [show w = t₀ from funext fun l => hl l (Finset.notMem_empty l)]
    | @insert l s hls ih =>
      intro w hw hwi hl
      set w' := Function.update w l (t₀ l)
      have hw' : w' ∈ cube d 2 := by
        rw [mem_cube_two_iff]
        intro k
        simp only [w', hupd]
        split_ifs
        · have := ht₀b l
          rw [abs_le]
          constructor <;> omega
        · exact mem_cube_two_iff.mp hw k
      have hw'i : w' i = 2 := by
        simp only [w', hupd]
        split_ifs with h
        · rw [ht₀, if_pos h.symm]
        · exact hwi
      have hl' : ∀ l' ∉ s, w' l' = t₀ l' := by
        intro l' hl's
        simp only [w', hupd]
        split_ifs with h
        · rw [h]
        · exact hl l' (by simp [h, hl's])
      refine (?_ : G.Reachable w w').trans (ih w' hw' hw'i hl')
      have := reachable_segment' hS w l (w l) (t₀ l) fun r h1 h2 => by
        change IsRim _
        refine ⟨mem_cube_two_iff.mpr fun k => ?_, i, ?_⟩
        · rw [hupd]
          split_ifs
          · have h3 := abs_le.mp (mem_cube_two_iff.mp hw l)
            have h4 := ht₀b l
            rw [abs_le]
            constructor <;> omega
          · exact mem_cube_two_iff.mp hw k
        · rw [hupd]
          split_ifs with h
          · have hwl : w l = 2 := h ▸ hwi
            have htl : t₀ l = 2 := by rw [ht₀, if_pos h.symm]
            rw [show r = 2 by omega]
            norm_num
          · rw [hwi]
            norm_num
      rwa [Function.update_eq_self] at this
  -- (L2) a site of `Q_2` with `|u_k| = 2` for some `k ≠ i`
  have L2 : ∀ w : Vertex d, w ∈ cube d 2 → ∀ k, k ≠ i → |w k| = 2 → G.Reachable w t₀ := by
    intro w hw k hki hwk
    have := reachable_segment' hS w i (w i) 2 fun r h1 h2 => by
      change IsRim _
      refine ⟨mem_cube_two_iff.mpr fun l => ?_, k, ?_⟩
      · rw [hupd]
        split_ifs
        · have h3 := abs_le.mp (mem_cube_two_iff.mp hw i)
          rw [abs_le]
          constructor <;> omega
        · exact mem_cube_two_iff.mp hw l
      · rw [hupd, if_neg hki, hwk]
    rw [Function.update_eq_self] at this
    refine this.trans (L1 Finset.univ _ ?_ (by simp) (fun l hl => absurd (Finset.mem_univ l) hl))
    rw [mem_cube_two_iff]
    intro l
    rw [hupd]
    split_ifs
    · norm_num
    · exact mem_cube_two_iff.mp hw l
  -- (L3) a site of `Q_2` with `|u_i| = 2`
  have L3 : ∀ w : Vertex d, w ∈ cube d 2 → |w i| = 2 → G.Reachable w t₀ := by
    intro w hw hwi
    rcases (abs_eq (by norm_num : (0 : ℤ) ≤ 2)).mp hwi with h | h
    · exact L1 Finset.univ w hw h (fun l hl => absurd (Finset.mem_univ l) hl)
    · have := reachable_segment' hS w j (w j) 2 fun r h1 h2 => by
        change IsRim _
        refine ⟨mem_cube_two_iff.mpr fun l => ?_, i, ?_⟩
        · rw [hupd]
          split_ifs
          · have h3 := abs_le.mp (mem_cube_two_iff.mp hw j)
            rw [abs_le]
            constructor <;> omega
          · exact mem_cube_two_iff.mp hw l
        · rw [hupd, if_neg hij, h]
          norm_num
      rw [Function.update_eq_self] at this
      refine this.trans (L2 _ ?_ j (Ne.symm hij) (by simp))
      rw [mem_cube_two_iff]
      intro l
      rw [hupd]
      split_ifs
      · norm_num
      · exact mem_cube_two_iff.mp hw l
  have hut : G.Reachable u t₀ := by
    obtain ⟨huc, k, hk⟩ := hu
    by_cases hki : k = i
    · subst hki
      exact L3 u huc hk
    · exact L2 u huc k hki hk
  have hit : G.Adj (LatticeProb.unit i) t₀ := by
    have hic : (LatticeProb.unit i : Vertex d) ∈ cube d 2 := fun k => by
      rw [unit_apply]
      split_ifs <;> norm_num
    have htc : t₀ ∈ cube d 2 := fun k => by
      rw [ht₀]
      split_ifs <;> norm_num
    exact (setGadget_adj_iff_of_mem hic htc).mpr ⟨⟨i, Or.inl rfl⟩, Or.inr (Or.inl (Or.inl rfl))⟩
  exact hit.reachable.trans hut.symm

/-- The last exit from `Q_2`: an open walk of `ω` ending outside `Q_2` either stays outside `Q_2`
or, after its last visit to `Q_2` (at a boundary site), is an open walk of the reset
configuration. -/
theorem rim_reachable_of_walk {i j : Fin d} {ω : Configuration d} {w z : Vertex d}
    (W : (openGraph ω).Walk w z) (hz : z ∉ cube d 2) :
    (w ∉ cube d 2 ∧ (openGraph (setGadget i j ω)).Reachable w z) ∨
      ∃ u, IsRim u ∧ (openGraph (setGadget i j ω)).Reachable u z := by
  induction W with
  | nil => exact Or.inl ⟨hz, SimpleGraph.Reachable.refl _⟩
  | @cons w v z hadj W' ih =>
    rcases ih hz with ⟨hv, hvz⟩ | h
    · have hadj' : (openGraph (setGadget i j ω)).Adj w v :=
        (setGadget_adj_iff_of_not_mem (Or.inr hv)).mpr hadj
      by_cases hw : w ∈ cube d 2
      · refine Or.inr ⟨w, ⟨hw, ?_⟩, hadj'.reachable.trans hvz⟩
        obtain ⟨k, hk⟩ : ∃ k, ¬ |v k| ≤ 2 := by
          by_contra hcon
          push Not at hcon
          exact hv fun k => by exact_mod_cast hcon k
        refine ⟨k, le_antisymm (by exact_mod_cast hw k) ?_⟩
        have h1 := abs_sub_le_one_of_adj hadj k
        have h2 := abs_sub_abs_le_abs_sub (v k) (w k)
        omega
      · exact Or.inl ⟨hw, hadj'.reachable.trans hvz⟩
    · exact Or.inr h

/-- Resetting the bonds of `Q_2` maps the event that the origin lies in an infinite open cluster
into the gadget event. -/
theorem setGadget_mem_gadgetEvent {i j : Fin d} (hij : i ≠ j) {ω : Configuration d}
    (hω : ω ∈ infiniteComponentEvent 0) : setGadget i j ω ∈ gadgetEvent i j := by
  refine ⟨gadgetAt_setGadget hij ω, (mem_infiniteComponentEvent_iff _ _).mpr fun s => ?_⟩
  obtain ⟨y, hy, h0y⟩ := (mem_infiniteComponentEvent_iff ω 0).mp hω (s ∪ Steps.S6.cubeFinset d 2)
  have hys : y ∉ s := fun h => hy (Finset.mem_union_left _ h)
  have hyc : y ∉ cube d 2 := fun h =>
    hy (Finset.mem_union_right _ (Steps.S6.mem_cubeFinset.mpr h))
  obtain ⟨W⟩ := h0y
  rcases rim_reachable_of_walk (i := i) (j := j) W hyc with ⟨h0, -⟩ | ⟨u, hu, huy⟩
  · exact absurd (fun k => by simp) h0
  · exact ⟨y, hys, (reachable_unit_of_rim hij ω hu).trans huy⟩

/-- Finite energy: the gadget event has positive probability. -/
theorem measure_gadgetEvent_ne_zero [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hwc : WellConnectedInput)
    {i j : Fin d} (hij : i ≠ j) : latticeBondLaw d p (gadgetEvent i j) ≠ 0 := by
  have hp0 : 0 < (p : ℝ) := lt_of_le_of_lt (criticalProbability_nonneg d) hpc
  intro h0
  apply measure_infiniteComponentEvent_ne_zero hd p hpc hp1 hwc
  have hcover : infiniteComponentEvent 0 ⊆ ⋃ T ∈ (insideBonds d 2).powerset,
      LatticeProb.BernoulliFiniteFlip.flip T ⁻¹' gadgetEvent i j := by
    intro ω hω
    refine Set.mem_biUnion (x := (insideBonds d 2).filter fun e => ω e ≠ gadgetPattern i j e)
      (Finset.mem_coe.mpr (Finset.mem_powerset.mpr (Finset.filter_subset _ _))) ?_
    exact setGadget_mem_gadgetEvent hij hω
  refine measure_mono_null hcover (nonpos_iff_eq_zero.mp ((measure_biUnion_finset_le _ _).trans
    (Finset.sum_eq_zero fun T _ => ?_).le))
  exact (LatticeProb.BernoulliFiniteFlip.full_product_flip_null_iff p hp0 hp1 T
    (measurableSet_gadgetEvent i j)).mpr h0

end GadgetCount

open GadgetCount SingleExit in
/-- `GadgetCountStep` (step:6.5-gadget-count, paper L2962-2964): almost surely, for every large
`n`, every admissible largest open cluster `V` of `Q_n` contains at least `c n^d` gadget sites.
Inputs: Proposition 2.3 (`WellConnectedInput`), `p_c < p < 1`, and the multiparameter ergodic
theorem (`Rigidity.Proofs.Ergodic.translateDensity`). -/
theorem gadgetCountStep {d : ℕ} [NeZero d] (hd : 2 ≤ d) (p : unitInterval)
    (hpc : criticalProbability d < (p : ℝ)) (hp1 : (p : ℝ) < 1) (hwc : WellConnectedInput) :
    Steps.S6.GadgetCountStep d p := by
  obtain ⟨i, j, hij⟩ : ∃ i j : Fin d, i ≠ j := by
    refine ⟨0, ⟨1, by omega⟩, fun h => ?_⟩
    have := congrArg Fin.val h
    simp at this
  set μ := latticeBondLaw d p
  set G := gadgetEvent (d := d) i j
  set q := (μ G).toReal with hqdef
  have hq : 0 < q := ENNReal.toReal_pos (measure_gadgetEvent_ne_zero hd p hpc hp1 hwc hij)
    (measure_ne_top _ _)
  set qq := 100 * d ^ 2 with hqqdef
  have hqq : qq ≠ 0 := by positivity
  have hex : ∀ n : ℕ, ∃ m, n ≤ m ^ qq := fun n => ⟨n, Nat.le_self_pow hqq n⟩
  let mOf : ℕ → ℕ := fun n => Nat.find (hex n)
  have hscale : ∀ n, 22 ^ qq ≤ n → 1 ≤ mOf n ∧ 20 * mOf n ≤ n ∧
      (2 * mOf n + 1) ^ d < (2 * (n - 2 * mOf n) + 1) / (2 * mOf n + 1) ∧
      (n : ℝ) ^ ((qq : ℝ)⁻¹) ≤ mOf n := by
    intro n hn
    have hspec : n ≤ mOf n ^ qq := Nat.find_spec (hex n)
    have h22 : 22 ≤ mOf n := by
      by_contra h
      push Not at h
      exact absurd (hn.trans hspec) (not_le.mpr (Nat.pow_lt_pow_left h hqq))
    have hlow : (mOf n - 1) ^ qq < n := by
      have := Nat.find_min (hex n) (show mOf n - 1 < mOf n by omega)
      push Not at this
      exact this
    obtain ⟨h20, hK⟩ := scale_conditions hd hqqdef h22 hlow
    refine ⟨by omega, h20, hK, ?_⟩
    calc (n : ℝ) ^ ((qq : ℝ)⁻¹) ≤ ((mOf n : ℝ) ^ qq) ^ ((qq : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast hspec) (by positivity)
      _ = mOf n := Real.pow_rpow_inv_natCast (by positivity) hqq
  have hδ : (1 / (10 * (d : ℝ)) ^ 2) = (qq : ℝ)⁻¹ := by
    rw [hqqdef]; push_cast; ring
  refine ⟨q / 2, by positivity, ?_⟩
  filter_upwards [Ergodic.translateDensity p G (measurableSet_gadgetEvent i j).nullMeasurableSet,
    ae_eventually_isWellConnected hd p hpc hp1 hwc] with ω hT hW
  intro _
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp (hT.eventually_const_le (by linarith : q / 2 < q))
  filter_upwards [hW, eventually_ge_atTop (22 ^ qq), eventually_ge_atTop (2 * N₁ + 1)]
    with n hWn hn hn1
  intro V hV
  obtain ⟨hm1, h20, hK, hnm⟩ := hscale n hn
  set m := mOf n
  set N := n - 2 * m - 1 with hNdef
  have hNz : (N : ℤ) = n - 2 * m - 1 := by omega
  have hg : CubesGood ω n m := by
    intro z hz
    have hmem : ∀ M : ℕ, (cubeAt z M ∩ cubeAt 0 n).Nonempty := fun M =>
      ⟨z, fun i => by simp, fun i => by simpa using hz i⟩
    have h20' : (20 : ℝ) * m ≤ n := by exact_mod_cast h20
    have hpos : 0 ≤ (n : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) := by positivity
    have hlo : (n : ℝ) ^ (1 / (10 * (d : ℝ)) ^ 2) ≤ m := by rw [hδ]; exact hnm
    exact ⟨hWn.2.2 z _ (by linarith) (by linarith) (hmem _),
      hWn.2.2 z _ (by push_cast; linarith) (by push_cast; linarith) (hmem _)⟩
  set S := {y : Vertex d | configurationTranslation y ω ∈ G}
  have hsite : ∀ y ∈ (Steps.S4.symmetricBox d N).filter (· ∈ S),
      -y ∈ Steps.S6.gadgetSites ω V := by
    intro y hy
    obtain ⟨hyB, hyG⟩ := Finset.mem_filter.mp hy
    have hyb : ∀ k, |y k| ≤ (N : ℤ) := fun k => by
      have := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hyB k)
      rw [abs_le]
      exact ⟨this.1, this.2⟩
    obtain ⟨hgad, hinf⟩ := hyG
    have hgad' : GadgetAt ω i j (-y) := by
      have := (gadgetAt_translation_iff y ω i j (-y)).mp
      rw [neg_add_cancel] at this
      exact this hgad
    have hinf' : ω ∈ infiniteComponentEvent (-y + LatticeProb.unit i) := by
      have := (infiniteComponentEvent_translation_iff y ω (LatticeProb.unit i)).mp hinf
      rwa [show LatticeProb.unit i - y = -y + LatticeProb.unit i by abel] at this
    have hx : ω ∈ infiniteComponentEvent (-y) :=
      mem_infiniteComponentEvent_of_reachable ((hgad'.1 _).mpr (Or.inl rfl)).reachable hinf'
    have hb : ω ∈ infiniteComponentEvent (-y + LatticeProb.unit i + LatticeProb.unit j) :=
      mem_infiniteComponentEvent_of_reachable ((hgad'.2 _).mpr (Or.inl rfl)).reachable hinf'
    have hbound : ∀ k, |(-y) k| ≤ (n : ℤ) - 2 * m := fun k => by
      rw [Pi.neg_apply, abs_neg]
      linarith [hyb k]
    have hbound' : ∀ k,
        |(-y + LatticeProb.unit i + LatticeProb.unit j) k| ≤ (n : ℤ) - 2 * m := by
      intro k
      have h1 := abs_unit_add_unit_le_one hij k
      have h2 := abs_add_le (-y k) ((LatticeProb.unit i + LatticeProb.unit j : Vertex d) k)
      have h3 : (-y + LatticeProb.unit i + LatticeProb.unit j) k =
          -y k + (LatticeProb.unit i + LatticeProb.unit j : Vertex d) k := by
        simp only [Pi.add_apply, Pi.neg_apply]
        ring
      have h4 : |-y k| ≤ N := by rw [abs_neg]; exact hyb k
      rw [h3]
      linarith
    have hxV := mem_of_mem_infiniteComponentEvent hd hg hm1 (by omega) hK hV.1 hbound hx
    have hbV := mem_of_mem_infiniteComponentEvent hd hg hm1 (by omega) hK hV.1 hbound' hb
    exact Finset.mem_filter.mpr ⟨hxV, _, hbV, isGadgetPair_of_gadgetAt hij hgad'⟩
  have hcount : (((Steps.S4.symmetricBox d N).filter (· ∈ S)).card : ℝ) ≤
      (Steps.S6.gadgetSites ω V).card := by
    exact_mod_cast Finset.card_le_card_of_injOn (fun y => -y) (fun y hy => hsite y hy)
      (fun y _ y' _ h => neg_injective h)
  have hcardpos : (0 : ℝ) < (Steps.S4.symmetricBox d N).card := by
    rw [Ergodic.card_symmetricBox]
    positivity
  have hsum : ∑ y ∈ Steps.S4.symmetricBox d N, S.indicator (fun _ => (1 : ℝ)) y =
      (((Steps.S4.symmetricBox d N).filter (· ∈ S)).card : ℝ) := by
    rw [Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun y _ => ?_
    simp [Set.indicator_apply]
  have hdens : q / 2 * (2 * N + 1 : ℝ) ^ d ≤
      (((Steps.S4.symmetricBox d N).filter (· ∈ S)).card : ℝ) := by
    have := hN₁ N (by omega)
    rw [Steps.S4.boxDensity, hsum, le_div_iff₀ hcardpos, Ergodic.card_symmetricBox] at this
    exact this
  have hnN : (n : ℝ) ≤ 2 * N + 1 := by exact_mod_cast (show n ≤ 2 * N + 1 by omega)
  calc q / 2 * (n : ℝ) ^ d ≤ q / 2 * (2 * N + 1 : ℝ) ^ d := by gcongr
    _ ≤ _ := hdens
    _ ≤ _ := hcount

end Rigidity.Proofs.S6
