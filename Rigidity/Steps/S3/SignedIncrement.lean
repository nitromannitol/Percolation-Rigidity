import Rigidity.Steps.S3.HorizontalIncrement
import Rigidity.Steps.S4.NonConstantOnGadgetJoint
import Rigidity.Steps.S3.SignedIncrementData

/-!
# The signed variant of Proposition 3.2 by local surgery

**A proof of the directional step of the printed Lemma 5.25.** The printed third good event `G_3(0, C_χ)` of
Lemma 5.25 (L2365-2370) lies on the edge `(0, e₁)` (`eventG3Edge`), and its positive probability
is the step of the printed proof that Proposition 3.2 "and symmetry arguments" does not give
(gap G5): it needs the signed variant `HorizontalIncrementStep`
(`Rigidity/Proofs/Section5/ThirdGoodEvent.lean`), a large increment `ℓ_{e₁}(e₁) - ℓ_{e₁}(0)` of a
fixed sign across the edge `(0, e₁)` of `𝒞_∞`. This file proves it for `p_c(2) < p < 1`
(`horizontalIncrementStep_of_exteriorNetwork_inputs`) from Proposition 3.2 as printed (the
direction-free statement `NotLipschitzStmt`) by a local surgery in a fixed finite region, with one
new ingredient, the exterior network of the region (`ExteriorNetworkStep`), proved from the
literature inputs in `Rigidity/Proofs/S3/ExteriorNetwork.lean` (`exteriorNetworkStep`). The
argument of `thirdGoodEventStep_of_horizontalIncrement` then gives, for every `C_χ ≥ 1`, a
measurable event of positive probability inside `eventG3Edge 0 C_χ`. The draft `G_3(x, C_χ)` is direction-free ([C32]); `eventG3Edge`
implies it (`eventG3Edge_subset`), and the direction-free form also follows from Proposition 3.2
directly (`Rigidity/Proofs/Section5/ThirdGoodEventDirectionFree.lean`). The slit route of
Proposition 3.2 does not give the signed variant (`Rigidity/Steps/S3/HorizontalIncrement.lean`).

## The route

Fix a finite set `U` of sites (`U = Q_2` minus its four corners) and let `E` be the bonds meeting
`U`; the terminals `T` are the sites outside `U` adjacent to `U`. Changing the bonds of `E` does
not change the exterior, the cluster made of the other bonds.

* **Exterior network** (new ingredient, `ExteriorNetworkStep`). Almost surely there are
  conductances `c_{ts} = c_{st} ≥ 0` on `T × T` with `∑_s c_{ts} ≤ 4`, and potentials `ℓ⁰` on `T`
  (the corrected plane of the environment with every bond of `E` closed), such that for every way
  of setting the bonds of `E`, every corrected plane `ℓ` of the new infinite cluster receives at
  each terminal `t` of the cluster the exterior current
  `∑_{x ∉ U, tx open} (ℓ(x) - ℓ(t)) = ∑_s c_{ts} ((ℓ(s) - ℓ(t)) - (ℓ⁰(s) - ℓ⁰(t)))`.
  The exterior is a finite network on `T` whose branch `ts` carries the electromotive force
  `ℓ⁰(t) - ℓ⁰(s)`. (Proof, `Rigidity/Proofs/S3/ExteriorNetwork.lean`: `ℓ - ℓ⁰` is harmonic off
  `T` on the exterior infinite component, of slope zero, with zero total flux through `T`; by the
  Liouville property it is a constant plus a zero-sum combination of Green columns at the
  terminals, with the asymptotics of Dario and Gu, and `c` is the trace of the exterior on `T`.)
* **Reciprocity bound** (finite network, elementary). With the original bonds of `E`, the current
  across an open bond `xy` of `E` is at most `∑_{t<s} c_{ts} |ℓ⁰(s) - ℓ⁰(t)|`: the outward flux of
  the super-level set `{ℓ ≥ ℓ(y)}` of the finite network is at least `ℓ(y) - ℓ(x)` (every boundary
  current is outward) and equals the total source `-∑ b_t` it contains, with
  `b_t = ∑_s c_{ts} (ℓ⁰(s) - ℓ⁰(t))`.
* **Path designs** (finite network, elementary). Open in `E` exactly the bonds of a self-avoiding
  path `π` of length `m` from a terminal `z` through `U` to a terminal `w`. Along `π` the increment
  `D` is constant; with `v = ℓ - ℓ⁰` on `T`, the energy identity `D (v_w - v_z) = -∑ c (Δv)²` and
  `v_w - v_z = m D - (ℓ⁰(w) - ℓ⁰(z))` give `c_{zw} |ℓ⁰(w) - ℓ⁰(z)| ≤ (c_{zw} m + 1) |D|`. If `π`
  crosses one horizontal bond to the right and one to the left, one of them has
  `ℓ(a + e₁) - ℓ(a) = |D|`. In `Q_2` minus its corners every pair of terminals is joined by such a
  path (in the full square `Q_R` the two terminals next to a corner share their only entry site, and
  the path between them is forced to cross a single horizontal bond in a fixed direction).
* **Conclusion** (`LocalSurgeryStep`): almost surely, `|∇ℓ_{e₁}(0)| > K L` forces a rise of more
  than `L` across the designated bond of some path design, with `K = 2 · #pairs · (4 m + 1)`.
* **Status.** `localSurgeryStep_of_steps` (proved) derives `LocalSurgeryStep` from
  `ExteriorNetworkStep` and `ModifiedPlaneStep`, with `K = 30000`: the reciprocity bound is
  `originGradientNorm_le_of_network`, the path design bound `pair_bound_of_design`, and the 120
  designs are checked by `decide +kernel` (`designs_good`, `designs_cover`) in the leaf module
  `Rigidity/Steps/S3/SignedIncrementData.lean`.
  `horizontalIncrementStep_of_exteriorNetwork` is the end-to-end reduction:
  `NotLipschitzStmt 2 p`, `ExteriorNetworkStep p` and `ModifiedPlaneStep p` give
  `HorizontalIncrementStep p` for `0 < p < 1`. `modifiedPlaneStep` (proved) derives
  `ModifiedPlaneStep` from the literature inputs `SupercriticalBondUniqueness` and
  `SupercriticalBondCorrectorInput`, so `horizontalIncrementStep_of_exteriorNetwork_inputs` takes
  `ExteriorNetworkStep p` as its one step hypothesis. `Rigidity.Proofs.S3.exteriorNetworkStep`
  (`Rigidity/Proofs/S3/ExteriorNetwork.lean`, which imports this file) proves it from the
  literature inputs `SupercriticalBondUniqueness`, `SupercriticalBondCorrectorInput`,
  `ArmstrongDarioOrderZero`, `SupercriticalBondGreenColumnExistence` and
  `SupercriticalBondGreenQuantitative`.
* **Probability** (`horizontalIncrementStep_of_localSurgery`, proved here). If the rise event at
  the origin were null, by stationarity and finite energy (`Rigidity.Steps.S4.finiteEnergyStep`,
  proved) so would be every rise event of every design, hence `|∇ℓ_{e₁}(0)| > K L` would be null,
  contradicting Proposition 3.2.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory LatticeProb LatticeProb.Percolation

namespace Rigidity.Steps.S3

open Rigidity.Section5 Rigidity.Proofs.Section5

/-! ### Events and local modifications -/

/-- The rise event at `a`: the bond `(a, a + e₁)` is an edge of the unique infinite cluster across
which some corrected plane `ℓ_{e₁}` increases by more than `L`. -/
def riseEvent (a : Vertex 2) (L : ℝ) : Set (Configuration 2) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∃ ha : a ∈ (uniqueInfiniteComponent h).supp,
    ∃ hb : a + e1 ∈ (uniqueInfiniteComponent h).supp,
      (componentGraph _).Adj ⟨a, ha⟩ ⟨a + e1, hb⟩ ∧
      ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) u ∧
        L < u ⟨a + e1, hb⟩ - u ⟨a, ha⟩}

/-- The large-gradient event of Proposition 3.2: some corrected plane `ℓ_{e₁}` has
`|∇ℓ_{e₁}(0)| > L` at the origin of the unique infinite cluster. -/
def gradientEvent (L : ℝ) : Set (Configuration 2) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∃ ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp,
    ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (Rigidity.Section3.slopeE1 2) u ∧
      L < Rigidity.Section3.originGradientNorm (uniqueInfiniteComponent h) ho u}

/-- A bond meets the set of sites `U`. -/
def MeetsSites (U : Set (Vertex 2)) (e : Bond 2) : Prop :=
  ∃ z ∈ (e : Sym2 (Vertex 2)), z ∈ U

open scoped Classical in
/-- The environment `ω` in which the bonds meeting `U` are open exactly on `F`. -/
noncomputable def modifyNear (U : Set (Vertex 2)) (F : Set (Bond 2)) (ω : Configuration 2) :
    Configuration 2 :=
  fun e => if MeetsSites U e then decide (e ∈ F) else ω e

/-- The rise event moves with the environment. -/
theorem riseEvent_translation (z : Vertex 2) {a : Vertex 2} {L : ℝ} {ω : Configuration 2}
    (hω : ω ∈ riseEvent a L) : configurationTranslation z ω ∈ riseEvent (a + z) L := by
  obtain ⟨h, ha, hb, hadj, u, hu, hlt⟩ := hω
  have h' := (hasUniqueInfiniteOpenComponent_translation_iff z ω).mpr h
  have hC : openComponentTranslation z ω (uniqueInfiniteComponent h) =
      uniqueInfiniteComponent h' := openComponentTranslation_uniqueInfiniteComponent z h
  refine ⟨h', ?_⟩
  rw [← hC]
  have haz : a + z ∈ (openComponentTranslation z ω (uniqueInfiniteComponent h)).supp :=
    (add_mem_openComponentTranslation_supp z _ a).mpr ha
  have hbz' : a + e1 + z ∈ (openComponentTranslation z ω (uniqueInfiniteComponent h)).supp :=
    (add_mem_openComponentTranslation_supp z _ (a + e1)).mpr hb
  have hbz : a + z + e1 ∈ (openComponentTranslation z ω (uniqueInfiniteComponent h)).supp := by
    rwa [add_right_comm]
  have e0 : (⟨a + z, haz⟩ : openComponentTranslation z ω (uniqueInfiniteComponent h)) =
      openComponentTranslationIso z _ ⟨a, ha⟩ := rfl
  have e0' : (⟨a + z + e1, hbz⟩ : openComponentTranslation z ω (uniqueInfiniteComponent h)) =
      openComponentTranslationIso z _ ⟨a + e1, hb⟩ :=
    Subtype.ext (show a + z + e1 = a + e1 + z by abel)
  refine ⟨haz, hbz, ?_, fun v => u ((openComponentTranslationIso z _).symm v),
    (isCorrectedPlane_translation_iff z _ _ u).mpr hu, ?_⟩
  · rw [e0, e0']
    exact (openComponentTranslationIso z _).map_adj_iff.mpr hadj
  · rw [e0, e0']
    simpa only [RelIso.symm_apply_apply] using hlt

/-- The rise event at the origin is the event of `HorizontalIncrementStep`. -/
theorem riseEvent_zero_subset (L : ℝ) :
    riseEvent 0 L ⊆ {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
      ∃ ho : (0 : Vertex 2) ∈ (uniqueInfiniteComponent h).supp,
      ∃ he : e1 ∈ (uniqueInfiniteComponent h).supp,
        (componentGraph _).Adj ⟨0, ho⟩ ⟨e1, he⟩ ∧
        ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) u ∧
          L < u ⟨e1, he⟩ - u ⟨0, ho⟩} := by
  rintro ω ⟨h, ha, hb, hadj, u, hu, hlt⟩
  have he : e1 ∈ (uniqueInfiniteComponent h).supp := by simpa only [zero_add] using hb
  have hsub : (⟨0 + e1, hb⟩ : uniqueInfiniteComponent h) = ⟨e1, he⟩ :=
    Subtype.ext (zero_add e1)
  exact ⟨h, ha, he, hsub ▸ hadj, u, hu, hsub ▸ hlt⟩

/-- **Finite energy** for local modifications (Lemma 2.1): for `0 < p < 1`, if `U` lies in a cube
`Q_R` (every bond meeting `U` meets `Q_R`), then setting the bonds meeting `U` to any prescribed
values maps null events to null events. From `Rigidity.Steps.S4.finiteEnergyStep`: the
modification is `attachConfig R G` for one of the finitely many sets `G` of bonds meeting `Q_R`. -/
theorem modifyNear_preimage_null {p : unitInterval} (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {R : ℕ} {U : Set (Vertex 2)}
    (hU : ∀ e, MeetsSites U e → e ∈ Rigidity.Steps.S4.bondsNear 2 R)
    (F : Set (Bond 2)) {S : Set (Configuration 2)} (hS : latticeBondLaw 2 p S = 0) :
    latticeBondLaw 2 p (modifyNear U F ⁻¹' S) = 0 := by
  classical
  set B := Rigidity.Steps.S4.bondsNear 2 R
  have hfin : B.Finite := Rigidity.Steps.S4.finite_bondsNear 2 R
  have hm : 0 < min (p : ℝ) (1 - p) := lt_min hp0 (by linarith)
  -- each attached environment maps `S` to a null event
  have hnull : ∀ G : Set (Bond 2),
      latticeBondLaw 2 p (Rigidity.Steps.S4.attachConfig R G ⁻¹' S) = 0 := by
    intro G
    have h := Rigidity.Steps.S4.finiteEnergyStep (d := 2) p R G S
    rw [hS, ENNReal.toReal_zero] at h
    have h2 : (latticeBondLaw 2 p (Rigidity.Steps.S4.attachConfig R G ⁻¹' S)).toReal = 0 :=
      le_antisymm (by
        have hpow : 0 < min (p : ℝ) (1 - p) ^ B.ncard := pow_pos hm _
        nlinarith [ENNReal.toReal_nonneg
          (a := latticeBondLaw 2 p (Rigidity.Steps.S4.attachConfig R G ⁻¹' S))])
        ENNReal.toReal_nonneg
    rcases (ENNReal.toReal_eq_zero_iff _).1 h2 with h0 | htop
    · exact h0
    · exact absurd htop (measure_ne_top _ _)
  -- the modified environment is an attached environment
  let G : Configuration 2 → Set (Bond 2) := fun ω =>
    {e | e ∈ B ∧ (if MeetsSites U e then e ∈ F else ω e = true)}
  have hG : ∀ ω, modifyNear U F ω = Rigidity.Steps.S4.attachConfig R (G ω) ω := by
    intro ω
    funext e
    by_cases hB : e ∈ B
    · by_cases hUe : MeetsSites U e
      · simp [modifyNear, Rigidity.Steps.S4.attachConfig, G, hB, hUe, B]
      · simp only [modifyNear, Rigidity.Steps.S4.attachConfig, G, hUe, if_false]
        rw [if_pos hB]
        simp [hB, hUe]
    · have hUe : ¬ MeetsSites U e := fun h => hB (hU e h)
      simp [modifyNear, Rigidity.Steps.S4.attachConfig, hUe, hB, B]
  have hsub : modifyNear U F ⁻¹' S ⊆
      ⋃ G' ∈ B.powerset, Rigidity.Steps.S4.attachConfig R G' ⁻¹' S := by
    intro ω hω
    refine Set.mem_iUnion₂.2 ⟨G ω, fun e he => he.1, ?_⟩
    rw [Set.mem_preimage, ← hG]
    exact hω
  refine measure_mono_null hsub ((measure_biUnion_null_iff ?_).2 fun G' _ => hnull G')
  exact (hfin.powerset).countable

/-! ### Finite networks with sources -/

/-- **Super-level-set bound.** In a finite network `W` with symmetric nonnegative conductances `k`
and Kirchhoff's law `∑_w k v w (f w - f v) = b v` at every `v ∈ W`, the increment of `f` across a
bond of conductance at least one is at most the total source `∑_v |b v|`: the outward flux of the
super-level set `{f ≥ f y}` is at least `f y - f x` (every boundary current is outward) and equals
minus the total source it contains. -/
theorem sub_le_sum_abs_of_kirchhoff {ι : Type*} [DecidableEq ι] (W : Finset ι)
    (k : ι → ι → ℝ) (f b : ι → ℝ) (hk : ∀ v w, k v w = k w v) (hk0 : ∀ v w, 0 ≤ k v w)
    (hkcl : ∀ v ∈ W, ∑ w ∈ W, k v w * (f w - f v) = b v)
    {x y : ι} (hx : x ∈ W) (hy : y ∈ W) (hxy : 1 ≤ k y x) :
    f y - f x ≤ ∑ v ∈ W, |b v| := by
  by_cases hle : f y ≤ f x
  · have : 0 ≤ ∑ v ∈ W, |b v| := Finset.sum_nonneg fun v _ => abs_nonneg _
    linarith
  push Not at hle
  set A := W.filter fun v => f y ≤ f v with hA
  have hAW : A ⊆ W := Finset.filter_subset _ _
  have hyA : y ∈ A := Finset.mem_filter.2 ⟨hy, le_rfl⟩
  have hxA : x ∉ A := fun h => by have := (Finset.mem_filter.1 h).2; linarith
  -- the currents inside `A` cancel
  have hint : ∑ v ∈ A, ∑ w ∈ A, k v w * (f w - f v) = 0 := by
    have h1 : ∑ v ∈ A, ∑ w ∈ A, k v w * (f w - f v) =
        ∑ v ∈ A, ∑ w ∈ A, k v w * (f v - f w) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
      rw [hk]
    have h2 : ∑ v ∈ A, ∑ w ∈ A, k v w * (f w - f v) +
        ∑ v ∈ A, ∑ w ∈ A, k v w * (f v - f w) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun v _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun w _ => by ring
    linarith
  -- every boundary current is outward, and the bond `yx` carries at least `f y - f x`
  have hterm : ∀ v ∈ A, ∀ w ∈ W \ A, k v w * (f w - f v) ≤ 0 := by
    intro v hv w hw
    have hv' := (Finset.mem_filter.1 hv).2
    have hw' : f w < f y := by
      have hwA : w ∉ A := (Finset.mem_sdiff.1 hw).2
      rw [Finset.mem_filter, not_and, not_le] at hwA
      exact hwA (Finset.mem_sdiff.1 hw).1
    exact mul_nonpos_of_nonneg_of_nonpos (hk0 v w) (by linarith)
  have hxs : x ∈ W \ A := Finset.mem_sdiff.2 ⟨hx, hxA⟩
  have hbd : ∑ v ∈ A, ∑ w ∈ W \ A, k v w * (f w - f v) ≤ -(f y - f x) := by
    have hrow : ∑ w ∈ W \ A, k y w * (f w - f y) ≤ -(f y - f x) := by
      rw [← Finset.add_sum_erase _ _ hxs]
      have hrest : ∑ w ∈ (W \ A).erase x, k y w * (f w - f y) ≤ 0 :=
        Finset.sum_nonpos fun w hw => hterm y hyA w (Finset.mem_of_mem_erase hw)
      have hyx : k y x * (f x - f y) ≤ -(f y - f x) := by nlinarith
      linarith
    rw [← Finset.add_sum_erase _ _ hyA]
    have hrest : ∑ v ∈ A.erase y, ∑ w ∈ W \ A, k v w * (f w - f v) ≤ 0 :=
      Finset.sum_nonpos fun v hv =>
        Finset.sum_nonpos fun w hw => hterm v (Finset.mem_of_mem_erase hv) w hw
    linarith
  have hsum : ∑ v ∈ A, b v ≤ -(f y - f x) := by
    have : ∑ v ∈ A, b v = ∑ v ∈ A, ∑ w ∈ A, k v w * (f w - f v) +
        ∑ v ∈ A, ∑ w ∈ W \ A, k v w * (f w - f v) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← hkcl v (hAW hv), ← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_of_subset hAW]
    linarith
  have habs : -∑ v ∈ A, b v ≤ ∑ v ∈ W, |b v| := by
    rw [← Finset.sum_neg_distrib]
    exact (Finset.sum_le_sum fun v _ => neg_le_abs (b v)).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hAW fun v _ _ => abs_nonneg _)
  linarith

/-- **Energy identity for a two-terminal design.** If a finite network `T` with symmetric
nonnegative conductances `c` carries the potential `v` with Kirchhoff's law
`∑_s c t s (v s - v t) = -D [t = z] + D [t = w]`, then `c z w (v w - v z)² ≤ -D (v w - v z)`. -/
theorem mul_sq_le_of_kirchhoff {ι : Type*} [DecidableEq ι] (T : Finset ι) (c : ι → ι → ℝ)
    (v : ι → ℝ) (hc : ∀ t s, c t s = c s t) (hc0 : ∀ t s, 0 ≤ c t s) {z w : ι} (hz : z ∈ T)
    (hw : w ∈ T) (hzw : z ≠ w) (D : ℝ)
    (hkcl : ∀ t ∈ T, ∑ s ∈ T, c t s * (v s - v t) =
      (if t = z then -D else 0) + (if t = w then D else 0)) :
    c z w * (v w - v z) ^ 2 ≤ -(D * (v w - v z)) := by
  -- pair Kirchhoff's law with `v`
  have hS : ∑ t ∈ T, v t * ∑ s ∈ T, c t s * (v s - v t) = D * (v w - v z) := by
    rw [Finset.sum_congr rfl fun t ht => by rw [hkcl t ht]]
    simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq',
      if_pos hz, if_pos hw]
    ring
  -- symmetrize
  have hsym : ∑ t ∈ T, v t * ∑ s ∈ T, c t s * (v s - v t) =
      ∑ t ∈ T, ∑ s ∈ T, c t s * (v t * (v s - v t)) := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hswap : ∑ t ∈ T, ∑ s ∈ T, c t s * (v t * (v s - v t)) =
      ∑ t ∈ T, ∑ s ∈ T, c t s * (v s * (v t - v s)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
    rw [hc]
  have hsq : ∑ t ∈ T, ∑ s ∈ T, c t s * (v t * (v s - v t)) =
      -(∑ t ∈ T, ∑ s ∈ T, c t s * (v s - v t) ^ 2) / 2 := by
    have : 2 * ∑ t ∈ T, ∑ s ∈ T, c t s * (v t * (v s - v t)) =
        -(∑ t ∈ T, ∑ s ∈ T, c t s * (v s - v t) ^ 2) := by
      rw [two_mul]
      nth_rewrite 2 [hswap]
      rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    linarith
  -- the double sum is at least its `(z, w)` and `(w, z)` terms
  have hnn : ∀ t s, 0 ≤ c t s * (v s - v t) ^ 2 := fun t s => mul_nonneg (hc0 t s) (sq_nonneg _)
  have hlow : 2 * (c z w * (v w - v z) ^ 2) ≤
      ∑ t ∈ T, ∑ s ∈ T, c t s * (v s - v t) ^ 2 := by
    have hrow : ∀ t ∈ T, ∀ s ∈ T, c t s * (v s - v t) ^ 2 ≤
        ∑ s' ∈ T, c t s' * (v s' - v t) ^ 2 := fun t _ s hs =>
      Finset.single_le_sum (f := fun s' => c t s' * (v s' - v t) ^ 2) (fun s' _ => hnn t s') hs
    have hpair : ∑ t ∈ ({z, w} : Finset ι), ∑ s ∈ T, c t s * (v s - v t) ^ 2 ≤
        ∑ t ∈ T, ∑ s ∈ T, c t s * (v s - v t) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (by
        intro t ht
        rcases Finset.mem_insert.1 ht with rfl | ht
        · exact hz
        · rw [Finset.mem_singleton.1 ht]; exact hw)
        fun t _ _ => Finset.sum_nonneg fun s _ => hnn t s
    rw [Finset.sum_pair hzw] at hpair
    have h1 := hrow z hz w hw
    have h2 := hrow w hw z hz
    have hcw : c w z * (v z - v w) ^ 2 = c z w * (v w - v z) ^ 2 := by rw [hc]; ring
    linarith
  linarith

/-- The real inequality behind the path designs: from `c δ² ≤ -D δ` and `δ = m D - ε`,
`c |ε| ≤ (c m + 1) |D|`. -/
theorem mul_abs_le_of_energy {c m D δ ε : ℝ} (hc : 0 ≤ c) (hm : 0 ≤ m)
    (hE : c * δ ^ 2 ≤ -(D * δ)) (hδ : δ = m * D - ε) :
    c * |ε| ≤ (c * m + 1) * |D| := by
  have hcδ : c * |δ| ≤ |D| := by
    rcases eq_or_ne δ 0 with h0 | h0
    · rw [h0, abs_zero, mul_zero]; exact abs_nonneg _
    · have hpos : 0 < |δ| := abs_pos.2 h0
      have h1 : c * |δ| * |δ| ≤ |D| * |δ| := by
        have : -(D * δ) ≤ |D| * |δ| := by rw [← abs_mul]; exact neg_le_abs _
        nlinarith [sq_abs δ]
      exact le_of_mul_le_mul_right h1 hpos
  have hε : |ε| ≤ m * |D| + |δ| := by
    have : ε = m * D - δ := by linarith
    rw [this]
    calc |m * D - δ| ≤ |m * D| + |δ| := abs_sub _ _
      _ = m * |D| + |δ| := by rw [abs_mul, abs_of_nonneg hm]
  nlinarith

/-! ### The surgery region and the exterior network -/

/-- The site of `ℤ²` with coordinates `(a, b)`. -/
def vtx (q : ℤ × ℤ) : Vertex 2 := ![q.1, q.2]

/-- The surgery region: the square `Q_2` minus its four corners. -/
def surgerySites : Set (Vertex 2) := {x | (x 0, x 1) ∈ siteList}

/-- The terminals of the surgery region, as a finite set of sites. -/
def surgeryTerminals : Finset (Vertex 2) := (terminalList.map vtx).toFinset

open scoped Classical in
/-- The exterior of the surgery region in the environment `ω` is the finite network on the
terminals with conductances `c` and potentials `ℓ⁰`: `c t s = c s t ≥ 0`, `∑_s c t s ≤ 4`, and for
every environment `ω'` that agrees with `ω` on the bonds not meeting the region, with unique
infinite cluster `𝒞'`:
* `c t s ≠ 0` only between terminals of the same exterior component (`t ∈ 𝒞' ↔ s ∈ 𝒞'`);
* the branch `ts` carries an electromotive force `c t s (ℓ⁰ s - ℓ⁰ t) ≠ 0` only between terminals of
  the exterior infinite component, which lie in `𝒞'`;
* every corrected plane `ℓ'` of `𝒞'` satisfies Kirchhoff's law at each terminal `t ∈ 𝒞'`: the
  current from the region, `∑ (ℓ'(y) - ℓ'(t))` over the open bonds `ty` with `y` in the region,
  plus the current `∑_s c t s ((ℓ'(s) - ℓ'(t)) - (ℓ⁰ s - ℓ⁰ t))` from the exterior, vanishes. -/
def ExteriorNetworkAt (ω : Configuration 2) (c : Vertex 2 → Vertex 2 → ℝ) (l0 : Vertex 2 → ℝ) :
    Prop :=
  (∀ t s, c t s = c s t) ∧ (∀ t s, 0 ≤ c t s) ∧
    (∀ t, ∑ s ∈ surgeryTerminals, c t s ≤ 4) ∧
    ∀ ω' : Configuration 2, (∀ e, ¬ MeetsSites surgerySites e → ω' e = ω e) →
    ∀ h' : HasUniqueInfiniteOpenComponent ω',
      (∀ t ∈ surgeryTerminals, ∀ s ∈ surgeryTerminals, c t s ≠ 0 →
        (t ∈ (uniqueInfiniteComponent h').supp ↔ s ∈ (uniqueInfiniteComponent h').supp)) ∧
      (∀ t ∈ surgeryTerminals, ∀ s ∈ surgeryTerminals, c t s * (l0 s - l0 t) ≠ 0 →
        t ∈ (uniqueInfiniteComponent h').supp) ∧
      ∀ u', IsCorrectedPlane (uniqueInfiniteComponent h') (Pi.single 0 1) u' →
        ∀ t ∈ surgeryTerminals, ∀ ht : t ∈ (uniqueInfiniteComponent h').supp,
          ∑ y ∈ ((componentGraph (uniqueInfiniteComponent h')).neighborFinset ⟨t, ht⟩).filter
              (fun y => y.val ∈ surgerySites), (u' y - u' ⟨t, ht⟩) +
            ∑ s ∈ surgeryTerminals, c t s *
              ((Rigidity.Section3.extend _ u' s - Rigidity.Section3.extend _ u' t) -
                (l0 s - l0 t)) = 0

/-- **Exterior network of the surgery region** (the new ingredient): almost surely the exterior
of the surgery region is a finite network on its terminals, `ExteriorNetworkAt ω c ℓ⁰`, where
`ℓ⁰` is the corrected plane `ℓ_{e₁}` of the environment with every bond meeting the region closed.

Proved in `Rigidity/Proofs/S3/ExteriorNetwork.lean` (`exteriorNetworkStep`, for
`p_c(2) < p < 1`) from the literature inputs on the uniqueness of the infinite cluster, the
corrected planes, the Liouville property at order zero and the Green function of the infinite
cluster. Route: by finite energy the environment `ω^E` with every bond meeting the region closed
is typical; a finite exterior component is a finite network, traced on its terminals through the
Dirichlet problem; on the exterior infinite component `𝒦`, `v = ℓ' - ℓ⁰` is harmonic off the
terminals, of slope zero, with zero total flux through the terminals, so by the Liouville property
it is a constant plus a zero-sum combination of Green columns at the terminals (asymptotics of
Dario and Gu), and its response at the terminals is a trace network (uniqueness by the energy
identity, reciprocity by Green's identity). The conductances are the traces of the exterior
components and the potentials are `ℓ⁰`, extended by zero off `𝒦`. -/
def ExteriorNetworkStep (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ∃ (c : Vertex 2 → Vertex 2 → ℝ) (l0 : Vertex 2 → ℝ),
    ExteriorNetworkAt ω c l0

/-- After setting the bonds meeting the surgery region in any way, the environment has a unique
infinite cluster carrying a corrected plane `ℓ_{e₁}`. -/
def ModifiedPlaneAt (ω : Configuration 2) : Prop :=
  ∀ F : Set (Bond 2), ∃ h : HasUniqueInfiniteOpenComponent (modifyNear surgerySites F ω),
    ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) u

/-- Almost surely `ModifiedPlaneAt ω` (Lemma 2.1 applied to the uniqueness of the infinite cluster
and to the existence of the corrector; the modifications form a finite family). -/
def ModifiedPlaneStep (p : unitInterval) : Prop :=
  ∀ᵐ ω ∂latticeBondLaw 2 p, ModifiedPlaneAt ω

/-! ### The local surgery step and the reduction -/

/-- **Local surgery** (the content of the route; see the module docstring): there are a finite
region `U` (inside a cube `Q_R`), finitely many designs `(F, a)` (the bonds meeting `U` are set
open exactly on `F`, and `(a, a + e₁)` is the designated bond) and a constant `K ≥ 1` such that,
for every `L ≥ 1`, almost surely, `|∇ℓ_{e₁}(0)| > K L` implies that for some design the modified
environment has a rise of more than `L` across its designated bond. -/
def LocalSurgeryStep (p : unitInterval) : Prop :=
  ∃ (R : ℕ) (U : Set (Vertex 2)) (D : Set (Set (Bond 2) × Vertex 2)) (K : ℝ),
    (∀ e, MeetsSites U e → e ∈ Rigidity.Steps.S4.bondsNear 2 R) ∧ D.Finite ∧ 1 ≤ K ∧
    ∀ L : ℝ, 1 ≤ L → ∀ᵐ ω ∂latticeBondLaw 2 p,
      ω ∈ gradientEvent (K * L) → ∃ d ∈ D, modifyNear U d.1 ω ∈ riseEvent d.2 L

/-- **The signed variant of Proposition 3.2** from Proposition 3.2 as printed and the local
surgery step: for `0 < p < 1`, `NotLipschitzStmt 2 p` and `LocalSurgeryStep p` give
`HorizontalIncrementStep p`. -/
theorem horizontalIncrementStep_of_localSurgery {p : unitInterval} (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (h32 : Rigidity.Section3.NotLipschitzStmt 2 p)
    (hsurg : LocalSurgeryStep p) : HorizontalIncrementStep p := by
  intro L hL h0
  obtain ⟨R, U, D, K, hU, hD, hK, hs⟩ := hsurg
  set μ := latticeBondLaw 2 p
  -- the rise event is null at the origin, hence everywhere by stationarity
  have hrise0 : μ (riseEvent 0 L) = 0 := measure_mono_null (riseEvent_zero_subset L) h0
  have hrise : ∀ a : Vertex 2, μ (riseEvent a L) = 0 := by
    intro a
    refine measure_mono_null (fun ω hω => ?_)
      (latticeBondLaw_preimage_translation_null hrise0 (-a))
    have := riseEvent_translation (-a) hω
    rwa [add_neg_cancel] at this
  -- hence null after every design, by finite energy
  have hdesign : μ (⋃ d ∈ D, modifyNear U d.1 ⁻¹' riseEvent d.2 L) = 0 :=
    (measure_biUnion_null_iff hD.countable).2 fun d _ =>
      modifyNear_preimage_null hp0 hp1 hU d.1 (hrise d.2)
  have hKL : 1 ≤ K * L := by nlinarith
  refine (h32.originGradient_ne_zero hKL) (measure_mono_null ?_ (measure_union_null (ae_iff.1 (hs L hL))
    hdesign))
  intro ω hω
  by_cases hgood : ∃ d ∈ D, modifyNear U d.1 ω ∈ riseEvent d.2 L
  · obtain ⟨d, hd, hmem⟩ := hgood
    exact Or.inr (Set.mem_iUnion₂.2 ⟨d, hd, hmem⟩)
  · exact Or.inl fun himp => hgood (himp hω)

/-! ### The path designs

The sites of the surgery region (`siteList`), its terminals (`terminalList`), the 120 path designs
(`designs`) and their checks by `decide +kernel` (`designs_good`, `designs_cover`, `siteList_nbr4`,
`terminalList_not_site`, `siteList_bound`) are in the leaf module
`Rigidity/Steps/S3/SignedIncrementData.lean`. -/

/-! #### Sites of `ℤ²` -/

theorem vtx_injective : Function.Injective vtx := fun a b h =>
  Prod.ext (by simpa [vtx] using congrFun h 0) (by simpa [vtx] using congrFun h 1)

theorem eq_vtx (x : Vertex 2) : x = vtx (x 0, x 1) := by
  funext i; fin_cases i <;> rfl

theorem mem_surgerySites_vtx {q : ℤ × ℤ} : vtx q ∈ surgerySites ↔ q ∈ siteList := Iff.rfl

theorem mem_surgeryTerminals {x : Vertex 2} :
    x ∈ surgeryTerminals ↔ ∃ a ∈ terminalList, vtx a = x := by
  simp [surgeryTerminals]

theorem vtx_mem_surgeryTerminals {a : ℤ × ℤ} (ha : a ∈ terminalList) :
    vtx a ∈ surgeryTerminals := mem_surgeryTerminals.2 ⟨a, ha, rfl⟩

theorem not_mem_surgerySites_of_mem_terminals {x : Vertex 2} (hx : x ∈ surgeryTerminals) :
    x ∉ surgerySites := by
  obtain ⟨a, ha, rfl⟩ := mem_surgeryTerminals.1 hx
  exact terminalList_not_site a ha

theorem card_surgeryTerminals : surgeryTerminals.card ≤ 16 :=
  (List.toFinset_card_le _).trans (by simp [card_terminalList])

theorem vtx_add_e1 (a : ℤ × ℤ) : vtx (a.1 + 1, a.2) = vtx a + e1 := by
  funext i; fin_cases i <;> simp [vtx, e1]

theorem adj_vtx_of_mem_nbr4 {a b : ℤ × ℤ} (h : b ∈ nbr4 a) :
    (nearestNeighborGraph 2).Adj (vtx a) (vtx b) := by
  simp only [nbr4, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨0, Or.inl (by funext j; fin_cases j <;> simp [vtx, LatticeProb.unit])⟩
  · exact ⟨0, Or.inr (by funext j; fin_cases j <;> simp [vtx, LatticeProb.unit])⟩
  · exact ⟨1, Or.inl (by funext j; fin_cases j <;> simp [vtx, LatticeProb.unit])⟩
  · exact ⟨1, Or.inr (by funext j; fin_cases j <;> simp [vtx, LatticeProb.unit])⟩

theorem exists_nbr4_of_adj {a : ℤ × ℤ} {y : Vertex 2}
    (h : (nearestNeighborGraph 2).Adj (vtx a) y) : ∃ b ∈ nbr4 a, y = vtx b := by
  obtain ⟨i, hi | hi⟩ := h
  · fin_cases i
    · refine ⟨(a.1 + 1, a.2), by simp [nbr4], ?_⟩
      rw [hi]; funext j; fin_cases j <;> simp [vtx, LatticeProb.unit]
    · refine ⟨(a.1, a.2 + 1), by simp [nbr4], ?_⟩
      rw [hi]; funext j; fin_cases j <;> simp [vtx, LatticeProb.unit]
  · fin_cases i
    · refine ⟨(a.1 - 1, a.2), by simp [nbr4], ?_⟩
      funext j; have := congrFun hi j
      fin_cases j <;> simp [vtx, LatticeProb.unit] at this ⊢ <;> linarith
    · refine ⟨(a.1, a.2 - 1), by simp [nbr4], ?_⟩
      funext j; have := congrFun hi j
      fin_cases j <;> simp [vtx, LatticeProb.unit] at this ⊢ <;> linarith

/-! #### Paths -/

theorem zipPairs_cons_cons (a b : ℤ × ℤ) (rest : List (ℤ × ℤ)) :
    zipPairs (a :: b :: rest) = (a, b) :: zipPairs (b :: rest) := rfl

theorem triples_cons_cons_cons (a b c : ℤ × ℤ) (rest : List (ℤ × ℤ)) :
    triples (a :: b :: c :: rest) = (a, b, c) :: triples (b :: c :: rest) := rfl

/-- Harmonicity at the middle of every consecutive triple makes the increments along the path
constant. -/
theorem incr_eq_of_triples (f : ℤ × ℤ → ℝ) : ∀ P : List (ℤ × ℤ),
    (∀ x ∈ triples P, (f x.1 - f x.2.1) + (f x.2.2 - f x.2.1) = 0) →
      ∀ q ∈ zipPairs P, ∀ q' ∈ zipPairs P, f q.2 - f q.1 = f q'.2 - f q'.1
  | [], _ => by simp [zipPairs]
  | [_], _ => by simp [zipPairs]
  | [a, b], _ => by
    intro q hq q' hq'
    simp only [zipPairs, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
      List.mem_singleton] at hq hq'
    rw [hq, hq']
  | a :: b :: c :: rest, h => by
    have hrec := incr_eq_of_triples f (b :: c :: rest) fun x hx =>
      h x (by rw [triples_cons_cons_cons]; exact List.mem_cons_of_mem _ hx)
    have habc := h (a, b, c) (by rw [triples_cons_cons_cons]; exact List.mem_cons.2 (Or.inl rfl))
    have hbc : (b, c) ∈ zipPairs (b :: c :: rest) := by
      rw [zipPairs_cons_cons]; exact List.mem_cons.2 (Or.inl rfl)
    have hall : ∀ q ∈ zipPairs (a :: b :: c :: rest), f q.2 - f q.1 = f c - f b := by
      intro q hq
      rw [zipPairs_cons_cons, List.mem_cons] at hq
      rcases hq with rfl | hq
      · simp only at habc ⊢; linarith
      · exact hrec q hq (b, c) hbc
    intro q hq q' hq'
    rw [hall q hq, hall q' hq']

/-- The increments along a path add up to the difference of its endpoint values. -/
theorem sum_incr_eq (f : ℤ × ℤ → ℝ) : ∀ (P : List (ℤ × ℤ)) (a b : ℤ × ℤ), P.head? = some a →
    P.getLast? = some b → ((zipPairs P).map fun q => f q.2 - f q.1).sum = f b - f a
  | [], a, b, h, _ => by simp at h
  | [x], a, b, ha, hb => by
    simp only [List.head?_cons, Option.some.injEq, List.getLast?_singleton] at ha hb
    subst ha; subst hb; simp [zipPairs]
  | x :: y :: rest, a, b, ha, hb => by
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    have hrec := sum_incr_eq f (y :: rest) y b rfl (by rw [← hb]; simp [List.getLast?_cons_cons])
    rw [zipPairs_cons_cons, List.map_cons, List.sum_cons, hrec]
    ring

theorem sum_map_eq_length_mul {α : Type*} (g : α → ℝ) (D : ℝ) :
    ∀ l : List α, (∀ q ∈ l, g q = D) → (l.map g).sum = l.length * D
  | [], _ => by simp
  | x :: l, h => by
    rw [List.map_cons, List.sum_cons,
      sum_map_eq_length_mul g D l fun q hq => h q (List.mem_cons_of_mem _ hq),
      h x (List.mem_cons.2 (Or.inl rfl))]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    ring

/-- A property of the first site propagated along the bonds of a path holds at every site. -/
theorem forall_zipPairs_of_head (S : ℤ × ℤ → Prop) : ∀ (P : List (ℤ × ℤ)) (a : ℤ × ℤ),
    P.head? = some a → S a → (∀ q ∈ zipPairs P, S q.1 → S q.2) →
      ∀ q ∈ zipPairs P, S q.1 ∧ S q.2
  | [], _, _, _, _ => by simp [zipPairs]
  | [_], _, _, _, _ => by simp [zipPairs]
  | x :: y :: rest, a, ha, hSa, hstep => by
    simp only [List.head?_cons, Option.some.injEq] at ha
    subst ha
    have hSy : S y :=
      hstep (x, y) (by rw [zipPairs_cons_cons]; exact List.mem_cons.2 (Or.inl rfl)) hSa
    have hrec := forall_zipPairs_of_head S (y :: rest) y rfl hSy fun q hq =>
      hstep q (by rw [zipPairs_cons_cons]; exact List.mem_cons_of_mem _ hq)
    intro q hq
    rw [zipPairs_cons_cons, List.mem_cons] at hq
    rcases hq with rfl | hq
    · exact ⟨hSa, hSy⟩
    · exact hrec q hq

theorem mem_partnersOf {a b : ℤ × ℤ} {P : List (ℤ × ℤ)} {q : (ℤ × ℤ) × (ℤ × ℤ)}
    (hq : q ∈ zipPairs P) (h : (q.1 = a ∧ q.2 = b) ∨ (q.2 = a ∧ q.1 = b)) :
    b ∈ partnersOf a P := by
  unfold partnersOf
  rw [List.mem_filterMap]
  refine ⟨q, hq, ?_⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1]; exact congrArg some h2
  · by_cases h3 : q.1 = a
    · rw [if_pos h3]; exact congrArg some (h1.trans (h3.symm.trans h2))
    · rw [if_neg h3, if_pos h1]; exact congrArg some h2

/-! #### Neighbour sums on a cluster -/

section Network

open scoped Classical

variable {ω : Configuration 2}

theorem extend_of_mem {C : OpenComponent ω} (u : C → ℝ) {x : Vertex 2} (hx : x ∈ C.supp) :
    Rigidity.Section3.extend C u x = u ⟨x, hx⟩ := by
  simp [Rigidity.Section3.extend, hx]

/-- A neighbour sum on a cluster restricted to the neighbours with a property `P` is a sum over
any finite set `W` containing those neighbours. -/
theorem sum_neighborFinset_filter_eq (C : OpenComponent ω) (x : C) (P : Vertex 2 → Prop)
    [DecidablePred P] (g : Vertex 2 → ℝ) (W : Finset (Vertex 2))
    (hW : ∀ y, (openGraph ω).Adj x.val y → P y → y ∈ W) :
    ∑ y ∈ ((componentGraph C).neighborFinset x).filter (fun y => P y.val), g y.val =
      ∑ w ∈ W, if (openGraph ω).Adj x.val w ∧ P w then g w else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_image (g := Subtype.val) fun a _ b _ h => Subtype.ext h]
  congr 1
  ext w
  simp only [Finset.mem_image, Finset.mem_filter, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨y, ⟨hadj, hP⟩, rfl⟩
    exact ⟨hW _ hadj hP, hadj, hP⟩
  · rintro ⟨-, hadj, hP⟩
    exact ⟨⟨w, C.mem_supp_of_adj_mem_supp x.2 hadj⟩, ⟨hadj, hP⟩, rfl⟩

/-- The unrestricted form of `sum_neighborFinset_filter_eq`. -/
theorem sum_neighborFinset_eq (C : OpenComponent ω) (x : C) (g : Vertex 2 → ℝ)
    (W : Finset (Vertex 2)) (hW : ∀ y, (openGraph ω).Adj x.val y → y ∈ W) :
    ∑ y ∈ (componentGraph C).neighborFinset x, g y.val =
      ∑ w ∈ W, if (openGraph ω).Adj x.val w then g w else 0 := by
  have h := sum_neighborFinset_filter_eq C x (fun _ => True) g W fun y hy _ => hW y hy
  simpa using h

/-- The sites of the surgery region and its terminals. -/
def nearSites : Finset (Vertex 2) := ((siteList ++ terminalList).map vtx).toFinset

theorem mem_nearSites_of_site {y : Vertex 2} (hy : y ∈ surgerySites) : y ∈ nearSites := by
  simp only [nearSites, List.mem_toFinset, List.mem_map, List.mem_append]
  exact ⟨(y 0, y 1), Or.inl hy, (eq_vtx y).symm⟩

theorem mem_nearSites_of_adj {v y : Vertex 2} (hv : v ∈ surgerySites)
    (hadj : (nearestNeighborGraph 2).Adj v y) : y ∈ nearSites := by
  rw [eq_vtx v] at hadj
  obtain ⟨b, hb, rfl⟩ := exists_nbr4_of_adj hadj
  simp only [nearSites, List.mem_toFinset, List.mem_map, List.mem_append]
  exact ⟨b, siteList_nbr4 _ hv b hb, rfl⟩

theorem mem_nearSites_of_terminal {y : Vertex 2} (hy : y ∈ surgeryTerminals) : y ∈ nearSites := by
  obtain ⟨a, ha, rfl⟩ := mem_surgeryTerminals.1 hy
  simp only [nearSites, List.mem_toFinset, List.mem_map, List.mem_append]
  exact ⟨a, Or.inr ha, rfl⟩

theorem site_or_terminal_of_mem_nearSites {v : Vertex 2} (hv : v ∈ nearSites) :
    v ∈ surgerySites ∨ v ∈ surgeryTerminals := by
  simp only [nearSites, List.mem_toFinset, List.mem_map, List.mem_append] at hv
  obtain ⟨a, ha | ha, rfl⟩ := hv
  · exact Or.inl ha
  · exact Or.inr (vtx_mem_surgeryTerminals ha)

theorem zero_mem_surgerySites : (0 : Vertex 2) ∈ surgerySites := by
  show ((0 : Vertex 2) 0, (0 : Vertex 2) 1) ∈ siteList
  decide

theorem unit_mem_surgerySites (i : Fin 2) : LatticeProb.unit i ∈ surgerySites := by
  show (LatticeProb.unit i 0, LatticeProb.unit i 1) ∈ siteList
  fin_cases i <;> decide

/-- **Reciprocity bound**: if the exterior of the surgery region is a finite network with
conductances `c` and potentials `ℓ⁰`, Kirchhoff's law holds on the sites of the region and its
terminals in the cluster, with sources `b_t = ∑_s c t s (ℓ⁰ s - ℓ⁰ t)` at the terminals, and the
super-level-set bound gives `|∇ℓ(0)| ≤ 2 ∑_t |b_t|`. -/
theorem originGradientNorm_le_of_network (C : OpenComponent ω) (ho : (0 : Vertex 2) ∈ C.supp)
    (u : C → ℝ) (hharm : ∀ x, componentLaplacian C u x = 0)
    (c : Vertex 2 → Vertex 2 → ℝ) (l0 : Vertex 2 → ℝ) (hcs : ∀ t s, c t s = c s t)
    (hc0 : ∀ t s, 0 ≤ c t s)
    (hsame : ∀ t ∈ surgeryTerminals, ∀ s ∈ surgeryTerminals, c t s ≠ 0 →
      (t ∈ C.supp ↔ s ∈ C.supp))
    (hkcl : ∀ t ∈ surgeryTerminals, ∀ ht : t ∈ C.supp,
      ∑ y ∈ ((componentGraph C).neighborFinset ⟨t, ht⟩).filter
          (fun y => y.val ∈ surgerySites), (u y - u ⟨t, ht⟩) +
        ∑ s ∈ surgeryTerminals, c t s *
          ((Rigidity.Section3.extend C u s - Rigidity.Section3.extend C u t) -
            (l0 s - l0 t)) = 0)
    {M : ℝ} (hM : ∀ t ∈ surgeryTerminals, ∀ s ∈ surgeryTerminals, c t s * |l0 s - l0 t| ≤ M) :
    Rigidity.Section3.originGradientNorm C ho u ≤ 2 * (16 * (16 * M)) := by
  set T := surgeryTerminals with hTdef
  set f : Vertex 2 → ℝ := Rigidity.Section3.extend C u with hf
  set W := nearSites.filter (· ∈ C.supp) with hWdef
  set k : Vertex 2 → Vertex 2 → ℝ := fun v w =>
    (if (openGraph ω).Adj v w ∧ (v ∈ surgerySites ∨ w ∈ surgerySites) then 1 else 0) +
      (if v ∈ T ∧ w ∈ T then c v w else 0) with hkdef
  set b : Vertex 2 → ℝ := fun v => if v ∈ T then ∑ s ∈ T, c v s * (l0 s - l0 v) else 0
    with hbdef
  have hk : ∀ v w, k v w = k w v := by
    intro v w
    simp only [hkdef, hcs v w, (openGraph ω).adj_comm v w, or_comm (a := v ∈ surgerySites),
      and_comm (a := v ∈ T)]
  have hk0 : ∀ v w, 0 ≤ k v w := fun v w =>
    add_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> simp [hc0])
  have hkcl' : ∀ v ∈ W, ∑ w ∈ W, k v w * (f w - f v) = b v := by
    intro v hv
    have hvC : v ∈ C.supp := (Finset.mem_filter.1 hv).2
    have hsplit : ∑ w ∈ W, k v w * (f w - f v) =
        (∑ w ∈ W, if (openGraph ω).Adj v w ∧ (v ∈ surgerySites ∨ w ∈ surgerySites) then
          f w - f v else 0) +
        ∑ w ∈ W, if v ∈ T ∧ w ∈ T then c v w * (f w - f v) else 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp only [hkdef]
      split_ifs <;> ring
    have hint : ∑ y ∈ ((componentGraph C).neighborFinset ⟨v, hvC⟩).filter
          (fun y => v ∈ surgerySites ∨ y.val ∈ surgerySites), (u y - u ⟨v, hvC⟩) =
        ∑ w ∈ W, if (openGraph ω).Adj v w ∧ (v ∈ surgerySites ∨ w ∈ surgerySites) then
          f w - f v else 0 := by
      have hW' : ∀ y, (openGraph ω).Adj (⟨v, hvC⟩ : C).val y →
          (fun y => v ∈ surgerySites ∨ y ∈ surgerySites) y → y ∈ W := by
        intro y hadj hP
        refine Finset.mem_filter.2 ⟨?_, C.mem_supp_of_adj_mem_supp hvC hadj⟩
        rcases hP with hvU | hyU
        · exact mem_nearSites_of_adj hvU (openGraph_le ω hadj)
        · exact mem_nearSites_of_site hyU
      refine (Finset.sum_congr rfl fun y _ => ?_).trans
        (sum_neighborFinset_filter_eq C ⟨v, hvC⟩
          (fun y => v ∈ surgerySites ∨ y ∈ surgerySites) (fun w => f w - f v) W hW')
      simp only [hf, extend_of_mem u y.2, extend_of_mem u hvC]
    rcases site_or_terminal_of_mem_nearSites (Finset.mem_filter.1 hv).1 with hvU | hvT
    · have hvT : v ∉ T := fun h => not_mem_surgerySites_of_mem_terminals h hvU
      have h2 : (∑ w ∈ W, if v ∈ T ∧ w ∈ T then c v w * (f w - f v) else 0) = 0 :=
        Finset.sum_eq_zero fun w _ => if_neg fun h => hvT h.1
      rw [hsplit, h2, ← hint, Finset.filter_true_of_mem fun y _ => Or.inl hvU]
      have := hharm ⟨v, hvC⟩
      unfold componentLaplacian at this
      simp only [hbdef, if_neg hvT]
      linarith
    · replace hvT : v ∈ T := hvT
      have hvU : v ∉ surgerySites := not_mem_surgerySites_of_mem_terminals hvT
      have hfilt : ((componentGraph C).neighborFinset ⟨v, hvC⟩).filter
            (fun y => v ∈ surgerySites ∨ y.val ∈ surgerySites) =
          ((componentGraph C).neighborFinset ⟨v, hvC⟩).filter (fun y => y.val ∈ surgerySites) :=
        Finset.filter_congr fun y _ => by simp [hvU]
      have h2 : (∑ w ∈ W, if v ∈ T ∧ w ∈ T then c v w * (f w - f v) else 0) =
          ∑ s ∈ T, c v s * (f s - f v) := by
        have hWT : W.filter (· ∈ T) = T.filter (· ∈ C.supp) := by
          ext w
          simp only [hWdef, Finset.mem_filter]
          constructor
          · rintro ⟨⟨-, hwC⟩, hwT⟩; exact ⟨hwT, hwC⟩
          · rintro ⟨hwT, hwC⟩; exact ⟨⟨mem_nearSites_of_terminal hwT, hwC⟩, hwT⟩
        calc (∑ w ∈ W, if v ∈ T ∧ w ∈ T then c v w * (f w - f v) else 0)
            = ∑ w ∈ W.filter (· ∈ T), c v w * (f w - f v) := by
              rw [Finset.sum_filter (s := W)]
              exact Finset.sum_congr rfl fun w _ => by simp only [hvT, true_and]
          _ = ∑ s ∈ T, c v s * (f s - f v) := by
              rw [hWT]
              refine Finset.sum_filter_of_ne fun s hs hne => ?_
              exact (hsame v hvT s hs (left_ne_zero_of_mul hne)).1 hvC
      have hE := hkcl v hvT hvC
      rw [← hfilt] at hE
      have hsub : ∑ s ∈ T, c v s * ((f s - f v) - (l0 s - l0 v)) =
          ∑ s ∈ T, c v s * (f s - f v) - ∑ s ∈ T, c v s * (l0 s - l0 v) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [hsplit, h2, ← hint]
      simp only [hbdef, if_pos hvT]
      rw [hsub] at hE
      linarith
  -- the total source
  have hM0 : 0 ≤ M := by
    have h := hM _ (vtx_mem_surgeryTerminals (a := (3, -1)) (by decide))
      _ (vtx_mem_surgeryTerminals (a := (3, -1)) (by decide))
    simpa using (mul_nonneg (hc0 _ _) (abs_nonneg _)).trans h
  have hS : ∑ v ∈ W, |b v| ≤ 16 * (16 * M) := by
    have h1 : ∑ v ∈ W, |b v| ≤ ∑ v ∈ T, |b v| := by
      rw [← Finset.sum_filter_of_ne (p := (· ∈ T)) fun v _ hne => by
        by_contra hvT; exact hne (by simp [hbdef, hvT])]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => (Finset.mem_filter.1 hv).2)
        fun v _ _ => abs_nonneg _
    have h2 : ∀ v ∈ T, |b v| ≤ 16 * M := by
      intro v hv
      simp only [hbdef, if_pos hv]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_card_nsmul _ _ M fun s hs => ?_).trans ?_
      · rw [abs_mul, abs_of_nonneg (hc0 v s)]; exact hM v hv s hs
      · rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_surgeryTerminals) hM0
    refine h1.trans ((Finset.sum_le_card_nsmul _ _ _ h2).trans ?_)
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_surgeryTerminals) (by positivity)
  -- the bonds at the origin
  have h0W : (0 : Vertex 2) ∈ W :=
    Finset.mem_filter.2 ⟨mem_nearSites_of_site zero_mem_surgerySites, ho⟩
  have hterm : ∀ i : Fin 2, (if hi : (openGraph ω).Adj 0 (LatticeProb.unit i) then
      |u ⟨0, ho⟩ - u ⟨LatticeProb.unit i, C.mem_supp_of_adj_mem_supp ho hi⟩| else 0) ≤
      16 * (16 * M) := by
    intro i
    split_ifs with hi
    · have hiC := C.mem_supp_of_adj_mem_supp ho hi
      have hiW : LatticeProb.unit i ∈ W :=
        Finset.mem_filter.2 ⟨mem_nearSites_of_site (unit_mem_surgerySites i), hiC⟩
      have hk1 : 1 ≤ k (LatticeProb.unit i) 0 := by
        have : (openGraph ω).Adj (LatticeProb.unit i) 0 ∧
            (LatticeProb.unit i ∈ surgerySites ∨ (0 : Vertex 2) ∈ surgerySites) :=
          ⟨hi.symm, Or.inr zero_mem_surgerySites⟩
        simp only [hkdef, if_pos this]
        have : 0 ≤ (if LatticeProb.unit i ∈ T ∧ (0 : Vertex 2) ∈ T then
          c (LatticeProb.unit i) 0 else 0) := by split_ifs <;> simp [hc0]
        linarith
      have hk2 : 1 ≤ k 0 (LatticeProb.unit i) := hk _ _ ▸ hk1
      have hup := sub_le_sum_abs_of_kirchhoff W k f b hk hk0 hkcl' h0W hiW hk1
      have hdn := sub_le_sum_abs_of_kirchhoff W k f b hk hk0 hkcl' hiW h0W hk2
      rw [hf, extend_of_mem u ho, extend_of_mem u hiC] at hup hdn
      rw [abs_le]
      constructor <;> linarith
    · positivity
  unfold Rigidity.Section3.originGradientNorm
  rw [Fin.sum_univ_two]
  linarith [hterm 0, hterm 1]

/-! #### The path designs -/

/-- The bonds of a path. -/
def designBonds (P : List (ℤ × ℤ)) : Set (Bond 2) :=
  {e | ∃ q ∈ zipPairs P, e.val = s(vtx q.1, vtx q.2)}

/-- The designs `(F, a)` of the local surgery step: the bonds of a path design, and a site of it. -/
noncomputable def designPairs : List (Set (Bond 2) × Vertex 2) :=
  designs.flatMap fun x => (zipPairs x.2.2).flatMap fun q =>
    [(designBonds x.2.2, vtx q.1), (designBonds x.2.2, vtx q.2)]

theorem mem_designPairs {x : (ℤ × ℤ) × (ℤ × ℤ) × List (ℤ × ℤ)} (hx : x ∈ designs)
    {q : (ℤ × ℤ) × (ℤ × ℤ)} (hq : q ∈ zipPairs x.2.2) :
    (designBonds x.2.2, vtx q.1) ∈ designPairs ∧ (designBonds x.2.2, vtx q.2) ∈ designPairs := by
  simp only [designPairs, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
  exact ⟨⟨x, hx, q, hq, Or.inl rfl⟩, ⟨x, hx, q, hq, Or.inr rfl⟩⟩

theorem modifyNear_of_meets {U : Set (Vertex 2)} {F : Set (Bond 2)} {e : Bond 2}
    (he : MeetsSites U e) (ω : Configuration 2) : modifyNear U F ω e = decide (e ∈ F) := by
  simp [modifyNear, he]

theorem adj_design_of_mem {P : List (ℤ × ℤ)} {q : (ℤ × ℤ) × (ℤ × ℤ)} (hq : q ∈ zipPairs P)
    (hstep : q.2 ∈ nbr4 q.1) (hU : q.1 ∈ siteList ∨ q.2 ∈ siteList) :
    (openGraph (modifyNear surgerySites (designBonds P) ω)).Adj (vtx q.1) (vtx q.2) := by
  have hl := adj_vtx_of_mem_nbr4 hstep
  refine ⟨hl, ?_⟩
  have hmeet : MeetsSites surgerySites (bondOfAdjacent hl) := by
    rcases hU with h | h
    · exact ⟨vtx q.1, Sym2.mem_mk_left _ _, h⟩
    · exact ⟨vtx q.2, Sym2.mem_mk_right _ _, h⟩
  rw [modifyNear_of_meets hmeet, decide_eq_true_iff]
  exact ⟨q, hq, rfl⟩

theorem exists_partner_of_adj {P : List (ℤ × ℤ)} {a : ℤ × ℤ} {y : Vertex 2}
    (hadj : (openGraph (modifyNear surgerySites (designBonds P) ω)).Adj (vtx a) y)
    (hU : vtx a ∈ surgerySites ∨ y ∈ surgerySites) : ∃ b ∈ partnersOf a P, y = vtx b := by
  obtain ⟨hl, hopen⟩ := hadj
  have hmeet : MeetsSites surgerySites (bondOfAdjacent hl) := by
    rcases hU with h | h
    · exact ⟨vtx a, Sym2.mem_mk_left _ _, h⟩
    · exact ⟨y, Sym2.mem_mk_right _ _, h⟩
  rw [modifyNear_of_meets hmeet, decide_eq_true_iff] at hopen
  obtain ⟨q, hq, hqe⟩ := hopen
  change s(vtx a, y) = s(vtx q.1, vtx q.2) at hqe
  rcases Sym2.eq_iff.1 hqe with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨q.2, mem_partnersOf hq (Or.inl ⟨vtx_injective h1.symm, rfl⟩), h2⟩
  · exact ⟨q.1, mem_partnersOf hq (Or.inr ⟨vtx_injective h1.symm, rfl⟩), h2⟩

theorem mem_toFinset_partners {a : ℤ × ℤ} {P : List (ℤ × ℤ)} {b : ℤ × ℤ}
    (hb : b ∈ partnersOf a P) : vtx b ∈ ((partnersOf a P).map vtx).toFinset :=
  List.mem_toFinset.2 (List.mem_map.2 ⟨b, hb, rfl⟩)

/-- **Path design bound.** If no design has a rise of more than `L`, the branch `ts` of the
exterior network carries `c t s |ℓ⁰ s - ℓ⁰ t| ≤ 49 L` for the path design from `t` to `s`. -/
theorem pair_bound_of_design {c : Vertex 2 → Vertex 2 → ℝ} {l0 : Vertex 2 → ℝ}
    (hE : ExteriorNetworkAt ω c l0) (hM : ModifiedPlaneAt ω) {L : ℝ}
    (hno : ∀ d ∈ designPairs, modifyNear surgerySites d.1 ω ∉ riseEvent d.2 L)
    {x : (ℤ × ℤ) × (ℤ × ℤ) × List (ℤ × ℤ)} (hx : x ∈ designs)
    (hne : c (vtx x.1) (vtx x.2.1) * (l0 (vtx x.2.1) - l0 (vtx x.1)) ≠ 0) :
    c (vtx x.1) (vtx x.2.1) * |l0 (vtx x.2.1) - l0 (vtx x.1)| ≤ 49 * L := by
  obtain ⟨hcs, hc0, hcsum, hnet⟩ := hE
  have hG := designs_good x hx
  obtain ⟨t, s, P⟩ := x
  simp only at hG hne hno ⊢
  obtain ⟨hhead, hlast, htT, hsT, hts, hlen, hsteps, htrip, ⟨q0, hq0, hq0t, hpt, hq0U⟩,
    ⟨q1, hq1, hq1s, hps, hq1U⟩, hother, ⟨qr, hqr, hqrR⟩, ⟨ql, hql, hqlL⟩⟩ := hG
  set ω' := modifyNear surgerySites (designBonds P) ω with hω'
  obtain ⟨h', hplane⟩ := hM (designBonds P)
  set C' := uniqueInfiniteComponent h' with hC'
  obtain ⟨u', hu'⟩ := hplane
  have hagree : ∀ e, ¬ MeetsSites surgerySites e → ω' e = ω e := fun e he => by
    simp [hω', modifyNear, he]
  obtain ⟨hsame, hinf, hkcl⟩ := hnet ω' hagree h'
  set F : Vertex 2 → ℝ := Rigidity.Section3.extend C' u' with hF
  set f : ℤ × ℤ → ℝ := fun a => F (vtx a) with hfdef
  have htT' := vtx_mem_surgeryTerminals htT
  have hsT' := vtx_mem_surgeryTerminals hsT
  have htC : vtx t ∈ C'.supp := hinf _ htT' _ hsT' hne
  have hadjq : ∀ q ∈ zipPairs P, (openGraph ω').Adj (vtx q.1) (vtx q.2) := fun q hq =>
    adj_design_of_mem hq (hsteps q hq).1 (hsteps q hq).2
  have hinC : ∀ q ∈ zipPairs P, vtx q.1 ∈ C'.supp ∧ vtx q.2 ∈ C'.supp :=
    forall_zipPairs_of_head (fun a => vtx a ∈ C'.supp) P t hhead htC fun q hq h1 =>
      C'.mem_supp_of_adj_mem_supp h1 (hadjq q hq)
  -- harmonicity at the inner sites
  have hharm : ∀ y ∈ triples P, (f y.1 - f y.2.1) + (f y.2.2 - f y.2.1) = 0 := by
    intro y hy
    obtain ⟨hbU, hac, hpart, hab, hbc⟩ := htrip y hy
    have hbC : vtx y.2.1 ∈ C'.supp := (hinC _ hbc).1
    have hlap := hu'.1.1 ⟨vtx y.2.1, hbC⟩
    unfold componentLaplacian at hlap
    have hsum := sum_neighborFinset_eq C' ⟨vtx y.2.1, hbC⟩ (fun w => F w - F (vtx y.2.1))
      ((partnersOf y.2.1 P).map vtx).toFinset fun z hz => by
        obtain ⟨b, hb, rfl⟩ := exists_partner_of_adj hz (Or.inl hbU)
        exact mem_toFinset_partners hb
    rw [hpart] at hsum
    have hvac : vtx y.1 ≠ vtx y.2.2 := fun h => hac (vtx_injective h)
    have hadj1 : (openGraph ω').Adj (vtx y.2.1) (vtx y.1) := (hadjq _ hab).symm
    have hadj2 : (openGraph ω').Adj (vtx y.2.1) (vtx y.2.2) := hadjq _ hbc
    simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
      insert_empty_eq] at hsum
    rw [Finset.sum_pair hvac, if_pos hadj1, if_pos hadj2] at hsum
    have hconv : ∑ z ∈ (componentGraph C').neighborFinset ⟨vtx y.2.1, hbC⟩,
        (u' z - u' ⟨vtx y.2.1, hbC⟩) =
        ∑ z ∈ (componentGraph C').neighborFinset ⟨vtx y.2.1, hbC⟩, (F z.val - F (vtx y.2.1)) :=
      Finset.sum_congr rfl fun z _ => by simp only [hF, extend_of_mem u' z.2, extend_of_mem u' hbC]
    rw [hconv, hsum] at hlap
    simp only [hfdef]
    linarith
  -- the increments along the path are constant
  set D := f q0.2 - f q0.1 with hD
  have hDq : ∀ q ∈ zipPairs P, f q.2 - f q.1 = D := fun q hq =>
    incr_eq_of_triples f P hharm q hq q0 hq0
  have htele : f s - f t = ((zipPairs P).length : ℝ) * D := by
    rw [← sum_incr_eq f P t s hhead hlast]
    exact sum_map_eq_length_mul _ D _ hDq
  -- Kirchhoff's law at the terminals
  set T' := surgeryTerminals.filter (· ∈ C'.supp) with hT'
  set v : Vertex 2 → ℝ := fun z => F z - l0 z with hv
  have hsC : vtx s ∈ C'.supp := by
    have := (hinC q1 hq1).2; rwa [hq1s] at this
  have hvts : vtx t ≠ vtx s := fun h => hts (vtx_injective h)
  have hkclT : ∀ r ∈ T', ∑ s' ∈ T', c r s' * (v s' - v r) =
      (if r = vtx t then -D else 0) + (if r = vtx s then D else 0) := by
    intro r hr
    obtain ⟨hrT, hrC⟩ := Finset.mem_filter.1 hr
    have hK := hkcl u' hu' r hrT hrC
    have hsum2 : ∑ s' ∈ surgeryTerminals, c r s' * ((F s' - F r) - (l0 s' - l0 r)) =
        ∑ s' ∈ T', c r s' * (v s' - v r) := by
      rw [hT', Finset.sum_filter_of_ne fun s' hs' hne' =>
        (hsame r hrT s' hs' (left_ne_zero_of_mul hne')).1 hrC]
      exact Finset.sum_congr rfl fun s' _ => by simp only [hv]; ring
    rw [hsum2] at hK
    obtain ⟨a, ha, rfl⟩ := mem_surgeryTerminals.1 hrT
    have haU : vtx a ∉ surgerySites := not_mem_surgerySites_of_mem_terminals hrT
    have hint := sum_neighborFinset_filter_eq C' ⟨vtx a, hrC⟩ (· ∈ surgerySites)
      (fun w => F w - F (vtx a)) ((partnersOf a P).map vtx).toFinset fun z hz hzU => by
        obtain ⟨b, hb, rfl⟩ := exists_partner_of_adj hz (Or.inr hzU)
        exact mem_toFinset_partners hb
    have hconv : ∑ z ∈ ((componentGraph C').neighborFinset ⟨vtx a, hrC⟩).filter
          (fun z => z.val ∈ surgerySites), (u' z - u' ⟨vtx a, hrC⟩) =
        ∑ z ∈ ((componentGraph C').neighborFinset ⟨vtx a, hrC⟩).filter
          (fun z => z.val ∈ surgerySites), (F z.val - F (vtx a)) :=
      Finset.sum_congr rfl fun z _ => by simp only [hF, extend_of_mem u' z.2, extend_of_mem u' hrC]
    rw [hconv, hint] at hK
    by_cases hat : a = t
    · subst hat
      rw [hpt] at hK
      simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
        insert_empty_eq, Finset.sum_singleton] at hK
      have hq0' : (openGraph ω').Adj (vtx a) (vtx q0.2) := by
        have := hadjq q0 hq0; rwa [hq0t] at this
      rw [if_pos ⟨hq0', hq0U⟩] at hK
      rw [if_pos rfl, if_neg hvts]
      have : F (vtx q0.2) - F (vtx a) = D := by simp only [hD, hfdef, hq0t]
      linarith
    by_cases has : a = s
    · subst has
      rw [hps] at hK
      simp only [List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
        insert_empty_eq, Finset.sum_singleton] at hK
      have hq1' : (openGraph ω').Adj (vtx a) (vtx q1.1) := by
        have := (hadjq q1 hq1).symm; rwa [hq1s] at this
      rw [if_pos ⟨hq1', hq1U⟩] at hK
      rw [if_neg (fun h => hts (vtx_injective h).symm), if_pos rfl]
      have h1 := hDq q1 hq1
      simp only [hfdef, hq1s] at h1
      linarith
    · rw [hother a ha hat has] at hK
      simp only [List.map_nil, List.toFinset_nil, Finset.sum_empty, zero_add] at hK
      rw [if_neg fun h => hat (vtx_injective h), if_neg fun h => has (vtx_injective h)]
      linarith
  -- the energy identity
  have htT'' : vtx t ∈ T' := Finset.mem_filter.2 ⟨htT', htC⟩
  have hsT'' : vtx s ∈ T' := Finset.mem_filter.2 ⟨hsT', hsC⟩
  have hen := mul_sq_le_of_kirchhoff T' c v hcs hc0 htT'' hsT'' hvts D hkclT
  have hδ : v (vtx s) - v (vtx t) =
      ((zipPairs P).length : ℝ) * D - (l0 (vtx s) - l0 (vtx t)) := by
    simp only [hv]; simp only [hfdef] at htele; linarith
  have hbound := mul_abs_le_of_energy (hc0 _ _) (Nat.cast_nonneg _) hen hδ
  have hc4 : c (vtx t) (vtx s) ≤ 4 :=
    (Finset.single_le_sum (f := fun s' => c (vtx t) s') (fun s' _ => hc0 _ s') hsT').trans
      (hcsum _)
  have hm : ((zipPairs P).length : ℝ) ≤ 12 := by exact_mod_cast hlen
  -- no rise beyond `L`
  have hDL : |D| ≤ L := by
    rw [abs_le]
    constructor
    · by_contra hlt
      push Not at hlt
      obtain ⟨-, hlC⟩ := hinC ql hql
      have he : vtx ql.2 + e1 = vtx ql.1 := by
        rw [← vtx_add_e1, hqlL]; simp
      apply hno _ (mem_designPairs hx hql).2
      have hb : vtx ql.2 + e1 ∈ C'.supp := by rw [he]; exact (hinC ql hql).1
      refine ⟨h', hlC, hb, ?_, u', hu', ?_⟩
      · show (openGraph ω').Adj (vtx ql.2) (vtx ql.2 + e1)
        rw [he]; exact (hadjq ql hql).symm
      · rw [← extend_of_mem u' hb, ← extend_of_mem u' hlC, he]
        have := hDq ql hql
        simp only [hfdef] at this
        rw [← hF]; linarith
    · by_contra hlt
      push Not at hlt
      obtain ⟨hlC, -⟩ := hinC qr hqr
      have he : vtx qr.1 + e1 = vtx qr.2 := by rw [← vtx_add_e1, hqrR]
      apply hno _ (mem_designPairs hx hqr).1
      have hb : vtx qr.1 + e1 ∈ C'.supp := by rw [he]; exact (hinC qr hqr).2
      refine ⟨h', hlC, hb, ?_, u', hu', ?_⟩
      · show (openGraph ω').Adj (vtx qr.1) (vtx qr.1 + e1)
        rw [he]; exact hadjq qr hqr
      · rw [← extend_of_mem u' hb, ← extend_of_mem u' hlC, he]
        have := hDq qr hqr
        simp only [hfdef] at this
        rw [← hF]; linarith
  have hL0 : 0 ≤ L := (abs_nonneg D).trans hDL
  calc c (vtx t) (vtx s) * |l0 (vtx s) - l0 (vtx t)|
      ≤ (c (vtx t) (vtx s) * ((zipPairs P).length : ℝ) + 1) * |D| := hbound
    _ ≤ (4 * 12 + 1) * L := by
        apply mul_le_mul _ hDL (abs_nonneg _) (by norm_num)
        nlinarith [hc0 (vtx t) (vtx s), (Nat.cast_nonneg (zipPairs P).length : (0 : ℝ) ≤ _)]
    _ = 49 * L := by norm_num

end Network

/-! #### The local surgery step -/

/-- **The local surgery step from the exterior network**: `ExteriorNetworkStep` and
`ModifiedPlaneStep` give `LocalSurgeryStep` with the region `Q_2` minus its corners, the path
designs and `K = 30000`. -/
theorem localSurgeryStep_of_steps {p : unitInterval} (hE : ExteriorNetworkStep p)
    (hM : ModifiedPlaneStep p) : LocalSurgeryStep p := by
  classical
  refine ⟨2, surgerySites, {d | d ∈ designPairs}, 30000, ?_, ?_, by norm_num, ?_⟩
  · rintro e ⟨z, hz, hzU⟩
    refine ⟨z, hz, fun i => ?_⟩
    have hb := siteList_bound _ hzU
    fin_cases i
    · exact hb.1
    · exact hb.2
  · exact (designPairs.toFinset.finite_toSet).subset fun d hd => List.mem_toFinset.2 hd
  intro L hL
  filter_upwards [hE, hM] with ω hEω hMω
  intro hω
  by_contra hno
  push Not at hno
  obtain ⟨c, l0, hnet⟩ := hEω
  have hnet' := hnet
  obtain ⟨hcs, hc0, -, hext⟩ := hnet'
  have hpair : ∀ t ∈ surgeryTerminals, ∀ s ∈ surgeryTerminals,
      c t s * |l0 s - l0 t| ≤ 49 * L := by
    intro t ht s hs
    by_cases hz : c t s * (l0 s - l0 t) = 0
    · have : c t s * |l0 s - l0 t| = 0 := by
        rw [← abs_of_nonneg (hc0 t s), ← abs_mul, hz, abs_zero]
      linarith
    obtain ⟨a, ha, rfl⟩ := mem_surgeryTerminals.1 ht
    obtain ⟨b, hb, rfl⟩ := mem_surgeryTerminals.1 hs
    have hab : a ≠ b := by rintro rfl; simp at hz
    obtain ⟨x, hx, hxab⟩ := designs_cover a ha b hb hab
    rcases hxab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have := pair_bound_of_design hnet hMω hno hx (by rw [h1, h2]; exact hz)
      rwa [h1, h2] at this
    · have hz' : c (vtx x.1) (vtx x.2.1) * (l0 (vtx x.2.1) - l0 (vtx x.1)) ≠ 0 := by
        rw [h1, h2, hcs]
        intro h; apply hz; linarith
      have := pair_bound_of_design hnet hMω hno hx hz'
      rwa [h1, h2, hcs, abs_sub_comm] at this
  obtain ⟨h, ho, u, hu, hgrad⟩ := hω
  obtain ⟨hsame, -, hkcl⟩ := hext ω (fun _ _ => rfl) h
  have hbound := originGradientNorm_le_of_network (uniqueInfiniteComponent h) ho u hu.1.1 c l0
    hcs hc0 hsame (hkcl u hu) hpair
  linarith

/-- **The signed variant of Proposition 3.2** from Proposition 3.2 as printed, the exterior network
of the surgery region and finite energy: `HorizontalIncrementStep p` for `0 < p < 1`. -/
theorem horizontalIncrementStep_of_exteriorNetwork {p : unitInterval} (hp0 : 0 < (p : ℝ))
    (hp1 : (p : ℝ) < 1) (h32 : Rigidity.Section3.NotLipschitzStmt 2 p)
    (hE : ExteriorNetworkStep p) (hM : ModifiedPlaneStep p) : HorizontalIncrementStep p :=
  horizontalIncrementStep_of_localSurgery hp0 hp1 h32 (localSurgeryStep_of_steps hE hM)

/-- Every bond meeting the surgery region meets the cube `Q_2`. -/
theorem meetsSites_surgerySites_bondsNear (e : Bond 2) (he : MeetsSites surgerySites e) :
    e ∈ Rigidity.Steps.S4.bondsNear 2 2 := by
  obtain ⟨z, hz, hzU⟩ := he
  refine ⟨z, hz, fun i => ?_⟩
  have hb := siteList_bound _ hzU
  fin_cases i
  · exact hb.1
  · exact hb.2

/-- Setting the bonds meeting the surgery region according to `F` only reads `F` on the bonds
meeting `Q_2`. -/
theorem modifyNear_inter_bondsNear (F : Set (Bond 2)) (ω : Configuration 2) :
    modifyNear surgerySites (F ∩ Rigidity.Steps.S4.bondsNear 2 2) ω =
      modifyNear surgerySites F ω := by
  classical
  funext e
  by_cases he : MeetsSites surgerySites e
  · simp [modifyNear, he, meetsSites_surgerySites_bondsNear e he]
  · simp [modifyNear, he]

/-- **`ModifiedPlaneStep`** from the uniqueness of the infinite cluster and the existence of the
corrected planes (literature inputs) and finite energy (Lemma 2.1): the modifications of the bonds
meeting the surgery region form a finite family, each mapping null events to null events. -/
theorem modifiedPlaneStep (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hcor : LatticeProb.External.SupercriticalBondCorrectorInput) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1) : ModifiedPlaneStep p := by
  classical
  set μ := latticeBondLaw 2 p
  have hp0 : 0 < (p : ℝ) := lt_trans (hUq.1 2 le_rfl).1 hpc
  set G : Set (Configuration 2) := {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
    ∃ u, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) u} with hGdef
  have hUae : ∀ᵐ ω ∂μ, ω ∈ uniqueInfiniteComponentEvent 2 :=
    (ae_iff_measure_eq (measurableSet_uniqueInfiniteComponentEvent 2).nullMeasurableSet).2
      (by rw [measure_univ]; exact hUq.2 2 le_rfl p hpc hp1)
  have hGae : ∀ᵐ ω ∂μ, ω ∈ G := by
    filter_upwards [hUae, hcor 2 le_rfl p hpc hp1] with ω hω hc
    obtain ⟨v, hv⟩ := (uniqueInfiniteComponent hω).nonempty_supp
    obtain ⟨u, hu, -⟩ := ((hc hω).1 (Pi.single 0 1) ⟨v, hv⟩).exists
    exact ⟨hω, u, hu⟩
  have hGnull : μ {ω | ω ∉ G} = 0 := ae_iff.1 hGae
  rw [ModifiedPlaneStep, ae_iff]
  have hsub : {ω | ¬ ModifiedPlaneAt ω} ⊆ ⋃ F' ∈ (Rigidity.Steps.S4.bondsNear 2 2).powerset,
      modifyNear surgerySites F' ⁻¹' {ω | ω ∉ G} := by
    intro ω hω
    simp only [ModifiedPlaneAt, Set.mem_setOf_eq, not_forall] at hω
    obtain ⟨F, hF⟩ := hω
    refine Set.mem_iUnion₂.2 ⟨F ∩ Rigidity.Steps.S4.bondsNear 2 2, Set.inter_subset_right, ?_⟩
    show modifyNear surgerySites (F ∩ Rigidity.Steps.S4.bondsNear 2 2) ω ∉ G
    rw [modifyNear_inter_bondsNear]
    exact hF
  refine measure_mono_null hsub ((measure_biUnion_null_iff ?_).2 fun F' _ =>
    modifyNear_preimage_null hp0 hp1 meetsSites_surgerySites_bondsNear F' hGnull)
  exact (Rigidity.Steps.S4.finite_bondsNear 2 2).powerset.countable

/-- **The signed variant of Proposition 3.2** from Proposition 3.2 as printed and the exterior
network of the surgery region, with the literature inputs on the uniqueness of the infinite
cluster and the corrected planes: `HorizontalIncrementStep p` for `p_c(2) < p < 1`.
`ExteriorNetworkStep p` is proved from the literature inputs in
`Rigidity/Proofs/S3/ExteriorNetwork.lean` (`Rigidity.Proofs.S3.exteriorNetworkStep`). -/
theorem horizontalIncrementStep_of_exteriorNetwork_inputs
    (hUq : LatticeProb.External.SupercriticalBondUniqueness)
    (hcor : LatticeProb.External.SupercriticalBondCorrectorInput) {p : unitInterval}
    (hpc : criticalProbability 2 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (h32 : Rigidity.Section3.NotLipschitzStmt 2 p) (hE : ExteriorNetworkStep p) :
    HorizontalIncrementStep p :=
  horizontalIncrementStep_of_exteriorNetwork (lt_trans (hUq.1 2 le_rfl).1 hpc) hp1 h32 hE
    (modifiedPlaneStep hUq hcor hpc hp1)

end Rigidity.Steps.S3
