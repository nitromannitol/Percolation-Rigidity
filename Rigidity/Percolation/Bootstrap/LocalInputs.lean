import Rigidity.Percolation.Bootstrap.ModelBridge
import Rigidity.Percolation.RestrictedReachability
import Rigidity.Proofs.Percolation.SupercriticalUniqueness

/-!
# Local inputs of the static renormalization

Three finite-volume consequences of supercriticality, transferred from the vendored edge-set
library to lattice configurations and to cubes with arbitrary centres.

* The uniqueness zone (S. Martineau, V. Tassion, *Locality of percolation for abelian Cayley
  graphs*, Ann. Probab. 45 (2017), proof of Lemma 3.7): for fixed `k`, with probability close to
  one for all large `n`, the vertices of `c + Q_k` joined inside `c + Q_n` to its shell are joined
  to each other inside `c + Q_n`.
* Large finite sets meet the infinite cluster with probability close to one (Martineau–Tassion,
  Lemma 3.6, in the cardinality form of the vendored library).
* A large cube is joined inside `c + Q_n` to each face orthant of `c + Q_n` with probability close
  to one (G. Grimmett, *Percolation*, 2nd ed., (7.14)–(7.16)).
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open _root_.Percolation.Literature _root_.Percolation.Literature.DCT16

variable {d : ℕ}

/-! ### Transport by translations -/

/-- The configuration moved by the translation by `c`. -/
abbrev translateConfig (c : Vertex d) : Configuration d ≃ᵐ Configuration d :=
  latticeConfigurationEquiv (translateEquiv c) (translateEquiv_dist c)

/-- Translations preserve probabilities. -/
theorem latticeBondLaw_preimage_translateConfig (p : unitInterval) (c : Vertex d)
    (A : Set (Configuration d)) :
    latticeBondLaw d p (translateConfig c ⁻¹' A) = latticeBondLaw d p A :=
  latticeBondLaw_preimage_latticeConfigurationEquiv p _ _ A

/-- Real form of translation invariance. -/
theorem latticeBondLaw_real_preimage_translateConfig (p : unitInterval) (c : Vertex d)
    (A : Set (Configuration d)) :
    (latticeBondLaw d p).real (translateConfig c ⁻¹' A) = (latticeBondLaw d p).real A := by
  rw [measureReal_def, measureReal_def, latticeBondLaw_preimage_translateConfig]

/-- Connections inside a region move with the translation. -/
theorem openIn_reachable_translateConfig_iff (c : Vertex d) (ω : Configuration d)
    (B : Set (Vertex d)) (x y : Vertex d) :
    (openIn (translateConfig c ω) (translateEquiv c '' B)).Reachable (x + c) (y + c) ↔
      (openIn ω B).Reachable x y :=
  openIn_reachable_latticeConfigurationEquiv_iff _ _ ω B x y

/-- Connections inside a translated cube. -/
theorem openIn_cubeAt_reachable_translateConfig_iff (c x₀ : Vertex d) (n : ℕ)
    (ω : Configuration d) (x y : Vertex d) :
    (openIn (translateConfig c ω) (cubeAt (x₀ + c) n)).Reachable (x + c) (y + c) ↔
      (openIn ω (cubeAt x₀ n)).Reachable x y := by
  rw [← image_translate_cubeAt]
  exact openIn_reachable_translateConfig_iff c ω _ x y

/-- Translating a point by `c` puts it in the translated cube exactly when it was in the cube. -/
theorem add_mem_cubeAt_iff (c x₀ x : Vertex d) (n : ℕ) :
    x + c ∈ cubeAt (x₀ + c) n ↔ x ∈ cubeAt x₀ n := by
  simp only [mem_cubeAt, Pi.add_apply, add_sub_add_right_eq_sub]

/-- Translating a point by `c` puts it in the translated shell exactly when it was in the shell. -/
theorem add_mem_cubeShell_iff (c x₀ x : Vertex d) (n : ℕ) :
    x + c ∈ cubeShell (x₀ + c) n ↔ x ∈ cubeShell x₀ n := by
  simp only [cubeShell, Set.mem_setOf_eq, mem_cubeAt, Pi.add_apply, add_sub_add_right_eq_sub]

/-- A vertex joined inside a region to a vertex of the region lies in the region. -/
theorem mem_of_openIn_reachable {ω : Configuration d} {B : Set (Vertex d)} {x v : Vertex d}
    (h : (openIn ω B).Reachable x v) (hv : v ∈ B) : x ∈ B := by
  obtain ⟨w⟩ := h
  cases w with
  | nil => exact hv
  | cons h' _ => exact h'.2.1

/-! ### The uniqueness zone -/

/-- The uniqueness zone at `c`: two vertices of `c + Q_k` that are joined inside `c + Q_n` to the
shell of `c + Q_n` are joined to each other inside `c + Q_n`. -/
def UniqueZone (ω : Configuration d) (c : Vertex d) (k n : ℕ) : Prop :=
  ∀ x ∈ cubeAt c k, ∀ y ∈ cubeAt c k,
    (∃ v ∈ cubeShell c n, (openIn ω (cubeAt c n)).Reachable x v) →
    (∃ w ∈ cubeShell c n, (openIn ω (cubeAt c n)).Reachable y w) →
    (openIn ω (cubeAt c n)).Reachable x y

/-- Reaching the shell of a cube inside it is measurable. -/
theorem measurableSet_reach_cubeShell (c : Vertex d) (n : ℕ) (x : Vertex d) :
    MeasurableSet {ω : Configuration d |
      ∃ v ∈ cubeShell c n, (openIn ω (cubeAt c n)).Reachable x v} := by
  have : {ω : Configuration d | ∃ v ∈ cubeShell c n, (openIn ω (cubeAt c n)).Reachable x v} =
      ⋃ v ∈ cubeShell c n, {ω | (openIn ω (cubeAt c n)).Reachable x v} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun v _ => measurableSet_openIn_reachable _ x v

/-- The uniqueness zone is measurable. -/
theorem measurableSet_uniqueZone (c : Vertex d) (k n : ℕ) :
    MeasurableSet {ω : Configuration d | UniqueZone ω c k n} := by
  have heq : {ω : Configuration d | UniqueZone ω c k n} =
      ⋂ x : Vertex d, ⋂ y : Vertex d,
        ({ω | x ∈ cubeAt c k ∧ y ∈ cubeAt c k ∧
            (∃ v ∈ cubeShell c n, (openIn ω (cubeAt c n)).Reachable x v) ∧
            (∃ w ∈ cubeShell c n, (openIn ω (cubeAt c n)).Reachable y w)}ᶜ ∪
          {ω | (openIn ω (cubeAt c n)).Reachable x y}) := by
    ext ω
    simp only [UniqueZone, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff]
    constructor
    · intro h x y
      by_cases hc : x ∈ cubeAt c k ∧ y ∈ cubeAt c k ∧
          (∃ v ∈ cubeShell c n, (openIn ω (cubeAt c n)).Reachable x v) ∧
          (∃ w ∈ cubeShell c n, (openIn ω (cubeAt c n)).Reachable y w)
      · exact Or.inr (h x hc.1 y hc.2.1 hc.2.2.1 hc.2.2.2)
      · exact Or.inl hc
    · intro h x hx y hy hxv hyw
      rcases h x y with h | h
      · exact absurd ⟨hx, hy, hxv, hyw⟩ h
      · exact h
  rw [heq]
  refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => ?_
  refine MeasurableSet.union (MeasurableSet.compl ?_) (measurableSet_openIn_reachable _ x y)
  simp only [Set.setOf_and]
  exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((measurableSet_reach_cubeShell c n x).inter (measurableSet_reach_cubeShell c n y)))

/-- The vendored uniqueness-zone event is measurable. -/
theorem measurableSet_uniqZone (k n : ℕ) : MeasurableSet (uniqZone (d := d) k n) := by
  have : uniqZone (d := d) k n = ⋂ x ∈ LatticeModels.box d k, ⋂ y ∈ LatticeModels.box d k,
      (toBdry n x ∩ toBdry n y)ᶜ ∪
        openConnIn (↑(LatticeModels.box d n) : Set (LatticeModels.Site d)) x y := by
    ext ω
    simp only [uniqZone, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union, Set.mem_compl_iff,
      Set.mem_inter_iff, not_and]
    refine forall₂_congr fun x _ => forall₂_congr fun y _ => ?_
    tauto
  rw [this]
  exact MeasurableSet.biInter (Finset.countable_toSet _) fun x _ =>
    MeasurableSet.biInter (Finset.countable_toSet _) fun y _ =>
      (((measurableSet_toBdry n x).inter (measurableSet_toBdry n y)).compl).union
        (measurableSet_openConnIn _ x y)

/-- At the origin, the uniqueness zone is the vendored event read on the open-edge set. -/
theorem uniqueZone_zero_iff [NeZero d] (ω : Configuration d) (k n : ℕ) :
    UniqueZone ω 0 k n ↔ edgeConfig d ω ∈ uniqZone k n := by
  have hbox : ∀ m : ℕ, ∀ x : Vertex d, x ∈ LatticeModels.box d m ↔ x ∈ cubeAt 0 m := by
    intro m x
    rw [← Finset.mem_coe, coe_box_eq_cubeAt]
  have hbdry : ∀ x : Vertex d, edgeConfig d ω ∈ toBdry n x ↔
      x ∈ cubeAt 0 n ∧ ∃ v ∈ cubeShell 0 n, (openIn ω (cubeAt 0 n)).Reachable x v := by
    intro x
    change BdryConn n (edgeConfig d ω) x ↔ _
    unfold BdryConn
    constructor
    · rintro ⟨w, hw, hconn⟩
      rw [coe_box_eq_cubeAt] at hconn
      obtain ⟨hx, -, hr⟩ := (edgeConfig_mem_openConnIn_iff ω _ x w).1 hconn
      refine ⟨hx, w, ?_, hr⟩
      rw [← coe_innerBoundary_box_eq_cubeShell]
      exact hw
    · rintro ⟨hx, v, hv, hr⟩
      have hvb : v ∈ cubeAt 0 n := hv.1
      refine ⟨v, ?_, ?_⟩
      · rw [← Finset.mem_coe, coe_innerBoundary_box_eq_cubeShell]
        exact hv
      · rw [coe_box_eq_cubeAt]
        exact (edgeConfig_mem_openConnIn_iff ω _ x v).2 ⟨hx, hvb, hr⟩
  constructor
  · intro h x hx y hy hxb hyb
    rw [hbdry] at hxb hyb
    rw [coe_box_eq_cubeAt, edgeConfig_mem_openConnIn_iff]
    exact ⟨hxb.1, hyb.1, h x ((hbox k x).1 hx) y ((hbox k y).1 hy) hxb.2 hyb.2⟩
  · intro h x hx y hy hxv hyw
    have hxn : x ∈ cubeAt 0 n := by
      obtain ⟨v, hv, hr⟩ := hxv
      exact mem_of_openIn_reachable hr hv.1
    have hyn : y ∈ cubeAt 0 n := by
      obtain ⟨w, hw, hr⟩ := hyw
      exact mem_of_openIn_reachable hr hw.1
    have := h x ((hbox k x).2 hx) y ((hbox k y).2 hy) ((hbdry x).2 ⟨hxn, hxv⟩)
      ((hbdry y).2 ⟨hyn, hyw⟩)
    rw [coe_box_eq_cubeAt, edgeConfig_mem_openConnIn_iff] at this
    exact this.2.2

/-- The uniqueness zone at `x₀ + c` is the translate of the uniqueness zone at `x₀`. -/
theorem uniqueZone_translate_iff (ω : Configuration d) (c x₀ : Vertex d) (k n : ℕ) :
    UniqueZone (translateConfig c ω) (x₀ + c) k n ↔ UniqueZone ω x₀ k n := by
  constructor
  · intro h x hx y hy hxv hyw
    have := h (x + c) ((add_mem_cubeAt_iff c x₀ x k).2 hx)
      (y + c) ((add_mem_cubeAt_iff c x₀ y k).2 hy)
      (by
        obtain ⟨v, hv, hr⟩ := hxv
        exact ⟨v + c, (add_mem_cubeShell_iff c x₀ v n).2 hv,
          (openIn_cubeAt_reachable_translateConfig_iff c x₀ n ω x v).2 hr⟩)
      (by
        obtain ⟨w, hw, hr⟩ := hyw
        exact ⟨w + c, (add_mem_cubeShell_iff c x₀ w n).2 hw,
          (openIn_cubeAt_reachable_translateConfig_iff c x₀ n ω y w).2 hr⟩)
    exact (openIn_cubeAt_reachable_translateConfig_iff c x₀ n ω x y).1 this
  · intro h x hx y hy hxv hyw
    have ex : ∀ z : Vertex d, z = (z - c) + c := fun z => (sub_add_cancel z c).symm
    rw [ex x] at hx hxv ⊢
    rw [ex y] at hy hyw ⊢
    have key := h (x - c) ((add_mem_cubeAt_iff c x₀ _ k).1 hx) (y - c)
      ((add_mem_cubeAt_iff c x₀ _ k).1 hy)
      (by
        obtain ⟨v, hv, hr⟩ := hxv
        rw [ex v] at hv hr
        exact ⟨v - c, (add_mem_cubeShell_iff c x₀ _ n).1 hv,
          (openIn_cubeAt_reachable_translateConfig_iff c x₀ n ω _ _).1 hr⟩)
      (by
        obtain ⟨w, hw, hr⟩ := hyw
        rw [ex w] at hw hr
        exact ⟨w - c, (add_mem_cubeShell_iff c x₀ _ n).1 hw,
          (openIn_cubeAt_reachable_translateConfig_iff c x₀ n ω _ _).1 hr⟩)
    exact (openIn_cubeAt_reachable_translateConfig_iff c x₀ n ω _ _).2 key

/-- **Uniqueness zone.** For every `k` and `η > 0` there is `n₀` such that for all `n ≥ n₀`
and every centre `c`, the uniqueness zone at `c` has probability above `1 - η`. -/
theorem exists_uniqueZone_prob [NeZero d] (p : unitInterval) (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∀ c : Vertex d,
      1 - η < (latticeBondLaw d p).real {ω | UniqueZone ω c k n} := by
  obtain ⟨n₀, hn₀⟩ := exists_forall_le_lt_real_uniqZone (d := d) p k hη
  refine ⟨n₀, fun n hn c => ?_⟩
  have h0 : {ω : Configuration d | UniqueZone ω 0 k n} = edgeConfig d ⁻¹' uniqZone k n := by
    ext ω
    exact uniqueZone_zero_iff ω k n
  have htr : translateConfig c ⁻¹' {ω : Configuration d | UniqueZone ω c k n} =
      {ω | UniqueZone ω 0 k n} := by
    ext ω
    have := uniqueZone_translate_iff ω c 0 k n
    rw [zero_add] at this
    exact this
  rw [← latticeBondLaw_real_preimage_translateConfig p c, htr, h0,
    latticeBondLaw_real_preimage_edgeConfig p (measurableSet_uniqZone k n)]
  exact hn₀ n hn

end Rigidity.Percolation
