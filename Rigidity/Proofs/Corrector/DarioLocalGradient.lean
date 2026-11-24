import Rigidity.Proofs.Corrector.DarioStepTwoReduce

/-!
# A local bound for the gradients of harmonic functions on the cluster

At scale `R`, the local cluster (`localCluster R ω`) is the set of the points of `B(0, R)` joined to
the boundary of `B(0, 2R)` by an open path inside `B(0, 2R)`; it contains the points of the infinite
cluster in `B(0, R)`, and equals that set unless a finite cluster of radius at least `R` meets
`B(0, R)`. A function is admissible (`LocalAdmissible`) when it is harmonic at the points of the
local cluster whose open neighbours lie in `B(0, R)` and is within `3R` of a constant on the local
cluster. The local gradient bound (`localGrad R ω`) is the supremum of `|h(0) - h(w)|` over the
admissible `h` and the open neighbours `w` of the origin, when the origin is in the local cluster:

* `localGrad_le`: it is at most `6R`;
* `abs_sub_le_localGrad`: it bounds every admissible function along the open edges at the origin;
* `localGrad_eq_of_adj_iff`, `measurable_localGrad`: it depends only on the open edges inside
  `B(0, 2R + 1)`, hence is measurable.

On the event where the local cluster is the infinite cluster in `B(0, R)` and the corrector
oscillates by at most `R` there, the corrected plane of a unit slope is admissible, so `localGrad`
bounds its gradient at the origin; this is the finite-range bound of the gradient of the corrected
plane in the concentration of the weight of the Step 2 sum.
-/

namespace Rigidity.Corrector

open MeasureTheory LatticeProb.Percolation Rigidity.Percolation Rigidity.Proofs.Cluster
  Rigidity.Proofs.Section5 Rigidity.Poincare
open scoped Classical

/-- The local cluster at scale `R`. -/
noncomputable def localCluster (R : ℕ) (ω : Configuration 2) : Finset (Vertex 2) :=
  (supBox 0 R).filter fun y => ∃ w ∈ supBox (0 : Vertex 2) (2 * R),
    (∃ i, ((2 * R : ℕ) : ℤ) ≤ |w i|) ∧ ReachIn ω ↑(supBox (0 : Vertex 2) (2 * R)) y w

/-- The admissible functions at scale `R`. -/
def LocalAdmissible (R : ℕ) (ω : Configuration 2) (h : Vertex 2 → ℝ) : Prop :=
  (∀ y ∈ localCluster R ω, (∀ w, (openGraph ω).Adj y w → w ∈ supBox (0 : Vertex 2) R) →
    openLaplacian ω h y = 0) ∧
  ∃ c : ℝ, ∀ y ∈ localCluster R ω, |h y - c| ≤ 3 * R

/-- The values of `|h(0) - h(w)|` over the admissible `h` and the open neighbours `w` of the
origin, when the origin is in the local cluster. -/
def localGradSet (R : ℕ) (ω : Configuration 2) : Set ℝ :=
  {t | ∃ (h : Vertex 2 → ℝ) (w : Vertex 2), LocalAdmissible R ω h ∧
    (0 : Vertex 2) ∈ localCluster R ω ∧ (openGraph ω).Adj 0 w ∧ t = |h 0 - h w|}

/-- **The local gradient bound at scale `R`.** -/
noncomputable def localGrad (R : ℕ) (ω : Configuration 2) : ℝ := sSup (insert 0 (localGradSet R ω))

theorem mem_supBox_of_adj_zero {ω : Configuration 2} {R : ℕ} (hR : 1 ≤ R) {w : Vertex 2}
    (h : (openGraph ω).Adj 0 w) : w ∈ supBox (0 : Vertex 2) R := by
  rw [mem_supBox]
  intro i
  have := abs_sub_le_one_of_adj h i
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have : |(w i : ℝ) - 0| ≤ R := by
    rw [abs_sub_comm]; simp only [Pi.zero_apply, Int.cast_zero] at this ⊢
    linarith
  exact_mod_cast this

/-- The open neighbours of a point of the local cluster inside `B(0, R)` are in it. -/
theorem mem_localCluster_of_adj {ω : Configuration 2} {R : ℕ} {y w : Vertex 2}
    (hy : y ∈ localCluster R ω) (hw : w ∈ supBox (0 : Vertex 2) R) (h : (openGraph ω).Adj w y) :
    w ∈ localCluster R ω := by
  obtain ⟨-, b, hb, hbd, W, hW⟩ := Finset.mem_filter.1 hy
  have hwR : w ∈ supBox (0 : Vertex 2) (2 * R) := supBox_mono (by omega) hw
  refine Finset.mem_filter.2 ⟨hw, b, hb, hbd, SimpleGraph.Walk.cons h W, fun v hv => ?_⟩
  rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hv
  rcases hv with rfl | hv
  · exact hwR
  · exact hW v hv

theorem abs_le_six_of_mem_localGradSet {ω : Configuration 2} {R : ℕ} {t : ℝ}
    (ht : t ∈ localGradSet R ω) (hR : 1 ≤ R) : t ≤ 6 * R := by
  obtain ⟨h, w, ⟨-, c, hc⟩, h0, hw, rfl⟩ := ht
  have hwK := mem_localCluster_of_adj h0 (mem_supBox_of_adj_zero hR hw) hw.symm
  have a := hc 0 h0
  have b := hc w hwK
  calc |h 0 - h w| ≤ |h 0 - c| + |h w - c| := by
        rw [abs_sub_comm (h w) c]; exact abs_sub_le _ _ _
    _ ≤ 6 * R := by linarith

theorem bddAbove_localGradSet (ω : Configuration 2) {R : ℕ} (hR : 1 ≤ R) :
    BddAbove (insert 0 (localGradSet R ω)) := by
  refine ⟨6 * R, fun t ht => ?_⟩
  rcases ht with rfl | ht
  · positivity
  · exact abs_le_six_of_mem_localGradSet ht hR

theorem localGrad_nonneg (ω : Configuration 2) {R : ℕ} (hR : 1 ≤ R) : 0 ≤ localGrad R ω :=
  le_csSup (bddAbove_localGradSet ω hR) (Set.mem_insert 0 _)

/-- `localGrad R ω ≤ 6R`. -/
theorem localGrad_le (ω : Configuration 2) {R : ℕ} (hR : 1 ≤ R) : localGrad R ω ≤ 6 * R := by
  refine csSup_le (Set.insert_nonempty _ _) fun t ht => ?_
  rcases ht with rfl | ht
  · positivity
  · exact abs_le_six_of_mem_localGradSet ht hR

/-- **The local gradient bound bounds the admissible functions.** -/
theorem abs_sub_le_localGrad {ω : Configuration 2} {R : ℕ} (hR : 1 ≤ R) {h : Vertex 2 → ℝ}
    (hh : LocalAdmissible R ω h) (h0 : (0 : Vertex 2) ∈ localCluster R ω) {w : Vertex 2}
    (hw : (openGraph ω).Adj 0 w) : |h 0 - h w| ≤ localGrad R ω :=
  le_csSup (bddAbove_localGradSet ω hR) (Set.mem_insert_of_mem _ ⟨h, w, hh, h0, hw, rfl⟩)

/-! ### Locality -/

section Locality

variable {ω ω' : Configuration 2} {R : ℕ}
  (hagree : ∀ a ∈ supBox (0 : Vertex 2) (2 * R + 1), ∀ b ∈ supBox (0 : Vertex 2) (2 * R + 1),
    ((openGraph ω').Adj a b ↔ (openGraph ω).Adj a b))
include hagree

theorem localCluster_eq_of_adj_iff : localCluster R ω' = localCluster R ω := by
  have hsub : ∀ a ∈ (↑(supBox (0 : Vertex 2) (2 * R)) : Set (Vertex 2)),
      ∀ b ∈ (↑(supBox (0 : Vertex 2) (2 * R)) : Set (Vertex 2)),
      ((openGraph ω').Adj a b ↔ (openGraph ω).Adj a b) := fun a ha b hb =>
    hagree a (supBox_mono (by omega) ha) b (supBox_mono (by omega) hb)
  unfold localCluster
  refine Finset.filter_congr fun y _ => ?_
  simp only [reachIn_iff_of_adj_iff hsub]

theorem adj_iff_of_mem_supBox {y : Vertex 2} (hy : y ∈ supBox (0 : Vertex 2) (2 * R))
    (w : Vertex 2) :
    ((openGraph ω').Adj y w ↔ (openGraph ω).Adj y w) := by
  by_cases hw : w ∈ supBox (0 : Vertex 2) (2 * R + 1)
  · exact hagree y (supBox_mono (by omega) hy) w hw
  · have key : ∀ η : Configuration 2, ¬ (openGraph η).Adj y w := by
      intro η h
      apply hw
      rw [mem_supBox] at hy ⊢
      intro i
      have := abs_sub_le_one_of_adj h i
      have h1 := hy i
      have h1' : |((y i : ℤ) : ℝ) - 0| ≤ ((2 * R : ℕ) : ℝ) := by exact_mod_cast h1
      have : |((w i : ℤ) : ℝ) - 0| ≤ ((2 * R + 1 : ℕ) : ℝ) := by
        simp only [sub_zero] at h1' ⊢
        push_cast at h1' ⊢
        have t := abs_sub_abs_le_abs_sub ((w i : ℤ) : ℝ) ((y i : ℤ) : ℝ)
        rw [abs_sub_comm] at this
        linarith
      exact_mod_cast this
    exact ⟨fun h => absurd h (key ω'), fun h => absurd h (key ω)⟩

theorem localAdmissible_iff_of_adj_iff (h : Vertex 2 → ℝ) :
    LocalAdmissible R ω' h ↔ LocalAdmissible R ω h := by
  unfold LocalAdmissible
  rw [localCluster_eq_of_adj_iff hagree]
  have hlap : ∀ y ∈ localCluster R ω, openLaplacian ω' h y = openLaplacian ω h y := by
    intro y hy
    have hy' : y ∈ supBox (0 : Vertex 2) (2 * R) :=
      supBox_mono (by omega) (Finset.mem_filter.1 hy).1
    exact GeneralDim.openLaplacian_eq_of_adj_iff (adj_iff_of_mem_supBox hagree hy') h
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun y hy hall => ?_, h2⟩
    have hy' : y ∈ supBox (0 : Vertex 2) (2 * R) :=
      supBox_mono (by omega) (Finset.mem_filter.1 hy).1
    rw [← hlap y hy]
    exact h1 y hy fun w hw => hall w ((adj_iff_of_mem_supBox hagree hy' w).1 hw)
  · rintro ⟨h1, h2⟩
    refine ⟨fun y hy hall => ?_, h2⟩
    have hy' : y ∈ supBox (0 : Vertex 2) (2 * R) :=
      supBox_mono (by omega) (Finset.mem_filter.1 hy).1
    rw [hlap y hy]
    exact h1 y hy fun w hw => hall w ((adj_iff_of_mem_supBox hagree hy' w).2 hw)

/-- **Locality of the local gradient bound.** -/
theorem localGrad_eq_of_adj_iff : localGrad R ω' = localGrad R ω := by
  have h0 : (0 : Vertex 2) ∈ supBox (0 : Vertex 2) (2 * R) := by
    rw [mem_supBox]; intro i; simp
  unfold localGrad localGradSet
  congr 2
  ext t
  simp only [Set.mem_setOf_eq, localAdmissible_iff_of_adj_iff hagree,
    localCluster_eq_of_adj_iff hagree, adj_iff_of_mem_supBox hagree h0]

end Locality

/-- **The local gradient bound is measurable**: it is a function of the open graph induced on
`B(0, 2R + 1)`. -/
theorem measurable_localGrad (R : ℕ) : Measurable (localGrad R) := by
  set S : Set (Vertex 2) := ↑(supBox (0 : Vertex 2) (2 * R + 1)) with hS
  set φ : Configuration 2 → SimpleGraph S := fun ω => (openGraph ω).induce S with hφ
  set F : SimpleGraph S → ℝ := fun g =>
    if hg : ∃ ω : Configuration 2, φ ω = g then localGrad R hg.choose else 0 with hF
  have hloc : ∀ ω, localGrad R ω = F (φ ω) := by
    intro ω
    have hex : ∃ ω' : Configuration 2, φ ω' = φ ω := ⟨ω, rfl⟩
    simp only [hF, dif_pos hex]
    symm
    refine localGrad_eq_of_adj_iff fun a ha b hb => ?_
    have := congrArg (fun g : SimpleGraph S => g.Adj ⟨a, ha⟩ ⟨b, hb⟩) hex.choose_spec
    simpa [hφ] using this
  have hφm : @Measurable _ _ (localGraphSigma S) ⊤ φ := fun s _ => ⟨s, trivial, rfl⟩
  have hle : localGraphSigma S ≤ (inferInstance : MeasurableSpace (Configuration 2)) :=
    (localGraphSigma_le_localEdgeSigma S (Finset.finite_toSet _)).trans
      (GeneralDim.localEdgeSigma_le S)
  have hFm : @Measurable _ _ ⊤ _ F := measurable_from_top (f := F)
  have : Measurable[localGraphSigma S] (localGrad R) := by
    rw [show localGrad R = F ∘ φ from funext hloc]
    exact @Measurable.comp _ _ _ (localGraphSigma S) ⊤ _ F φ hFm hφm
  exact this.mono hle le_rfl

end Rigidity.Corrector
