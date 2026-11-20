import Rigidity.Percolation.Bootstrap.LocalInputs
import Rigidity.Percolation.SlabCrossings

/-!
# Seeds reach the face orthants of large cubes

A *seed* at `s` of radius `u` is a set containing a lattice path from `s` to the shell of
`s + Q_u` inside `s + Q_u`. Above criticality and below one, for every `η > 0` there are `u` and
`n₁` such that for all `n ≥ n₁` every seed at `c` of radius `u` is joined inside `c + Q_n` to each
face orthant of `c + Q_n` with probability above `1 - η`.

The proof combines three inputs: a large cube is joined to each face orthant (G. Grimmett,
*Percolation*, 2nd ed., (7.14)–(7.16)); a seed path has many vertices and so meets the infinite
cluster (S. Martineau, V. Tassion, Ann. Probab. 45 (2017), Lemma 3.6); and the uniqueness zone
(ibid., proof of Lemma 3.7) joins the two clusters, which both cross a large shell. This is the
seed-to-box estimate of D. Contreras, *Percolation on graphs of polynomial growth*, ETH Zürich
dissertation (2022), Lemma 2.3.2, with every face orthant as a target.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External
open _root_.Percolation.Literature _root_.Percolation.Literature.DCT16

variable {d : ℕ}

/-! ### Exits through shells -/

/-- An open walk from a vertex of a cube to a vertex outside it passes through the shell of the
cube; its part up to the first such vertex stays inside the cube. -/
theorem exists_cubeShell_of_walk {ω : Configuration d} {C : Set (Vertex d)} {c : Vertex d}
    {N : ℕ} : ∀ {x y : Vertex d} (w : (openIn ω C).Walk x y), x ∈ cubeAt c N →
      y ∉ cubeAt c N →
      ∃ v ∈ w.support, v ∈ cubeShell c N ∧ (openIn ω (cubeAt c N)).Reachable x v
  | _, _, .nil, hx, hy => absurd hx hy
  | x, _, .cons (v := z) h w, hx, hy => by
    by_cases hsh : ∃ i, |x i - c i| = N
    · exact ⟨x, List.mem_cons_self .., ⟨hx, hsh⟩, SimpleGraph.Reachable.refl _⟩
    · push Not at hsh
      have hadj : (nearestNeighborGraph d).Adj x z := ((openGraph_adj_iff ω x z).1 h.1).1
      have hz : z ∈ cubeAt c N := fun i => by
        have h1 := abs_sub_le_one_of_nearestNeighbor_adj hadj i
        have h2 : |x i - c i| < N := lt_of_le_of_ne (hx i) (hsh i)
        have h3 : |z i - c i| ≤ |z i - x i| + |x i - c i| := by
          have := abs_sub_le (z i) (x i) (c i)
          linarith
        rw [abs_sub_comm] at h1
        omega
      obtain ⟨v, hv, hvs, hr⟩ := exists_cubeShell_of_walk w hz hy
      exact ⟨v, List.mem_cons_of_mem _ hv, hvs,
        (SimpleGraph.Adj.reachable (show (openIn ω (cubeAt c N)).Adj _ z from ⟨h.1, hx, hz⟩)).trans hr⟩

/-- A vertex of a cube joined inside a region to a vertex outside the cube is joined inside the
cube to its shell. -/
theorem exists_cubeShell_of_reachable {ω : Configuration d} {C : Set (Vertex d)} {c x y : Vertex d}
    {N : ℕ} (h : (openIn ω C).Reachable x y) (hx : x ∈ cubeAt c N) (hy : y ∉ cubeAt c N) :
    ∃ v ∈ cubeShell c N, (openIn ω (cubeAt c N)).Reachable x v := by
  obtain ⟨w⟩ := h
  obtain ⟨v, -, hv, hr⟩ := exists_cubeShell_of_walk w hx hy
  exact ⟨v, hv, hr⟩

/-- A vertex of a cube in an infinite open cluster is joined inside the cube to its shell. -/
theorem exists_cubeShell_of_infinite {ω : Configuration d} {c x : Vertex d} {N : ℕ}
    (hinf : ω ∈ infiniteComponentEvent x) (hx : x ∈ cubeAt c N) :
    ∃ v ∈ cubeShell c N, (openIn ω (cubeAt c N)).Reachable x v := by
  have hfin : (cubeAt c N).Finite := by
    have : cubeAt c N = (translateEquiv c) '' ((LatticeModels.box d N : Finset (Vertex d)) :
        Set (Vertex d)) := by
      rw [coe_box_eq_cubeAt, image_translate_cubeAt, zero_add]
    rw [this]
    exact (Finset.finite_toSet _).image _
  obtain ⟨y, hy, hxy⟩ := (mem_infiniteComponentEvent_iff ω x).1 hinf hfin.toFinset
  have hyC : y ∉ cubeAt c N := fun h => hy (hfin.mem_toFinset.2 h)
  have hr : (openIn ω Set.univ).Reachable x y := by
    apply hxy.mono
    intro a b hab
    exact ⟨hab, trivial, trivial⟩
  exact exists_cubeShell_of_reachable hr hx hyC

/-! ### Seeds -/

/-- `S` contains `s` and a lattice path from `s` to the shell of `s + Q_u` inside `s + Q_u`. -/
def HasSeedPath (S : Set (Vertex d)) (s : Vertex d) (u : ℕ) : Prop :=
  s ∈ S ∧ ∃ v ∈ cubeShell s u, (openIn (allOpen d) (S ∩ cubeAt s u)).Reachable s v

/-- Seeds are monotone in the set. -/
theorem HasSeedPath.mono {S T : Set (Vertex d)} {s : Vertex d} {u : ℕ} (h : HasSeedPath S s u)
    (hST : S ⊆ T) : HasSeedPath T s u := by
  obtain ⟨hs, v, hv, hr⟩ := h
  exact ⟨hST hs, v, hv, reachable_openIn_mono (Set.inter_subset_inter_left _ hST) hr⟩

/-- Shells of distinct radii are disjoint. -/
theorem cubeShell_injective_radius {c v : Vertex d} {r r' : ℕ} (hv : v ∈ cubeShell c r)
    (hv' : v ∈ cubeShell c r') : r = r' := by
  obtain ⟨hc, i, hi⟩ := hv
  obtain ⟨hc', j, hj⟩ := hv'
  have h1 : (r : ℤ) ≤ r' := hi ▸ hc' i
  have h2 : (r' : ℤ) ≤ r := hj ▸ hc j
  exact_mod_cast le_antisymm h1 h2

/-- The vertices of a walk inside a region starting in the region lie in the region. -/
theorem support_subset_of_walk_openIn {ω : Configuration d} {B : Set (Vertex d)} :
    ∀ {x y : Vertex d} (w : (openIn ω B).Walk x y), x ∈ B → ∀ z ∈ w.support, z ∈ B
  | _, _, .nil, hx, z, hz => by
    rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    exact hz ▸ hx
  | _, _, .cons h w, hx, z, hz => by
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · exact support_subset_of_walk_openIn w h.2.2 z hz

/-- A seed path of radius `u` has at least `u + 1` vertices, all in the seed and in the cube. -/
theorem HasSeedPath.exists_finset {S : Set (Vertex d)} {s : Vertex d} {u : ℕ}
    (h : HasSeedPath S s u) :
    ∃ T : Finset (Vertex d), (↑T : Set (Vertex d)) ⊆ S ∩ cubeAt s u ∧ u + 1 ≤ T.card := by
  classical
  obtain ⟨hs, v, hv, ⟨w⟩⟩ := h
  have hsC : s ∈ S ∩ cubeAt s u := ⟨hs, fun i => by simp⟩
  have hsupp := support_subset_of_walk_openIn w hsC
  refine ⟨w.support.toFinset, fun z hz => hsupp z (List.mem_toFinset.1 hz), ?_⟩
  have hshell : ∀ r ∈ Finset.range (u + 1), ∃ z ∈ w.support, z ∈ cubeShell s r := by
    intro r hr
    rw [Finset.mem_range] at hr
    rcases Nat.lt_succ_iff_lt_or_eq.1 hr with hr | rfl
    · have hvout : v ∉ cubeAt s r := by
        obtain ⟨-, i, hi⟩ := hv
        intro hvr
        have := hvr i
        rw [hi] at this
        omega
      obtain ⟨z, hz, hzs, -⟩ := exists_cubeShell_of_walk w (c := s) (N := r)
        (fun i => by simp) hvout
      exact ⟨z, hz, hzs⟩
    · exact ⟨v, w.end_mem_support, hv⟩
  choose! f hf using hshell
  have hcard := Finset.card_le_card_of_injOn f
    (fun r hr => List.mem_toFinset.2 (hf r hr).1)
    (fun r hr r' hr' heq => cubeShell_injective_radius (hf r hr).2 (heq ▸ (hf r' hr').2))
  simpa using hcard

/-! ### Connections between regions -/

/-- Connections between two regions inside a third are measurable. -/
theorem measurableSet_connectsRegions (B L R : Set (Vertex d)) :
    MeasurableSet {ω : Configuration d | ConnectsRegions ω B L R} := by
  have : {ω : Configuration d | ConnectsRegions ω B L R} =
      ⋃ x ∈ B ∩ L, ⋃ y ∈ B ∩ R, {ω | (openIn ω B).Reachable x y} := by
    ext ω
    simp only [ConnectsRegions, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff,
      exists_prop]
    constructor
    · rintro ⟨x, hxB, hxL, y, hyB, hyR, h⟩
      exact ⟨x, ⟨hxB, hxL⟩, y, ⟨hyB, hyR⟩, h⟩
    · rintro ⟨x, ⟨hxB, hxL⟩, y, ⟨hyB, hyR⟩, h⟩
      exact ⟨x, hxB, hxL, y, hyB, hyR, h⟩
  rw [this]
  exact MeasurableSet.biUnion (Set.to_countable _) fun x _ =>
    MeasurableSet.biUnion (Set.to_countable _) fun y _ => measurableSet_openIn_reachable B x y

/-- Translations carry connections between regions to connections between their translates. -/
theorem connectsRegions_translateConfig_iff (z : Vertex d) (ω : Configuration d)
    (B L R : Set (Vertex d)) :
    ConnectsRegions (translateConfig z ω) (translateEquiv z '' B) (translateEquiv z '' L)
        (translateEquiv z '' R) ↔ ConnectsRegions ω B L R := by
  have hinj := (translateEquiv z).injective
  constructor
  · rintro ⟨x', ⟨x, hxB, rfl⟩, hxL, y', ⟨y, hyB, rfl⟩, hyR, h⟩
    exact ⟨x, hxB, hinj.mem_set_image.1 hxL, y, hyB, hinj.mem_set_image.1 hyR,
      (openIn_reachable_translateConfig_iff z ω B x y).1 h⟩
  · rintro ⟨x, hxB, hxL, y, hyB, hyR, h⟩
    exact ⟨_, ⟨x, hxB, rfl⟩, ⟨x, hxL, rfl⟩, _, ⟨y, hyB, rfl⟩, ⟨y, hyR, rfl⟩,
      (openIn_reachable_translateConfig_iff z ω B x y).2 h⟩

/-! ### Face orthants -/

/-- The face orthant of `c + Q_n` on the face `τ_a (x_a - c_a) = n` whose other coordinates
satisfy `τ_j (x_j - c_j) ≥ 0`. -/
def faceOrthant (c : Vertex d) (a : Fin d) (τ : Fin d → ℤˣ) (n : ℕ) : Set (Vertex d) :=
  {x | x ∈ cubeAt c n ∧ (τ a : ℤ) * (x a - c a) = n ∧ ∀ j, j ≠ a → 0 ≤ (τ j : ℤ) * (x j - c j)}

/-- The vendored face orthant is the face orthant at the origin. -/
theorem coe_orthantFace_eq (a : Fin d) (τ : Fin d → ℤˣ) (n : ℕ) :
    ((orthantFace a τ n : Finset (Vertex d)) : Set (Vertex d)) = faceOrthant 0 a τ n := by
  ext x
  rw [Finset.mem_coe, mem_orthantFace, ← Finset.mem_coe (s := LatticeModels.box d n),
    coe_box_eq_cubeAt]
  simp only [faceOrthant, Set.mem_setOf_eq, Pi.zero_apply, sub_zero]

/-- Translating a face orthant moves its centre. -/
theorem image_translate_faceOrthant (z c : Vertex d) (a : Fin d) (τ : Fin d → ℤˣ) (n : ℕ) :
    translateEquiv z '' faceOrthant c a τ n = faceOrthant (c + z) a τ n := by
  ext y
  constructor
  · rintro ⟨x, ⟨hx, ha, hj⟩, rfl⟩
    refine ⟨fun i => ?_, ?_, fun j hjne => ?_⟩
    · simpa [translateEquiv, latticeVertexTranslation] using hx i
    · simpa [translateEquiv, latticeVertexTranslation] using ha
    · simpa [translateEquiv, latticeVertexTranslation] using hj j hjne
  · rintro ⟨hy, ha, hj⟩
    refine ⟨y - z, ⟨fun i => ?_, ?_, fun j hjne => ?_⟩,
      by simp [translateEquiv, latticeVertexTranslation]⟩
    · have := hy i
      simp only [Pi.add_apply] at this
      simpa [sub_sub, add_comm] using this
    · simp only [Pi.add_apply] at ha
      simpa [sub_sub, add_comm] using ha
    · have := hj j hjne
      simp only [Pi.add_apply] at this
      simpa [sub_sub, add_comm] using this

/-- A vertex of a face orthant of `c + Q_n` is at distance `n` from `c` in the face direction. -/
theorem abs_sub_eq_of_mem_faceOrthant {c x : Vertex d} {a : Fin d} {τ : Fin d → ℤˣ} {n : ℕ}
    (hx : x ∈ faceOrthant c a τ n) : |x a - c a| = n := by
  obtain ⟨-, ha, -⟩ := hx
  have hτ : |(τ a : ℤ)| = 1 := by
    rcases Int.units_eq_one_or (τ a) with h | h <;> simp [h]
  calc |x a - c a| = |(τ a : ℤ)| * |x a - c a| := by rw [hτ, one_mul]
    _ = |(τ a : ℤ) * (x a - c a)| := (abs_mul _ _).symm
    _ = n := by rw [ha]; simp

/-- **A large cube is joined to every face orthant** of a much larger cube, at every centre. -/
theorem exists_link_faceOrthant_prob [NeZero d] (p : unitInterval)
    (hθ : 0 < LatticeProb.Percolation.theta d p) (hp1 : (p : ℝ) < 1) {η : ℝ} (hη : 0 < η)
    (k₀ : ℕ) :
    ∃ k : ℕ, k₀ ≤ k ∧ ∃ n₁ : ℕ, k < n₁ ∧ ∀ n, n₁ ≤ n → ∀ (c : Vertex d) (a : Fin d)
      (τ : Fin d → ℤˣ), 1 - η < (latticeBondLaw d p).real
        {ω | ConnectsRegions ω (cubeAt c n) (cubeAt c k) (faceOrthant c a τ n)} := by
  rw [theta_eq] at hθ
  obtain ⟨k, hk, n₁, hkn, h⟩ := exists_forall_lt_real_linked_orthantFace p hθ hp1 hη k₀
  refine ⟨k, hk, n₁, hkn, fun n hn c a τ => ?_⟩
  have h0 : {ω : Configuration d | ConnectsRegions ω (cubeAt 0 n) (cubeAt 0 k)
      (faceOrthant 0 a τ n)} =
      edgeConfig d ⁻¹' linkEvent (LatticeModels.box d k) (orthantFace a τ n) n := by
    ext ω
    simp only [Set.mem_preimage, linkEvent, Set.mem_setOf_eq, ConnectsRegions]
    rw [← coe_box_eq_cubeAt k, ← coe_box_eq_cubeAt n, ← coe_orthantFace_eq]
    constructor
    · rintro ⟨x, -, hxk, y, -, hyR, hr⟩
      exact ⟨x, hxk, y, hyR, (edgeConfig_mem_openConnIn_iff ω _ x y).2
        ⟨mem_of_openIn_reachable hr (by
          rw [coe_box_eq_cubeAt]
          rw [coe_orthantFace_eq] at hyR
          exact hyR.1), by
          rw [coe_box_eq_cubeAt]
          rw [coe_orthantFace_eq] at hyR
          exact hyR.1, hr⟩⟩
    · rintro ⟨x, hxk, y, hyR, hconn⟩
      obtain ⟨hx, hy, hr⟩ := (edgeConfig_mem_openConnIn_iff ω _ x y).1 hconn
      exact ⟨x, hx, hxk, y, hy, hyR, hr⟩
  have hmeas : MeasurableSet (linkEvent (LatticeModels.box d k) (orthantFace a τ n) n) := by
    have : linkEvent (LatticeModels.box d k) (orthantFace a τ n) n =
        ⋃ y ∈ LatticeModels.box d k, ⋃ x ∈ orthantFace a τ n,
          openConnIn (↑(LatticeModels.box d n) : Set (LatticeModels.Site d)) y x := by
      ext ω
      simp only [linkEvent, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    rw [this]
    exact MeasurableSet.biUnion (Finset.countable_toSet _) fun y _ =>
      MeasurableSet.biUnion (Finset.countable_toSet _) fun x _ => measurableSet_openConnIn _ y x
  have htr : translateConfig c ⁻¹' {ω : Configuration d | ConnectsRegions ω (cubeAt c n)
      (cubeAt c k) (faceOrthant c a τ n)} =
      {ω | ConnectsRegions ω (cubeAt 0 n) (cubeAt 0 k) (faceOrthant 0 a τ n)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    have := connectsRegions_translateConfig_iff c ω (cubeAt 0 n) (cubeAt 0 k)
      (faceOrthant 0 a τ n)
    rw [image_translate_cubeAt, image_translate_cubeAt, image_translate_faceOrthant,
      zero_add] at this
    exact this
  rw [← latticeBondLaw_real_preimage_translateConfig p c, htr, h0,
    latticeBondLaw_real_preimage_edgeConfig p hmeas]
  exact h n hn a τ

/-! ### Large sets meet the infinite cluster -/

/-- **Large finite sets meet the infinite cluster** with probability close to one. -/
theorem exists_card_infinite_prob (p : unitInterval)
    (hθ : 0 < LatticeProb.Percolation.theta d p) {η : ℝ} (hη : 0 < η) :
    ∃ m₀ : ℕ, ∀ T : Finset (Vertex d), m₀ ≤ T.card →
      1 - η < (latticeBondLaw d p).real {ω | ∃ y ∈ T, ω ∈ infiniteComponentEvent y} := by
  rw [theta_eq] at hθ
  obtain ⟨m₀, h⟩ := exists_card_le_imp_lt_real_exists_percolatesAt p hθ hη
  refine ⟨m₀, fun T hT => ?_⟩
  have h0 : {ω : Configuration d | ∃ y ∈ T, ω ∈ infiniteComponentEvent y} =
      edgeConfig d ⁻¹' {ω | ∃ y ∈ T, ω ∈ percolatesAt y} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    exact exists_congr fun y => and_congr_right fun _ => infinite_event_iff d ω y
  have hmeas : MeasurableSet {ω : BondConfig (Vertex d) | ∃ y ∈ T, ω ∈ percolatesAt y} := by
    have : {ω : BondConfig (Vertex d) | ∃ y ∈ T, ω ∈ percolatesAt y} =
        ⋃ y ∈ T, percolatesAt y := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    rw [this]
    exact MeasurableSet.biUnion (Finset.countable_toSet _) fun y _ =>
      measurableSet_percolatesAt_holds y
  rw [h0, latticeBondLaw_real_preimage_edgeConfig p hmeas]
  exact h T hT

/-! ### Seeds reach face orthants -/

/-- Cubes with a common centre are nested. -/
theorem cubeAt_mono {c : Vertex d} {m n : ℕ} (h : m ≤ n) : cubeAt c m ⊆ cubeAt c n :=
  fun _ hx i => (hx i).trans (by exact_mod_cast h)

/-- The probability of an intersection is at least the sum of the probabilities minus one. -/
theorem measureReal_add_sub_one_le_inter {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (A : Set Ω) {B : Set Ω} (hB : MeasurableSet B) :
    μ.real A + μ.real B - 1 ≤ μ.real (A ∩ B) := by
  have h := measureReal_union_add_inter (s := A) hB (μ := μ)
  have h1 : μ.real (A ∪ B) ≤ 1 := measureReal_le_one
  linarith

/-- **Seeds reach face orthants.** Above criticality and below one, for every `η > 0` there are
`u < n₁` such that for every `n ≥ n₁`, every centre `c`, every face orthant of `c + Q_n` and
every seed `S` at `c` of radius `u`, the seed is joined inside `c + Q_n` to the face orthant with
probability above `1 - η`. -/
theorem exists_seed_faceOrthant_prob [NeZero d] (p : unitInterval)
    (hθ : 0 < LatticeProb.Percolation.theta d p) (hp1 : (p : ℝ) < 1) {η : ℝ} (hη : 0 < η) :
    ∃ u n₁ : ℕ, u < n₁ ∧ ∀ n, n₁ ≤ n → ∀ (c : Vertex d) (a : Fin d) (τ : Fin d → ℤˣ)
      (S : Set (Vertex d)), HasSeedPath S c u →
        1 - η < (latticeBondLaw d p).real
          {ω | ConnectsRegions ω (cubeAt c n) S (faceOrthant c a τ n)} := by
  have hη3 : 0 < η / 3 := by positivity
  obtain ⟨m₀, hm₀⟩ := exists_card_infinite_prob p hθ hη3
  obtain ⟨k, -, n₁', -, hlink⟩ := exists_link_faceOrthant_prob p hθ hp1 hη3 0
  obtain ⟨N₀, hN₀⟩ := exists_uniqueZone_prob (d := d) p (max k m₀) hη3
  refine ⟨max k m₀, max n₁' (max N₀ (max k m₀ + 1) + 1), by omega,
    fun n hn c a τ S hS => ?_⟩
  set u := max k m₀ with hu
  set N := max N₀ (u + 1) with hN
  obtain ⟨T, hTS, hTcard⟩ := hS.exists_finset
  have hT : m₀ ≤ T.card := by omega
  have hkN : k ≤ N := by omega
  have huN : u ≤ N := by omega
  have hNn : N < n := by omega
  set E1 := {ω : Configuration d | ConnectsRegions ω (cubeAt c n) (cubeAt c k)
    (faceOrthant c a τ n)} with hE1
  set E2 := {ω : Configuration d | ∃ y ∈ T, ω ∈ infiniteComponentEvent y} with hE2
  set E3 := {ω : Configuration d | UniqueZone ω c u N} with hE3
  have h1 : 1 - η / 3 < (latticeBondLaw d p).real E1 := hlink n (by omega) c a τ
  have h2 : 1 - η / 3 < (latticeBondLaw d p).real E2 := hm₀ T hT
  have h3 : 1 - η / 3 < (latticeBondLaw d p).real E3 := hN₀ N (le_max_left _ _) c
  have hm2 : MeasurableSet E2 := by
    have : E2 = ⋃ y ∈ T, infiniteComponentEvent y := by
      ext ω
      simp only [hE2, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    rw [this]
    exact MeasurableSet.biUnion (Finset.countable_toSet _) fun y _ =>
      measurableSet_infiniteComponentEvent y
  have hm3 : MeasurableSet E3 := measurableSet_uniqueZone c u N
  have hsub : E1 ∩ E2 ∩ E3 ⊆
      {ω | ConnectsRegions ω (cubeAt c n) S (faceOrthant c a τ n)} := by
    rintro ω ⟨⟨⟨z, hzn, hzk, w, hwn, hwR, hzw⟩, ⟨y, hyT, hyinf⟩⟩, hU⟩
    have hyS : y ∈ S ∩ cubeAt c u := hTS hyT
    have hzN : z ∈ cubeAt c N := cubeAt_mono hkN hzk
    have hwout : w ∉ cubeAt c N := by
      intro hw
      have h1 := hw a
      rw [abs_sub_eq_of_mem_faceOrthant hwR] at h1
      have : (n : ℤ) ≤ N := h1
      omega
    obtain ⟨v, hv, hzv⟩ := exists_cubeShell_of_reachable hzw hzN hwout
    obtain ⟨v', hv', hyv⟩ := exists_cubeShell_of_infinite hyinf (cubeAt_mono huN hyS.2)
    have hyz : (openIn ω (cubeAt c N)).Reachable y z :=
      hU y hyS.2 z (cubeAt_mono (le_max_left k m₀) hzk) ⟨v', hv', hyv⟩ ⟨v, hv, hzv⟩
    exact ⟨y, cubeAt_mono (by omega) hyS.2, hyS.1, w, hwn, hwR,
      (reachable_openIn_mono (cubeAt_mono hNn.le) hyz).trans hzw⟩
  calc 1 - η < (latticeBondLaw d p).real E1 + (latticeBondLaw d p).real E2 +
        (latticeBondLaw d p).real E3 - 2 := by linarith
    _ ≤ (latticeBondLaw d p).real (E1 ∩ E2) + (latticeBondLaw d p).real E3 - 1 := by
        linarith [measureReal_add_sub_one_le_inter (latticeBondLaw d p) E1 hm2]
    _ ≤ (latticeBondLaw d p).real (E1 ∩ E2 ∩ E3) :=
        measureReal_add_sub_one_le_inter (latticeBondLaw d p) (E1 ∩ E2) hm3
    _ ≤ _ := measureReal_mono hsub

end Rigidity.Percolation
