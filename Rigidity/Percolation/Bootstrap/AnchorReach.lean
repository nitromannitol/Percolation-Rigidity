import Rigidity.Percolation.Bootstrap.Geometry

/-!
# Left seeds reach the anchors of the subregions

Above criticality, a left seed of scale `3m'` is joined inside the left exploration region to the
left anchor of each subregion `±9m' e_b + Q_{6m'}` with probability close to one, uniformly in
`m'` large and in the seed. The seed path first reaches a cube of radius `w = ⌊m'/16⌋` next to it
(seed-to-face-orthant estimate), and this cube is then moved by steps of length `w` towards the
anchor (navigation), raising the level by a small amount at each step. This is the directional
seed-to-box estimate of D. Contreras, *Percolation on graphs of polynomial growth*, ETH Zürich
dissertation (2022), Lemma 2.3.5, in the form used by the bootstrap.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory Rigidity.External

variable {d : ℕ}

/-- Coordinates of the offset vector. -/
theorem offsetVec_apply (b j : Fin d) (k : ℤ) :
    offsetVec b k j = if j = b then k else 0 := by
  classical
  simp only [offsetVec, Pi.single_apply]

/-- The centre of the first cube of the route from `s`. -/
def routeStart (a : Fin d) (s : Vertex d) (w : ℕ) : Vertex d :=
  fun j => if j = a then s a + 2 * w else s j + w

/-- The destination of the route: `-5m' e_a + σ 9m' e_b`. -/
def routeTarget (a b : Fin d) (sg : ℤˣ) (m' : ℕ) : Vertex d :=
  fun j => if j = a then -(5 * m' : ℤ) else if j = b then (sg : ℤ) * (9 * m' : ℕ) else 0

/-- The centres between the start and the destination, coordinate by coordinate. -/
def routeSafe (c₁ t : Vertex d) : Set (Vertex d) :=
  {c | ∀ j, min (c₁ j) (t j) ≤ c j ∧ c j ≤ max (c₁ j) (t j)}

/-- Steps towards the destination stay between the start and the destination. -/
theorem stepToward_mem_routeSafe {c₁ t c : Vertex d} (hc : c ∈ routeSafe c₁ t) {w : ℕ}
    (j : Fin d) (hj : (w : ℤ) ≤ |t j - c j|) : stepToward t c w j ∈ routeSafe c₁ t := by
  intro i
  by_cases hij : i = j
  · subst hij
    simp only [stepToward, Function.update_self, signUnit]
    have hci := hc i
    split_ifs with hs
    · simp only [Units.val_one, one_mul]
      rw [abs_of_nonneg hs] at hj
      constructor
      · have := hci.1
        omega
      · rw [le_max_iff]
        right
        omega
    · simp only [Units.val_neg, Units.val_one, neg_mul, one_mul]
      push Not at hs
      rw [abs_of_neg hs] at hj
      constructor
      · rw [min_le_iff]
        right
        omega
      · have := hci.2
        omega
  · simp only [stepToward, Function.update_of_ne hij]
    exact hc i

/-- Bounds on the coordinates of a vertex of the left anchor at scale `3m'`. -/
theorem leftAnchor_bounds {a : Fin d} {m' : ℕ} {s : Vertex d} (hs : s ∈ leftAnchor a (3 * m'))
    (j : Fin d) :
    (j = a → -(18 * m' : ℤ) + ((3 * m') / 8 : ℕ) ≤ s j ∧ s j ≤ -(12 * m' : ℤ) - ((3 * m') / 8 : ℕ)) ∧
      (j ≠ a → -((18 * m' : ℤ) - ((3 * m') / 8 : ℕ)) ≤ s j ∧
        s j ≤ (18 * m' : ℤ) - ((3 * m') / 8 : ℕ)) := by
  obtain ⟨⟨h1, h2⟩, h3⟩ := hs
  refine ⟨fun hj => ?_, fun hj => ?_⟩
  · subst hj
    push_cast at h1 h2 ⊢
    constructor <;> omega
  · have := abs_le.1 (h3 j hj)
    push_cast at this ⊢
    constructor <;> omega

/-- The first cubes of the route lie in the left exploration region. -/
theorem cubeAt_subset_leftExplore_of_leftAnchor {a : Fin d} {m' : ℕ} {s : Vertex d}
    (hs : s ∈ leftAnchor a (3 * m')) {r : ℕ} (hr : r ≤ (3 * m') / 8) :
    cubeAt s r ⊆ leftExplore a m' := by
  intro y hy
  refine ⟨fun i => ?_, ?_⟩
  · have hyi := abs_le.1 (hy i)
    have hb := leftAnchor_bounds hs i
    simp only [Pi.zero_apply, sub_zero]
    rw [abs_le]
    by_cases hia : i = a
    · obtain ⟨h1, h2⟩ := hb.1 hia
      constructor <;> push_cast at * <;> omega
    · obtain ⟨h1, h2⟩ := hb.2 hia
      constructor <;> push_cast at * <;> omega
  · have hya := abs_le.1 (hy a)
    obtain ⟨h1, h2⟩ := (leftAnchor_bounds hs a).1 rfl
    push_cast at *
    omega

/-- The face orthant of `s + Q_{2w}` in direction `a` with nonnegative signs lies in the first
cube of the route. -/
theorem faceOrthant_subset_routeStart (a : Fin d) (s : Vertex d) (w : ℕ) :
    faceOrthant s a (fun _ => 1) (2 * w) ⊆ cubeAt (routeStart a s w) w := by
  rintro y ⟨hy, hya, hyj⟩ i
  simp only [Units.val_one, one_mul] at hya hyj
  simp only [routeStart]
  by_cases hia : i = a
  · subst hia
    simp only [↓reduceIte]
    push_cast at hya ⊢
    rw [abs_le]
    constructor <;> omega
  · simp only [hia, ↓reduceIte]
    have h1 := hyj i hia
    have h2 := abs_le.1 (hy i)
    push_cast at h2 ⊢
    rw [abs_le]
    constructor <;> omega

/-- Coordinates of the route destination. -/
theorem routeTarget_apply_bounds {a b : Fin d} (hab : a ≠ b) (sg : ℤˣ) (m' : ℕ) (j : Fin d) :
    (j = a → routeTarget a b sg m' j = -(5 * m' : ℤ)) ∧
      (j ≠ a → |routeTarget a b sg m' j| ≤ 9 * m' ∧
        (j = b → routeTarget a b sg m' j = (sg : ℤ) * (9 * m' : ℕ)) ∧
        (j ≠ b → routeTarget a b sg m' j = 0)) := by
  refine ⟨fun hj => by simp [routeTarget, hj], fun hj => ?_⟩
  refine ⟨?_, fun hjb => by subst hjb; simp [routeTarget, hj],
    fun hjb => by simp [routeTarget, hj, hjb]⟩
  simp only [routeTarget, hj, ↓reduceIte]
  split_ifs with hjb
  · rcases units_coe_eq_one_or sg with h | h <;> rw [h] <;> push_cast <;> simp
  · simp

/-- The cubes of radius `2w` around the centres of the route lie in the left exploration
region. -/
theorem route_cube_subset {a b : Fin d} (hab : a ≠ b) {m' w : ℕ} {s : Vertex d}
    (hs : s ∈ leftAnchor a (3 * m')) (hw : 3 * w ≤ (3 * m') / 8) (hw' : 2 * w ≤ m') (sg : ℤˣ)
    {c : Vertex d} (hc : c ∈ routeSafe (routeStart a s w) (routeTarget a b sg m')) :
    cubeAt c (2 * w) ⊆ leftExplore a m' := by
  intro y hy
  have hca := hc a
  have hta := (routeTarget_apply_bounds hab sg m' a).1 rfl
  obtain ⟨hsa1, hsa2⟩ := (leftAnchor_bounds hs a).1 rfl
  simp only [routeStart, ↓reduceIte, hta] at hca
  refine ⟨fun i => ?_, ?_⟩
  · have hyi := abs_le.1 (hy i)
    simp only [Pi.zero_apply, sub_zero]
    rw [abs_le]
    by_cases hia : i = a
    · subst hia
      push_cast at *
      constructor <;> omega
    · have hci := hc i
      have hti := ((routeTarget_apply_bounds hab sg m' i).2 hia).1
      obtain ⟨hsi1, hsi2⟩ := (leftAnchor_bounds hs i).2 hia
      simp only [routeStart, hia, ↓reduceIte] at hci
      rw [abs_le] at hti
      push_cast at *
      constructor <;> omega
  · have hya := abs_le.1 (hy a)
    push_cast at *
    omega

/-- Cubes of radius `w` around the centres of the route are far from a seed path of radius `u`
at `s` when `2u < w`. -/
theorem route_far {a b : Fin d} (hab : a ≠ b) {m' w u : ℕ} {s : Vertex d}
    (hs : s ∈ leftAnchor a (3 * m')) (huw : 2 * u < w) (hw' : 2 * w ≤ m') (sg : ℤˣ)
    {c : Vertex d}
    (hc : c ∈ routeSafe (routeStart a s w) (routeTarget a b sg m')) {x g : Vertex d}
    (hx : x ∈ cubeAt c w) (hg : g ∈ cubeAt s u) : g ∉ cubeAt x u := by
  intro hgx
  have hca := hc a
  have hta := (routeTarget_apply_bounds hab sg m' a).1 rfl
  obtain ⟨hsa1, hsa2⟩ := (leftAnchor_bounds hs a).1 rfl
  simp only [routeStart, ↓reduceIte, hta] at hca
  have h1 := abs_le.1 (hx a)
  have h2 := abs_le.1 (hg a)
  have h3 := abs_le.1 (hgx a)
  push_cast at *
  omega

/-- When every coordinate of a centre of the route is within `w` of the destination, its cube of
radius `w` lies in the shifted anchor. -/
theorem route_final_subset {a b : Fin d} (hab : a ≠ b) {m' w : ℕ} (hw : 2 * w ≤ m' / 8)
    (sg : ℤˣ) {c : Vertex d} (hc : ∀ j, |routeTarget a b sg m' j - c j| < w) :
    cubeAt c w ⊆ (shiftedAnchorFinset a b sg m' : Set (Vertex d)) := by
  classical
  intro y hy
  simp only [shiftedAnchorFinset, Finset.coe_filter, Set.mem_setOf_eq]
  have hyt : ∀ j, |y j - routeTarget a b sg m' j| < 2 * w := by
    intro j
    have h1 := abs_le.1 (hy j)
    have h2 := abs_lt.1 (hc j)
    rw [abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  refine ⟨mem_cubeFinset.2 fun j => ?_, ⟨?_, ?_⟩, fun j hj => ?_⟩
  · have h1 := abs_lt.1 (hyt j)
    simp only [Pi.zero_apply, sub_zero]
    rw [abs_le]
    by_cases hja : j = a
    · have := (routeTarget_apply_bounds hab sg m' j).1 hja
      rw [this] at h1
      push_cast at *
      constructor <;> omega
    · have := abs_le.1 ((routeTarget_apply_bounds hab sg m' j).2 hja).1
      push_cast at *
      constructor <;> omega
  · have h1 := abs_lt.1 (hyt a)
    rw [(routeTarget_apply_bounds hab sg m' a).1 rfl] at h1
    rw [Pi.sub_apply, offsetVec_apply, if_neg hab, sub_zero]
    push_cast at *
    omega
  · have h1 := abs_lt.1 (hyt a)
    rw [(routeTarget_apply_bounds hab sg m' a).1 rfl] at h1
    rw [Pi.sub_apply, offsetVec_apply, if_neg hab, sub_zero]
    push_cast at *
    omega
  · have h1 := abs_lt.1 (hyt j)
    simp only [Pi.sub_apply, offsetVec_apply]
    rw [abs_le]
    by_cases hjb : j = b
    · have := ((routeTarget_apply_bounds hab sg m' j).2 hj).2.1 hjb
      rw [this] at h1
      simp only [hjb, ↓reduceIte]
      subst hjb
      push_cast at *
      constructor <;> omega
    · have := ((routeTarget_apply_bounds hab sg m' j).2 hj).2.2 hjb
      rw [this] at h1
      simp only [hjb, ↓reduceIte, sub_zero]
      push_cast at *
      constructor <;> omega

/-- The number of steps of the route is bounded independently of the scale. -/
theorem stepPotential_routeStart_le {a b : Fin d} (hab : a ≠ b) {m' w : ℕ} {s : Vertex d}
    (hs : s ∈ leftAnchor a (3 * m')) (hw0 : 1 ≤ w) (hwm : m' < 16 * (w + 1)) (sg : ℤˣ) :
    stepPotential (routeTarget a b sg m') (routeStart a s w) w ≤ d * 1300 := by
  have hcoord : ∀ j, (routeTarget a b sg m' j - routeStart a s w j).natAbs / w ≤ 1300 := by
    intro j
    apply Nat.div_le_of_le_mul
    have hbound : |routeTarget a b sg m' j - routeStart a s w j| ≤ 40 * m' + 2 * w := by
      rw [abs_le]
      by_cases hja : j = a
      · have ht := (routeTarget_apply_bounds hab sg m' j).1 hja
        subst hja
        obtain ⟨h1, h2⟩ := (leftAnchor_bounds hs j).1 rfl
        simp only [routeStart, ↓reduceIte, ht]
        push_cast at *
        constructor <;> omega
      · have ht := abs_le.1 ((routeTarget_apply_bounds hab sg m' j).2 hja).1
        obtain ⟨h1, h2⟩ := (leftAnchor_bounds hs j).2 hja
        simp only [routeStart, hja, ↓reduceIte]
        push_cast at *
        constructor <;> omega
    rw [Int.abs_eq_natAbs] at hbound
    have : (routeTarget a b sg m' j - routeStart a s w j).natAbs ≤ 40 * m' + 2 * w := by
      exact_mod_cast hbound
    omega
  unfold stepPotential
  calc ∑ j, (routeTarget a b sg m' j - routeStart a s w j).natAbs / w ≤ ∑ _j : Fin d, 1300 :=
        Finset.sum_le_sum fun j _ => hcoord j
    _ = d * 1300 := by simp

/-- **Left seeds reach the shifted anchors.** Let `p_c < p_s < p₀ < 1` with `θ(p_s) > 0`. For every
`η > 0` there are `u` and `m₀` such that for all `m' ≥ m₀`, both signs `σ` and every left seed `S`
of scale `3m'` and radius `u`, the seed is joined inside the left exploration region to the left
anchor of the subregion `σ 9m' e_b + Q_{6m'}` at level `p₀` with probability at least `1 - η`. -/
theorem exists_leftSeed_anchor_prob [NeZero d] {a b : Fin d} (hab : a ≠ b)
    {p_s p₀ : unitInterval} (hθ : 0 < LatticeProb.Percolation.theta d p_s)
    (hps : (p_s : ℝ) < p₀) (hp₀ : (p₀ : ℝ) < 1) {η : ℝ} (hη : 0 < η) :
    ∃ u m₀ : ℕ, ∀ m', m₀ ≤ m' → ∀ (sg : ℤˣ) (S : Finset (Vertex d)),
      LeftSeed a u (3 * m') S →
        1 - η ≤ (latticeBondLaw d p₀).real
          {ω | ConnectsRegions ω (leftExplore a m') S (shiftedAnchorFinset a b sg m')} := by
  set Nmax : ℕ := d * 1300 with hNmaxdef
  have hd : 0 < d := Nat.pos_of_ne_zero (NeZero.ne d)
  have hNmax : (0 : ℝ) < Nmax := by rw [hNmaxdef]; positivity
  set δ : ℝ := ((p₀ : ℝ) - p_s) / Nmax with hδdef
  have hδ : 0 < δ := div_pos (by linarith) hNmax
  have hδ1 : δ < 1 := by
    rw [hδdef, div_lt_one hNmax]
    have : (1 : ℝ) ≤ Nmax := by rw [hNmaxdef]; push_cast; nlinarith [(Nat.one_le_cast.2 hd : (1:ℝ) ≤ d)]
    linarith [p_s.property.1]
  obtain ⟨K, hK⟩ : ∃ K : ℕ, (1 - δ) ^ K < η / (3 * Nmax) :=
    exists_pow_lt_of_lt_one (by positivity) (by linarith)
  have hpK : 0 < (1 - (p₀ : ℝ)) ^ K := pow_pos (by linarith) _
  set η' : ℝ := min (η / 3) (η * (1 - (p₀ : ℝ)) ^ K / (3 * Nmax)) with hη'def
  have hη' : 0 < η' := lt_min (by positivity) (by positivity)
  have hps1 : (p_s : ℝ) < 1 := by linarith
  obtain ⟨u, n₁, -, hseed⟩ := exists_seed_faceOrthant_prob p_s hθ hps1 hη'
  refine ⟨u, 16 * (n₁ + 2 * u + 2), fun m' hm' sg S hS => ?_⟩
  set w := m' / 16 with hwdef
  have hw1 : n₁ + 2 * u + 2 ≤ w := by omega
  obtain ⟨-, s, hs, hpath⟩ := hS
  obtain ⟨γ, hγS, hγpath⟩ := hpath.exists_finset_seed
  set W := leftExploreFinset a m' with hWdef
  have hγW : γ ⊆ W := by
    intro g hg
    rw [← Finset.mem_coe, hWdef, coe_leftExploreFinset]
    exact cubeAt_subset_leftExplore_of_leftAnchor hs (r := u) (by omega) (hγS hg).2
  have hinit : 1 - η' ≤ (latticeBondLaw d p_s).real
      {ω | ConnectsRegions ω (W : Set (Vertex d)) γ (cubeFinset (routeStart a s w) w)} := by
    have h := hseed (2 * w) (by omega) s a (fun _ => 1) γ hγpath
    refine (le_of_lt h).trans (measureReal_mono ?_)
    intro ω hω
    refine connectsRegions_mono hω ?_ le_rfl ?_
    · rw [hWdef, coe_leftExploreFinset]
      exact cubeAt_subset_leftExplore_of_leftAnchor hs (by omega)
    · rw [coe_cubeFinset]
      exact faceOrthant_subset_routeStart a s w
  have hstart : routeStart a s w ∈ routeSafe (routeStart a s w) (routeTarget a b sg m') :=
    fun j => ⟨min_le_left _ _, le_max_left _ _⟩
  have hN := stepPotential_routeStart_le hab hs (w := w) (by omega) (by omega) sg
  set N := stepPotential (routeTarget a b sg m') (routeStart a s w) w with hNdef
  have hNδ : (N : ℝ) * δ ≤ (p₀ : ℝ) - p_s := by
    have : (N : ℝ) ≤ Nmax := by exact_mod_cast hN
    calc (N : ℝ) * δ ≤ Nmax * δ := mul_le_mul_of_nonneg_right this hδ.le
      _ = (p₀ : ℝ) - p_s := by rw [hδdef]; field_simp
  have hnav := navigate hη'.le hseed γ W (shiftedAnchorFinset a b sg m') hγW
    (routeTarget a b sg m') (w := w) (by omega) (by omega)
    (routeSafe (routeStart a s w) (routeTarget a b sg m'))
    (fun c hc => by
      rw [hWdef, coe_leftExploreFinset]
      exact route_cube_subset hab hs (by omega) (by omega) sg hc)
    (fun c hc x hx g hg => route_far hab hs (u := u) (by omega) (by omega) sg hc hx (hγS hg).2)
    (fun c hc j hj => stepToward_mem_routeSafe hc j hj)
    (fun c hc hfin => route_final_subset hab (by omega) sg hfin)
    δ hδ p₀ hp₀ K N (routeStart a s w) hstart rfl p_s p₀ le_rfl (by linarith) le_rfl η' hinit
  have hbound : η' + N * (η' / (1 - (p₀ : ℝ)) ^ K + (1 - δ) ^ K) ≤ η := by
    have h1 : η' ≤ η / 3 := min_le_left _ _
    have h2 : η' ≤ η * (1 - (p₀ : ℝ)) ^ K / (3 * Nmax) := min_le_right _ _
    have hNle : (N : ℝ) ≤ Nmax := by exact_mod_cast hN
    have h3 : (N : ℝ) * (η' / (1 - (p₀ : ℝ)) ^ K) ≤ η / 3 := by
      calc (N : ℝ) * (η' / (1 - (p₀ : ℝ)) ^ K) ≤ Nmax * (η' / (1 - (p₀ : ℝ)) ^ K) :=
            mul_le_mul_of_nonneg_right hNle (by positivity)
        _ ≤ Nmax * ((η * (1 - (p₀ : ℝ)) ^ K / (3 * Nmax)) / (1 - (p₀ : ℝ)) ^ K) := by
            gcongr
        _ = η / 3 := by field_simp
    have h4 : (N : ℝ) * (1 - δ) ^ K ≤ η / 3 := by
      calc (N : ℝ) * (1 - δ) ^ K ≤ Nmax * (η / (3 * Nmax)) :=
            mul_le_mul hNle hK.le (by positivity) (by positivity)
        _ = η / 3 := by field_simp
    nlinarith
  refine le_trans (by linarith) (hnav.trans (measureReal_mono ?_))
  intro ω hω
  refine connectsRegions_mono hω ?_ (fun g hg => (hγS hg).1) le_rfl
  rw [hWdef, coe_leftExploreFinset]

end Rigidity.Percolation
