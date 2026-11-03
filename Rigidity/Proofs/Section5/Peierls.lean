import Rigidity.Steps.Section5.DisjointPathsToInfinity
import LatticeProb.Prob.Percolation.LSSThinVacuity

/-!
# Proposition 5.21: the Peierls bounds

This file proves the steps `SiteDensityNearOneStep` (`step:5.21-site-density`) and
`OneDependentPeierlsStep` (`step:5.21-peierls`) of Proposition 5.21
(`Rigidity/Steps/Section5/DisjointPathsToInfinity.lean`; corrected draft L2154-2158,
L2253-2276). The printed proof cites Grimmett, *Percolation*, Theorem 8.92 for the first; both
follow from one Peierls bound, valid for every `1`-dependent site field on `ℤ²` (for the
`ℓ^∞` distance) whose sites are closed with probability at most `ε`:
`P(z is not in an infinite open cluster) ≤ 64⁹ ε` (`measure_not_inInfiniteSiteCluster_le`).

**Duality** (`exists_closedStarWalk`). Let `z` be open with a finite open cluster `C`, and let
`u = z + (k₀, 0)` be the last site of `C` on the horizontal ray from `z`. The lattice edges with
exactly one endpoint in `C` (the edge boundary of `C`) form, with two of them adjacent when
they are edges of a common plaquette, the dual boundary graph (`boundaryGraph`); let `Γ` be the
component of the edge `D₀` from `u` to `u + (1, 0)`. Every plaquette has an even number of edges
in `Γ` (`plaquette_sum_eq_zero`: if it has one, its edges in `Γ` are its boundary edges, and the
four corners of a plaquette change membership in `C` an even number of times). Hence the parity
`F(a)` of the number of edges of `Γ` crossed by the horizontal ray from `a` satisfies
`F(a) + F(b) = 1_{ab ∈ Γ}` for each lattice edge `ab` (`rowCount_succ_fst`,
`rowCount_add_succ_snd`): `F` is constant on `C`, equal to `F(u) = 1`, and vanishes on the
column `x = -B - 2` left of `C`. So `Γ` crosses the ray to the left of `z`. The outer endpoints of
the edges of `Γ` are closed and `*`-connected, which gives a closed self-avoiding `*`-walk from
`z + (k₀ + 1, 0)` to a site of abscissa at most `z.1`, of length at least `k₀ + 1`.

**Counting.** The `*`-walks of length `n` from a site number at most `9ⁿ`
(`card_starWalkLists_le`). Among the `n + 1` sites of a self-avoiding walk, at least
`(n + 1) / 9` lie at pairwise `ℓ^∞` distance at least `2` (`exists_separated_subset`); by
`1`-dependence these are all closed with probability at most `ε^{(n+1)/9}`
(`measure_forall_closed_le`). Summing over `n` and the starting points `z + (k, 0)`, `k ≤ n`,
gives a bound linear in `ε` for `ε ≤ 64⁻⁹`.
-/

open MeasureTheory ProbabilityTheory LatticeProb.Percolation Rigidity.Steps.Section5

noncomputable section

open Classical

namespace Rigidity.Proofs.Section5

/-! ### Lattice edges, plaquettes and the dual boundary graph -/

/-- The tip of the lattice edge `e` of `ℤ²`: `(s, false)` is the edge from `s` to `s + (1, 0)`,
`(s, true)` the edge from `s` to `s + (0, 1)`. -/
def edgeTip (e : PlanarCarrier × Bool) : PlanarCarrier :=
  if e.2 then (e.1.1, e.1.2 + 1) else (e.1.1 + 1, e.1.2)

@[simp] theorem edgeTip_false (x y : ℤ) : edgeTip ((x, y), false) = (x + 1, y) := rfl

@[simp] theorem edgeTip_true (x y : ℤ) : edgeTip ((x, y), true) = (x, y + 1) := rfl

theorem edgeTip_dist (e : PlanarCarrier × Bool) :
    |e.1.1 - (edgeTip e).1| + |e.1.2 - (edgeTip e).2| = 1 := by
  obtain ⟨⟨x, y⟩, b⟩ := e
  cases b <;> simp

/-- The edge `e` has exactly one endpoint in `C`. -/
def IsBoundaryEdge (C : Set PlanarCarrier) (e : PlanarCarrier × Bool) : Prop :=
  (e.1 ∈ C ∧ edgeTip e ∉ C) ∨ (e.1 ∉ C ∧ edgeTip e ∈ C)

/-- The edge `e` is one of the four edges of the plaquette `[x, x + 1] × [y, y + 1]`. -/
def IsPlaquetteEdge (x y : ℤ) (e : PlanarCarrier × Bool) : Prop :=
  e = ((x, y), false) ∨ e = ((x, y), true) ∨ e = ((x, y + 1), false) ∨ e = ((x + 1, y), true)

/-- The dual boundary graph of `C`: two edges of the edge boundary of `C` are adjacent when they
are edges of a common plaquette. -/
def boundaryGraph (C : Set PlanarCarrier) : SimpleGraph (PlanarCarrier × Bool) where
  Adj e e' := e ≠ e' ∧ IsBoundaryEdge C e ∧ IsBoundaryEdge C e' ∧
    ∃ x y, IsPlaquetteEdge x y e ∧ IsPlaquetteEdge x y e'
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2.1, h.2.1,
    let ⟨x, y, h1, h2⟩ := h.2.2.2; ⟨x, y, h2, h1⟩⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The component of the edge `D₀` in the dual boundary graph of `C`. -/
def boundaryComponent (C : Set PlanarCarrier) (D₀ : PlanarCarrier × Bool) :
    Set (PlanarCarrier × Bool) :=
  {e | (boundaryGraph C).Reachable D₀ e}

/-- The indicator of a set of edges, in `ZMod 2`. -/
def edgeInd (Γ : Set (PlanarCarrier × Bool)) (e : PlanarCarrier × Bool) : ZMod 2 :=
  if e ∈ Γ then 1 else 0

/-- The indicator of a set of sites, in `ZMod 2`. -/
def siteInd (C : Set PlanarCarrier) (s : PlanarCarrier) : ZMod 2 :=
  if s ∈ C then 1 else 0

theorem two_eq_zero_zmod : (2 : ZMod 2) = 0 := rfl

theorem edgeInd_of_notMem {Γ : Set (PlanarCarrier × Bool)} {e : PlanarCarrier × Bool}
    (h : e ∉ Γ) : edgeInd Γ e = 0 := if_neg h

theorem edgeInd_of_mem {Γ : Set (PlanarCarrier × Bool)} {e : PlanarCarrier × Bool}
    (h : e ∈ Γ) : edgeInd Γ e = 1 := if_pos h

theorem boundary_indicator (C : Set PlanarCarrier) (e : PlanarCarrier × Bool) :
    (if IsBoundaryEdge C e then (1 : ZMod 2) else 0) = siteInd C e.1 + siteInd C (edgeTip e) := by
  unfold IsBoundaryEdge siteInd
  by_cases h1 : e.1 ∈ C <;> by_cases h2 : edgeTip e ∈ C <;>
    first | (simp [h1, h2]; done) | (simp [h1, h2]; decide)

variable {C : Set PlanarCarrier} {D₀ : PlanarCarrier × Bool}

theorem isBoundaryEdge_of_mem (hD : IsBoundaryEdge C D₀) {e : PlanarCarrier × Bool}
    (he : e ∈ boundaryComponent C D₀) : IsBoundaryEdge C e := by
  have he' := (SimpleGraph.reachable_iff_reflTransGen _ _).mp he
  induction he' with
  | refl => exact hD
  | tail _ hadj _ => exact hadj.2.2.1

theorem notMem_boundaryComponent_of_both_notMem (hD : IsBoundaryEdge C D₀)
    {e : PlanarCarrier × Bool} (h1 : e.1 ∉ C) (h2 : edgeTip e ∉ C) :
    e ∉ boundaryComponent C D₀ := fun he => by
  rcases isBoundaryEdge_of_mem hD he with ⟨h, _⟩ | ⟨_, h⟩
  · exact h1 h
  · exact h2 h

theorem notMem_boundaryComponent_of_both_mem (hD : IsBoundaryEdge C D₀)
    {e : PlanarCarrier × Bool} (h1 : e.1 ∈ C) (h2 : edgeTip e ∈ C) :
    e ∉ boundaryComponent C D₀ := fun he => by
  rcases isBoundaryEdge_of_mem hD he with ⟨_, h⟩ | ⟨h, _⟩
  · exact h h2
  · exact h h1

/-- Every plaquette has an even number of edges in the component `Γ` of the dual boundary
graph. -/
theorem plaquette_sum_eq_zero (hD : IsBoundaryEdge C D₀) (x y : ℤ) :
    edgeInd (boundaryComponent C D₀) ((x, y), false) +
      edgeInd (boundaryComponent C D₀) ((x, y), true) +
      edgeInd (boundaryComponent C D₀) ((x, y + 1), false) +
      edgeInd (boundaryComponent C D₀) ((x + 1, y), true) = 0 := by
  set Γ := boundaryComponent C D₀ with hΓ
  by_cases h : ∃ e, IsPlaquetteEdge x y e ∧ e ∈ Γ
  · obtain ⟨e₀, he₀, hΓ₀⟩ := h
    have key : ∀ e, IsPlaquetteEdge x y e →
        edgeInd Γ e = siteInd C e.1 + siteInd C (edgeTip e) := by
      intro e he
      have hiff : e ∈ Γ ↔ IsBoundaryEdge C e := by
        refine ⟨isBoundaryEdge_of_mem hD, fun hb => ?_⟩
        by_cases hee : e₀ = e
        · exact hee ▸ hΓ₀
        · exact SimpleGraph.Reachable.trans hΓ₀
            (SimpleGraph.Adj.reachable ⟨hee, isBoundaryEdge_of_mem hD hΓ₀, hb, x, y, he₀, he⟩)
      rw [← boundary_indicator]
      unfold edgeInd
      simp only [hiff]
    rw [key _ (Or.inl rfl), key _ (Or.inr (Or.inl rfl)), key _ (Or.inr (Or.inr (Or.inl rfl))),
      key _ (Or.inr (Or.inr (Or.inr rfl)))]
    simp only [edgeTip_false, edgeTip_true]
    linear_combination (siteInd C (x, y) + siteInd C (x + 1, y) + siteInd C (x, y + 1) +
      siteInd C (x + 1, y + 1)) * two_eq_zero_zmod
  · push Not at h
    rw [edgeInd_of_notMem (h _ (Or.inl rfl)), edgeInd_of_notMem (h _ (Or.inr (Or.inl rfl))),
      edgeInd_of_notMem (h _ (Or.inr (Or.inr (Or.inl rfl)))),
      edgeInd_of_notMem (h _ (Or.inr (Or.inr (Or.inr rfl))))]
    simp

/-! ### The parity of the crossings of a horizontal ray -/

/-- The parity of the number of edges of `Γ` crossed by the horizontal ray from `a`, up to the
abscissa `R`. -/
def rowCount (Γ : Set (PlanarCarrier × Bool)) (R : ℤ) (a : PlanarCarrier) : ZMod 2 :=
  ∑ i ∈ Finset.range (R - a.1).toNat, edgeInd Γ ((a.1 + i, a.2), false)

theorem rowCount_succ_fst (Γ : Set (PlanarCarrier × Bool)) {R x : ℤ} (y : ℤ) (h : x < R) :
    rowCount Γ R (x, y) = edgeInd Γ ((x, y), false) + rowCount Γ R (x + 1, y) := by
  unfold rowCount
  have hn : (R - x).toNat = (R - (x + 1)).toNat + 1 := by omega
  simp only
  rw [hn, Finset.sum_range_succ', add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ => ?_
    congr 3
    push_cast
    ring

theorem sum_range_add_succ_eq (g : ℕ → ZMod 2) (m : ℕ) :
    ∑ i ∈ Finset.range m, (g i + g (i + 1)) = g 0 + g m := by
  induction m with
  | zero => simp only [Finset.sum_range_zero]; linear_combination (-g 0) * two_eq_zero_zmod
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    linear_combination g m * two_eq_zero_zmod

theorem rowCount_add_succ_snd (Γ : Set (PlanarCarrier × Bool)) {R x : ℤ} (y : ℤ) (h : x ≤ R)
    (hR : ∀ y', ((R, y'), true) ∉ Γ)
    (heven : ∀ x y : ℤ, edgeInd Γ ((x, y), false) + edgeInd Γ ((x, y), true) +
      edgeInd Γ ((x, y + 1), false) + edgeInd Γ ((x + 1, y), true) = 0) :
    rowCount Γ R (x, y) + rowCount Γ R (x, y + 1) = edgeInd Γ ((x, y), true) := by
  unfold rowCount
  simp only
  set n := (R - x).toNat with hn
  have hxn : x + (n : ℤ) = R := by omega
  have h0 := Finset.sum_eq_zero (s := Finset.range n) fun i (_ : i ∈ Finset.range n) =>
    heven (x + i) y
  simp only [Finset.sum_add_distrib] at h0
  have htel := sum_range_add_succ_eq (fun i : ℕ => edgeInd Γ ((x + i, y), true)) n
  simp only [Finset.sum_add_distrib, Nat.cast_zero, add_zero, Nat.cast_succ, ← add_assoc] at htel
  have hz : edgeInd Γ ((x + (n : ℤ), y), true) = 0 := edgeInd_of_notMem (hxn ▸ hR y)
  linear_combination h0 - htel - hz - edgeInd Γ ((x, y), true) * two_eq_zero_zmod

/-! ### Closed `*`-walks -/

/-- The `*`-graph of the closed sites of `η`: two distinct closed sites are adjacent when they
are at `ℓ^∞` distance `1`. -/
def closedStarGraph (η : PlanarCarrier → Bool) : SimpleGraph PlanarCarrier where
  Adj s t := s ≠ t ∧ |s.1 - t.1| ≤ 1 ∧ |s.2 - t.2| ≤ 1 ∧ η s = false ∧ η t = false
  symm := ⟨fun s t h => ⟨h.1.symm, by rw [abs_sub_comm]; exact h.2.1,
    by rw [abs_sub_comm]; exact h.2.2.1, h.2.2.2.2, h.2.2.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The endpoint of the edge `e` outside `C`. -/
def outerEnd (C : Set PlanarCarrier) (e : PlanarCarrier × Bool) : PlanarCarrier :=
  if e.1 ∈ C then edgeTip e else e.1

theorem plaquetteEdge_bounds {x y : ℤ} {e : PlanarCarrier × Bool} (h : IsPlaquetteEdge x y e) :
    (x ≤ e.1.1 ∧ e.1.1 ≤ x + 1 ∧ y ≤ e.1.2 ∧ e.1.2 ≤ y + 1) ∧
      (x ≤ (edgeTip e).1 ∧ (edgeTip e).1 ≤ x + 1 ∧ y ≤ (edgeTip e).2 ∧ (edgeTip e).2 ≤ y + 1) := by
  rcases h with rfl | rfl | rfl | rfl <;> simp

theorem outerEnd_bounds {x y : ℤ} {e : PlanarCarrier × Bool} (h : IsPlaquetteEdge x y e) :
    x ≤ (outerEnd C e).1 ∧ (outerEnd C e).1 ≤ x + 1 ∧ y ≤ (outerEnd C e).2 ∧
      (outerEnd C e).2 ≤ y + 1 := by
  unfold outerEnd
  split_ifs
  · exact (plaquetteEdge_bounds h).2
  · exact (plaquetteEdge_bounds h).1

theorem reachable_outerEnd (η : PlanarCarrier → Bool)
    (hcl : ∀ e, IsBoundaryEdge C e → η (outerEnd C e) = false) {e : PlanarCarrier × Bool}
    (he : (boundaryGraph C).Reachable D₀ e) :
    (closedStarGraph η).Reachable (outerEnd C D₀) (outerEnd C e) := by
  have he' := (SimpleGraph.reachable_iff_reflTransGen _ _).mp he
  clear he
  induction he' with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail b c _ hadj ih =>
    refine ih.trans ?_
    by_cases heq : outerEnd C b = outerEnd C c
    · rw [heq]
    · obtain ⟨x, y, hb, hc⟩ := hadj.2.2.2
      have h1 := outerEnd_bounds (C := C) hb
      have h2 := outerEnd_bounds (C := C) hc
      exact SimpleGraph.Adj.reachable ⟨heq, abs_le.mpr ⟨by omega, by omega⟩,
        abs_le.mpr ⟨by omega, by omega⟩, hcl _ hadj.2.1, hcl _ hadj.2.2.1⟩

theorem open_of_reachable {η : PlanarCarrier → Bool} {z w : PlanarCarrier} (hz : η z = true)
    (h : (siteOpenGraph η).Reachable z w) : η w = true := by
  have h' := (SimpleGraph.reachable_iff_reflTransGen _ _).mp h
  induction h' with
  | refl => exact hz
  | tail _ hadj _ => exact hadj.2.2

theorem unit_step_cases {a b : ℤ} (h : |a| + |b| = 1) :
    (a = -1 ∧ b = 0) ∨ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = -1) ∨ (a = 0 ∧ b = 1) := by
  rcases abs_cases a with ⟨ha, _⟩ | ⟨ha, _⟩ <;> rcases abs_cases b with ⟨hb, _⟩ | ⟨hb, _⟩ <;>
    rw [ha, hb] at h <;> omega

/-- **Duality.** If the open cluster of the open site `z` is finite, a closed self-avoiding
`*`-walk joins a site `z + (k + 1, 0)` of the horizontal ray from `z` to a site of abscissa at
most `z.1`. -/
theorem exists_closedStarWalk (η : PlanarCarrier → Bool) (z : PlanarCarrier) (hz : η z = true)
    (hfin : {w | (siteOpenGraph η).Reachable z w}.Finite) :
    ∃ k : ℕ, ∃ w' : PlanarCarrier, ∃ p : (closedStarGraph η).Walk (z.1 + (k + 1 : ℕ), z.2) w',
      p.IsPath ∧ w'.1 ≤ z.1 ∧ η (z.1 + (k + 1 : ℕ), z.2) = false := by
  set C := {w | (siteOpenGraph η).Reachable z w} with hCdef
  have hzC : z ∈ C := SimpleGraph.Reachable.refl z
  obtain ⟨B, hB⟩ : ∃ B : ℤ, ∀ c ∈ C, |c.1| ≤ B ∧ |c.2| ≤ B := by
    obtain ⟨B, hB⟩ := (hfin.image fun c : PlanarCarrier => max |c.1| |c.2|).bddAbove
    exact ⟨B, fun c hc => by
      have := hB (Set.mem_image_of_mem _ hc)
      exact ⟨(le_max_left _ _).trans this, (le_max_right _ _).trans this⟩⟩
  have hB' : ∀ c ∈ C, -B ≤ c.1 ∧ c.1 ≤ B ∧ -B ≤ c.2 ∧ c.2 ≤ B := fun c hc =>
    ⟨(abs_le.mp (hB c hc).1).1, (abs_le.mp (hB c hc).1).2, (abs_le.mp (hB c hc).2).1,
      (abs_le.mp (hB c hc).2).2⟩
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB z hzC).1
  have hnot : ∀ s : PlanarCarrier, (B < s.1 ∨ s.1 < -B ∨ B < s.2 ∨ s.2 < -B) → s ∉ C :=
    fun s hs hsC => by have := hB' s hsC; omega
  -- the last site `u = z + (k₀, 0)` of `C` on the horizontal ray from `z`
  have hrowfin : {k : ℕ | ((z.1 + k, z.2) : PlanarCarrier) ∈ C}.Finite :=
    hfin.preimage (f := fun k : ℕ => ((z.1 + k, z.2) : PlanarCarrier))
      (fun a _ b _ h => by simpa using h)
  set K := hrowfin.toFinset
  have hK0 : 0 ∈ K := by simpa [K] using hzC
  set k₀ := K.max' ⟨0, hK0⟩
  have hk₀C : ((z.1 + k₀, z.2) : PlanarCarrier) ∈ C := by
    have := K.max'_mem ⟨0, hK0⟩
    simpa [K] using this
  have hk₀max : ∀ j : ℕ, k₀ < j → ((z.1 + j, z.2) : PlanarCarrier) ∉ C := fun j hj hjC => by
    have : j ≤ k₀ := K.le_max' j (by simpa [K] using hjC)
    omega
  set D₀ : PlanarCarrier × Bool := ((z.1 + k₀, z.2), false) with hD₀
  have hD : IsBoundaryEdge C D₀ := by
    refine Or.inl ⟨hk₀C, ?_⟩
    have := hk₀max (k₀ + 1) (by omega)
    push_cast at this
    simpa [D₀, ← add_assoc] using this
  set Γ := boundaryComponent C D₀ with hΓ
  set R := B + 1 with hRdef
  have hR : ∀ y', ((R, y'), true) ∉ Γ := fun y' =>
    notMem_boundaryComponent_of_both_notMem hD (hnot _ (by simp; omega))
      (hnot _ (by simp; omega))
  have heven := plaquette_sum_eq_zero hD
  -- `rowCount` is constant on `C`
  have hadj : ∀ s t : PlanarCarrier, s ∈ C → t ∈ C → |s.1 - t.1| + |s.2 - t.2| = 1 →
      rowCount Γ R s = rowCount Γ R t := by
    rintro ⟨s1, s2⟩ ⟨t1, t2⟩ hs ht hd
    have hs' := hB' _ hs
    have ht' := hB' _ ht
    simp only at hd hs' ht'
    rcases unit_step_cases hd with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain rfl : t1 = s1 + 1 := by omega
      obtain rfl : s2 = t2 := by omega
      rw [rowCount_succ_fst Γ s2 (R := R) (x := s1) (by omega),
        edgeInd_of_notMem (notMem_boundaryComponent_of_both_mem (e := ((s1, s2), false)) hD hs ht),
        zero_add]
    · obtain rfl : s1 = t1 + 1 := by omega
      obtain rfl : s2 = t2 := by omega
      rw [rowCount_succ_fst Γ s2 (R := R) (x := t1) (by omega),
        edgeInd_of_notMem (notMem_boundaryComponent_of_both_mem (e := ((t1, s2), false)) hD ht hs),
        zero_add]
    · obtain rfl : t1 = s1 := by omega
      obtain rfl : t2 = s2 + 1 := by omega
      have := rowCount_add_succ_snd Γ s2 (R := R) (x := t1) (by omega) hR heven
      rw [edgeInd_of_notMem
        (notMem_boundaryComponent_of_both_mem (e := ((t1, s2), true)) hD hs ht)] at this
      linear_combination this - rowCount Γ R (t1, s2 + 1) * two_eq_zero_zmod
    · obtain rfl : t1 = s1 := by omega
      obtain rfl : s2 = t2 + 1 := by omega
      have := rowCount_add_succ_snd Γ t2 (R := R) (x := t1) (by omega) hR heven
      rw [edgeInd_of_notMem
        (notMem_boundaryComponent_of_both_mem (e := ((t1, t2), true)) hD ht hs)] at this
      linear_combination this - rowCount Γ R (t1, t2) * two_eq_zero_zmod
  have hconst : ∀ s ∈ C, rowCount Γ R s = rowCount Γ R z := by
    intro s hs
    have hs' := (SimpleGraph.reachable_iff_reflTransGen _ _).mp hs
    clear hs
    induction hs' with
    | refl => rfl
    | @tail a b hab hab' ih =>
      have haC : a ∈ C := (SimpleGraph.reachable_iff_reflTransGen _ _).mpr hab
      have hbC : b ∈ C := (SimpleGraph.reachable_iff_reflTransGen _ _).mpr (hab.tail hab')
      rw [← ih, hadj b a hbC haC]
      rw [abs_sub_comm b.1, abs_sub_comm b.2]
      exact hab'.1
  -- `rowCount` is `1` on `C`
  have hFw : rowCount Γ R (z.1 + k₀ + 1, z.2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => edgeInd_of_notMem ?_
    refine notMem_boundaryComponent_of_both_notMem hD ?_ ?_
    · have := hk₀max (k₀ + 1 + i) (by omega)
      push_cast at this
      simpa [add_assoc] using this
    · have := hk₀max (k₀ + 1 + i + 1) (by omega)
      push_cast at this
      simpa [add_assoc] using this
  have hFz : rowCount Γ R z = 1 := by
    rw [← hconst _ hk₀C, rowCount_succ_fst Γ z.2 (by have := hB' _ hk₀C; simp at this; omega),
      hFw, edgeInd_of_mem (SimpleGraph.Reachable.refl _), add_zero]
  -- `Γ` crosses the ray to the left of `z`
  have hleft : ∃ x : ℤ, x < z.1 ∧ ((x, z.2), false) ∈ Γ := by
    by_contra hno
    push Not at hno
    have hzB := hB' z hzC
    have h1 : ∀ m : ℕ, rowCount Γ R (z.1 - m, z.2) = 1 := by
      intro m
      induction m with
      | zero => simpa using hFz
      | succ m ih =>
        have := rowCount_succ_fst Γ z.2 (x := z.1 - (m + 1 : ℕ)) (R := R) (by omega)
        rw [edgeInd_of_notMem (hno _ (by omega)), zero_add] at this
        rw [this, ← ih]
        congr 2
        push_cast
        ring
    have h2 : ∀ m : ℕ, rowCount Γ R (-B - 2, -B - 2 + m) = 0 := by
      intro m
      induction m with
      | zero =>
        refine Finset.sum_eq_zero fun i _ => edgeInd_of_notMem ?_
        exact notMem_boundaryComponent_of_both_notMem hD (hnot _ (by simp))
          (hnot _ (by simp))
      | succ m ih =>
        have := rowCount_add_succ_snd Γ (-B - 2 + m) (x := -B - 2) (R := R) (by omega) hR heven
        rw [edgeInd_of_notMem (notMem_boundaryComponent_of_both_notMem hD (hnot _ (by simp))
          (hnot _ (by simp))), ih] at this
        push_cast
        rw [← add_assoc]
        linear_combination this
    have e1 := h1 (z.1 + B + 2).toNat
    have e2 := h2 (z.2 + B + 2).toNat
    rw [Int.toNat_of_nonneg (by omega)] at e1 e2
    have : z.1 - (z.1 + B + 2) = -B - 2 := by ring
    rw [this] at e1
    have : -B - 2 + (z.2 + B + 2) = z.2 := by ring
    rw [this] at e2
    have : (1 : ZMod 2) = 0 := e1.symm.trans e2
    exact absurd this (by decide)
  -- the closed `*`-walk through the outer endpoints of `Γ`
  have hcl : ∀ e, IsBoundaryEdge C e → η (outerEnd C e) = false := by
    intro e he
    by_contra hη
    rw [Bool.not_eq_false] at hη
    rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [outerEnd, if_pos h1] at hη
      exact h2 (SimpleGraph.Reachable.trans h1 (SimpleGraph.Adj.reachable
        ⟨edgeTip_dist e, open_of_reachable hz h1, hη⟩))
    · rw [outerEnd, if_neg h1] at hη
      refine h1 (SimpleGraph.Reachable.trans h2 (SimpleGraph.Adj.reachable
        ⟨?_, open_of_reachable hz h2, hη⟩))
      rw [abs_sub_comm, abs_sub_comm (edgeTip e).2]
      exact edgeTip_dist e
  obtain ⟨x, hx, hxΓ⟩ := hleft
  have hreach := reachable_outerEnd η hcl hxΓ
  have hout : outerEnd C D₀ = (z.1 + (k₀ + 1 : ℕ), z.2) := by
    rw [outerEnd, if_pos hk₀C]
    simp [D₀, add_assoc]
  rw [hout] at hreach
  obtain ⟨p⟩ := hreach
  refine ⟨k₀, _, p.toPath.1, p.toPath.2, ?_, ?_⟩
  · unfold outerEnd
    split_ifs <;> simp <;> omega
  · rw [← hout]
    exact hcl D₀ hD

/-! ### Counting the `*`-walks -/

/-- The steps of a `*`-walk, `{-1, 0, 1}²`. -/
def starOffsets : Finset PlanarCarrier := Finset.Icc (-1) 1 ×ˢ Finset.Icc (-1) 1

theorem card_starOffsets : starOffsets.card = 9 := by
  rw [starOffsets, Finset.card_product, Int.card_Icc]
  rfl

/-- The site sequences of the walks of length `n` from `w` with steps in `{-1, 0, 1}²`. -/
def starWalkLists : ℕ → PlanarCarrier → Finset (List PlanarCarrier)
  | 0, w => {[w]}
  | n + 1, w => starOffsets.biUnion fun o => (starWalkLists n (w + o)).image (List.cons w)

theorem card_starWalkLists_le (n : ℕ) (w : PlanarCarrier) : (starWalkLists n w).card ≤ 9 ^ n := by
  induction n generalizing w with
  | zero => simp [starWalkLists]
  | succ n ih =>
    rw [starWalkLists, pow_succ, mul_comm, ← card_starOffsets]
    exact Finset.card_biUnion_le_card_mul _ _ _ fun o _ => Finset.card_image_le.trans (ih _)

theorem length_of_mem_starWalkLists {n : ℕ} {w : PlanarCarrier} {l : List PlanarCarrier}
    (h : l ∈ starWalkLists n w) : l.length = n + 1 := by
  induction n generalizing w l with
  | zero => simp [starWalkLists] at h; simp [h]
  | succ n ih =>
    simp only [starWalkLists, Finset.mem_biUnion, Finset.mem_image] at h
    obtain ⟨o, _, l', hl', rfl⟩ := h
    simp [ih hl']

theorem support_mem_starWalkLists {η : PlanarCarrier → Bool} {w v : PlanarCarrier}
    (p : (closedStarGraph η).Walk w v) : p.support ∈ starWalkLists p.length w := by
  induction p with
  | nil => simp [starWalkLists]
  | @cons u v' _ h p ih =>
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.length_cons, starWalkLists,
      Finset.mem_biUnion, Finset.mem_image]
    refine ⟨v' - u, ?_, p.support, by rwa [add_sub_cancel], rfl⟩
    have h1 := abs_le.mp h.2.1
    have h2 := abs_le.mp h.2.2.1
    simp only [starOffsets, Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub]
    omega

theorem fst_sub_le_length {η : PlanarCarrier → Bool} {w v : PlanarCarrier}
    (p : (closedStarGraph η).Walk w v) : w.1 - v.1 ≤ p.length := by
  induction p with
  | nil => simp
  | @cons u v' _ h p ih =>
    have := (abs_le.mp h.2.1).2
    simp only [SimpleGraph.Walk.length_cons]
    push_cast
    omega

theorem closed_of_mem_support {η : PlanarCarrier → Bool} {w v : PlanarCarrier}
    (p : (closedStarGraph η).Walk w v) (hw : η w = false) :
    ∀ s ∈ p.support, η s = false := by
  induction p with
  | nil => simpa using hw
  | @cons u v' _ h p ih =>
    intro s hs
    rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact hw
    · exact ih h.2.2.2.2 s hs

/-! ### Separated sites and `1`-dependence -/

/-- The sites at `ℓ^∞` distance at most `1` from `a`. -/
def starBox (a : PlanarCarrier) : Finset PlanarCarrier := starOffsets.image (a + ·)

theorem card_starBox_le (a : PlanarCarrier) : (starBox a).card ≤ 9 :=
  Finset.card_image_le.trans card_starOffsets.le

/-- Every finite set `T` of sites contains at least `|T| / 9` sites at pairwise `ℓ^∞` distance at
least `2`. -/
theorem exists_separated_subset (T : Finset PlanarCarrier) :
    ∃ S ⊆ T, T.card ≤ 9 * S.card ∧
      ∀ s ∈ S, ∀ t ∈ S, s ≠ t → (1 : ℤ) < max |s.1 - t.1| |s.2 - t.2| := by
  suffices ∀ n, ∀ T : Finset PlanarCarrier, T.card = n → ∃ S ⊆ T, T.card ≤ 9 * S.card ∧
      ∀ s ∈ S, ∀ t ∈ S, s ≠ t → (1 : ℤ) < max |s.1 - t.1| |s.2 - t.2| from this _ T rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro T hT
    rcases T.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact ⟨∅, by simp, by simp, by simp⟩
    set T' := T.filter fun t => (1 : ℤ) < max |t.1 - a.1| |t.2 - a.2| with hT'
    have haT' : a ∉ T' := by simp [T']
    have hT'T : T' ⊆ T := Finset.filter_subset _ _
    have hlt : T'.card < n := hT ▸ Finset.card_lt_card ⟨hT'T, fun h => haT' (h ha)⟩
    obtain ⟨S', hS'T', hcard, hsep⟩ := ih _ hlt T' rfl
    have haS' : a ∉ S' := fun h => haT' (hS'T' h)
    refine ⟨insert a S', Finset.insert_subset ha (hS'T'.trans hT'T), ?_, ?_⟩
    · have hbox : (T.filter fun t => ¬ (1 : ℤ) < max |t.1 - a.1| |t.2 - a.2|) ⊆ starBox a := by
        intro t ht
        simp only [Finset.mem_filter, not_lt, max_le_iff] at ht
        simp only [starBox, Finset.mem_image]
        refine ⟨t - a, ?_, by simp⟩
        simp only [starOffsets, Finset.mem_product, Finset.mem_Icc, Prod.fst_sub, Prod.snd_sub]
        have h1 := abs_le.mp ht.2.1
        have h2 := abs_le.mp ht.2.2
        omega
      have : T'.card + (T.filter fun t => ¬ (1 : ℤ) < max |t.1 - a.1| |t.2 - a.2|).card =
          T.card := Finset.card_filter_add_card_filter_not _
      have := (Finset.card_le_card hbox).trans (card_starBox_le a)
      rw [Finset.card_insert_of_notMem haS']
      omega
    · intro s hs t ht hst
      rw [Finset.mem_insert] at hs ht
      rcases hs with rfl | hs <;> rcases ht with rfl | ht
      · exact absurd rfl hst
      · have := (Finset.mem_filter.mp (hS'T' ht)).2
        rwa [abs_sub_comm s.1, abs_sub_comm s.2]
      · exact (Finset.mem_filter.mp (hS'T' hs)).2
      · exact hsep s hs t ht hst

/-- For a `1`-dependent field whose sites are closed with probability at most `ε`, the sites of
a set at pairwise `ℓ^∞` distance at least `2` are all closed with probability at most `ε^{|S|}`. -/
theorem measure_forall_closed_le {ν : Measure (PlanarCarrier → Bool)} [IsProbabilityMeasure ν]
    (hν : KDependentPlanar 1 ν) {ε : ℝ} (hε : ∀ z, ν {η | η z = false} ≤ ENNReal.ofReal ε)
    (S : Finset PlanarCarrier)
    (hS : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → (1 : ℤ) < max |s.1 - t.1| |s.2 - t.2|) :
    ν {η | ∀ s ∈ S, η s = false} ≤ ENNReal.ofReal ε ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.card_insert_of_notMem ha, pow_succ']
    have hsplit : {η : PlanarCarrier → Bool | ∀ s ∈ insert a S, η s = false} =
        (fun η : PlanarCarrier → Bool => fun i : ({a} : Finset PlanarCarrier) => η i) ⁻¹'
            {f | ∀ i, f i = false} ∩
          (fun η : PlanarCarrier → Bool => fun j : S => η j) ⁻¹' {f | ∀ j, f j = false} := by
      ext η
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Finset.mem_insert,
        Subtype.forall, Finset.mem_singleton]
      constructor
      · intro h
        exact ⟨fun i hi => h i (Or.inl hi), fun j hj => h j (Or.inr hj)⟩
      · rintro ⟨h1, h2⟩ s (hs | hs)
        · exact h1 s hs
        · exact h2 s hs
    have hind := hν {a} S fun i hi j hj => by
      rw [Finset.mem_singleton] at hi
      subst hi
      exact_mod_cast hS i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
        (fun h => ha (h ▸ hj))
    rw [hsplit, hind.measure_inter_preimage_eq_mul _ _ (Set.to_countable _).measurableSet
      (Set.to_countable _).measurableSet]
    refine mul_le_mul' ?_ ?_
    · have hA : (fun η : PlanarCarrier → Bool => fun i : ({a} : Finset PlanarCarrier) => η i) ⁻¹'
          {f | ∀ i, f i = false} = {η | η a = false} := by
        ext η
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Subtype.forall, Finset.mem_singleton,
          forall_eq]
      rw [hA]
      exact hε a
    · have hB : (fun η : PlanarCarrier → Bool => fun j : S => η j) ⁻¹'
          {f | ∀ j, f j = false} = {η | ∀ s ∈ S, η s = false} := by
        ext η
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Subtype.forall]
      rw [hB]
      exact ih fun s hs t ht hst => hS s (Finset.mem_insert_of_mem hs) t
        (Finset.mem_insert_of_mem ht) hst

/-! ### The Peierls bound -/

theorem pow_le_of_le_nine_mul {ε : ℝ} (hε : 0 ≤ ε) (hε0 : ε ≤ (64 : ℝ)⁻¹ ^ 9) {j n : ℕ}
    (hj : n + 1 ≤ 9 * j) : ε ^ j ≤ ε * 64 ^ 8 * (64 : ℝ)⁻¹ ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have h1 : ε ^ m ≤ (64 : ℝ)⁻¹ ^ (9 * m) := by
    rw [pow_mul]
    exact pow_le_pow_left₀ hε hε0 m
  have h64 : (64 : ℝ) ^ 8 * (64 : ℝ)⁻¹ ^ 8 = 1 := by norm_num
  have h2 : (64 : ℝ)⁻¹ ^ (9 * m) = 64 ^ 8 * (64 : ℝ)⁻¹ ^ (9 * m + 8) := by
    calc (64 : ℝ)⁻¹ ^ (9 * m) = (64 : ℝ)⁻¹ ^ (9 * m) * (64 ^ 8 * (64 : ℝ)⁻¹ ^ 8) := by
          rw [h64, mul_one]
      _ = 64 ^ 8 * (64 : ℝ)⁻¹ ^ (9 * m + 8) := by rw [pow_add]; ring
  have h3 : (64 : ℝ)⁻¹ ^ (9 * m + 8) ≤ (64 : ℝ)⁻¹ ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  calc ε ^ (m + 1) = ε * ε ^ m := pow_succ' _ _
    _ ≤ ε * (64 : ℝ)⁻¹ ^ (9 * m) := mul_le_mul_of_nonneg_left h1 hε
    _ = ε * (64 ^ 8 * (64 : ℝ)⁻¹ ^ (9 * m + 8)) := by rw [h2]
    _ ≤ ε * (64 ^ 8 * (64 : ℝ)⁻¹ ^ n) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 (by positivity)) hε
    _ = ε * 64 ^ 8 * (64 : ℝ)⁻¹ ^ n := by ring

/-- The sites of a self-avoiding walk of length `n` are all closed with probability at most
`64⁸ ε 64⁻ⁿ`. -/
theorem measure_closed_list_le {ν : Measure (PlanarCarrier → Bool)} [IsProbabilityMeasure ν]
    (hν : KDependentPlanar 1 ν) {ε : ℝ} (hε : 0 ≤ ε) (hε0 : ε ≤ (64 : ℝ)⁻¹ ^ 9)
    (hcl : ∀ z, ν {η | η z = false} ≤ ENNReal.ofReal ε) {l : List PlanarCarrier} (hl : l.Nodup)
    {n : ℕ} (hlen : l.length = n + 1) :
    ν {η | ∀ s ∈ l, η s = false} ≤ ENNReal.ofReal (ε * 64 ^ 8 * (64 : ℝ)⁻¹ ^ n) := by
  obtain ⟨S, hST, hcard, hsep⟩ := exists_separated_subset l.toFinset
  rw [List.toFinset_card_of_nodup hl, hlen] at hcard
  calc ν {η | ∀ s ∈ l, η s = false} ≤ ν {η | ∀ s ∈ S, η s = false} :=
        measure_mono fun η hη s hs => hη s (List.mem_toFinset.mp (hST hs))
    _ ≤ ENNReal.ofReal ε ^ S.card := measure_forall_closed_le hν hcl S hsep
    _ = ENNReal.ofReal (ε ^ S.card) := (ENNReal.ofReal_pow hε _).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (pow_le_of_le_nine_mul hε hε0 hcard)

theorem succ_mul_nine_pow_le (n : ℕ) :
    ((n : ℝ) + 1) * 9 ^ n * (64 : ℝ)⁻¹ ^ n ≤ (1 / 2) ^ n := by
  have h2n : ((n : ℝ) + 1) ≤ 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
  calc ((n : ℝ) + 1) * 9 ^ n * (64 : ℝ)⁻¹ ^ n ≤ 2 ^ n * 9 ^ n * (64 : ℝ)⁻¹ ^ n := by gcongr
    _ = (2 * 9 * (64 : ℝ)⁻¹) ^ n := by rw [mul_pow, mul_pow]
    _ ≤ (1 / 2) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n

/-- **Peierls bound.** For a `1`-dependent site field on `ℤ²` (for the `ℓ^∞` distance) whose
sites are closed with probability at most `ε`, a site misses the infinite open clusters with
probability at most `64⁹ ε`. -/
theorem measure_not_inInfiniteSiteCluster_le {ν : Measure (PlanarCarrier → Bool)}
    [IsProbabilityMeasure ν] (hν : KDependentPlanar 1 ν) {ε : ℝ} (hε : 0 ≤ ε)
    (hcl : ∀ z, ν {η | η z = false} ≤ ENNReal.ofReal ε) (z : PlanarCarrier) :
    ν {η | ¬ InInfiniteSiteCluster η z} ≤ ENNReal.ofReal (64 ^ 9 * ε) := by
  by_cases hε0 : ε ≤ (64 : ℝ)⁻¹ ^ 9
  swap
  · push Not at hε0
    refine prob_le_one.trans (ENNReal.one_le_ofReal.mpr ?_)
    have h64 : (64 : ℝ) ^ 9 * (64 : ℝ)⁻¹ ^ 9 = 1 := by norm_num
    nlinarith
  set E : List PlanarCarrier → Set (PlanarCarrier → Bool) :=
    fun l => {η | l.Nodup ∧ ∀ s ∈ l, η s = false} with hEdef
  have hsub : {η | ¬ InInfiniteSiteCluster η z} ⊆ {η | η z = false} ∪
      ⋃ n : ℕ, ⋃ k ∈ Finset.range (n + 1), ⋃ l ∈ starWalkLists n (z.1 + k, z.2), E l := by
    intro η hη
    by_cases hz : η z = true
    · right
      have hfin : {w | (siteOpenGraph η).Reachable z w}.Finite := by
        by_contra h
        exact hη ⟨hz, h⟩
      obtain ⟨k, w', p, hp, hw', hcl0⟩ := exists_closedStarWalk η z hz hfin
      have hlen : z.1 + ((k + 1 : ℕ) : ℤ) - w'.1 ≤ p.length := fst_sub_le_length p
      have hk' : ((k + 1 : ℕ) : ℤ) ≤ (p.length : ℤ) := by linarith
      have hk : k + 1 < p.length + 1 := Nat.lt_succ_of_le (by exact_mod_cast hk')
      simp only [Set.mem_iUnion]
      exact ⟨p.length, k + 1, Finset.mem_range.mpr hk, p.support,
        support_mem_starWalkLists p, hp.support_nodup, closed_of_mem_support p hcl0⟩
    · left
      simpa using hz
  have hE : ∀ n w l, l ∈ starWalkLists n w →
      ν (E l) ≤ ENNReal.ofReal (ε * 64 ^ 8 * (64 : ℝ)⁻¹ ^ n) := by
    intro n w l hl
    by_cases hnd : l.Nodup
    · exact (measure_mono fun η hη => hη.2).trans
        (measure_closed_list_le hν hε hε0 hcl hnd (length_of_mem_starWalkLists hl))
    · have : E l = ∅ := by
        ext η
        simp [E, hnd]
      rw [this, measure_empty]
      exact zero_le
  have hterm : ∀ n : ℕ, ν (⋃ k ∈ Finset.range (n + 1), ⋃ l ∈ starWalkLists n (z.1 + k, z.2),
      E l) ≤ ENNReal.ofReal (ε * 64 ^ 8 * (1 / 2) ^ n) := by
    intro n
    calc _ ≤ ∑ k ∈ Finset.range (n + 1), ν (⋃ l ∈ starWalkLists n (z.1 + k, z.2), E l) :=
          measure_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ Finset.range (n + 1), ∑ l ∈ starWalkLists n (z.1 + k, z.2), ν (E l) :=
          Finset.sum_le_sum fun k _ => measure_biUnion_finset_le _ _
      _ ≤ ∑ _k ∈ Finset.range (n + 1), (9 ^ n) • ENNReal.ofReal (ε * 64 ^ 8 * (64 : ℝ)⁻¹ ^ n) :=
          Finset.sum_le_sum fun k _ =>
            (Finset.sum_le_card_nsmul _ _ _ fun l hl => hE n _ l hl).trans
              (nsmul_le_nsmul_left zero_le (card_starWalkLists_le n _))
      _ = ENNReal.ofReal (((n : ℝ) + 1) * 9 ^ n * (ε * 64 ^ 8 * (64 : ℝ)⁻¹ ^ n)) := by
          have ha : ENNReal.ofReal (((n : ℝ) + 1) * 9 ^ n) = ((n + 1) * 9 ^ n : ℕ) := by
            rw [← ENNReal.ofReal_natCast]
            norm_num
          rw [Finset.sum_const, Finset.card_range, smul_smul, nsmul_eq_mul,
            ENNReal.ofReal_mul (p := ((n : ℝ) + 1) * 9 ^ n) (by positivity), ha]
      _ ≤ ENNReal.ofReal (ε * 64 ^ 8 * (1 / 2) ^ n) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := mul_le_mul_of_nonneg_left (succ_mul_nine_pow_le n)
            (by positivity : (0 : ℝ) ≤ ε * 64 ^ 8)
          calc ((n : ℝ) + 1) * 9 ^ n * (ε * 64 ^ 8 * (64 : ℝ)⁻¹ ^ n) =
              ε * 64 ^ 8 * (((n : ℝ) + 1) * 9 ^ n * (64 : ℝ)⁻¹ ^ n) := by ring
            _ ≤ _ := this
  have hU : ν (⋃ n : ℕ, ⋃ k ∈ Finset.range (n + 1), ⋃ l ∈ starWalkLists n (z.1 + k, z.2), E l)
      ≤ ENNReal.ofReal (2 * 64 ^ 8 * ε) := by
    calc _ ≤ ∑' n : ℕ, ν (⋃ k ∈ Finset.range (n + 1),
          ⋃ l ∈ starWalkLists n (z.1 + k, z.2), E l) := measure_iUnion_le _
      _ ≤ ∑' n : ℕ, ENNReal.ofReal (ε * 64 ^ 8 * (1 / 2) ^ n) := ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (∑' n : ℕ, ε * 64 ^ 8 * (1 / 2) ^ n) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
            (summable_geometric_two.mul_left _)).symm
      _ = ENNReal.ofReal (2 * 64 ^ 8 * ε) := by
          rw [tsum_mul_left, tsum_geometric_two]
          congr 1
          ring
  calc ν {η | ¬ InInfiniteSiteCluster η z}
      ≤ ν ({η | η z = false} ∪ ⋃ n : ℕ, ⋃ k ∈ Finset.range (n + 1),
          ⋃ l ∈ starWalkLists n (z.1 + k, z.2), E l) := measure_mono hsub
    _ ≤ ν {η | η z = false} + ν (⋃ n : ℕ, ⋃ k ∈ Finset.range (n + 1),
          ⋃ l ∈ starWalkLists n (z.1 + k, z.2), E l) := measure_union_le _ _
    _ ≤ ENNReal.ofReal ε + ENNReal.ofReal (2 * 64 ^ 8 * ε) := add_le_add (hcl z) hU
    _ = ENNReal.ofReal (ε + 2 * 64 ^ 8 * ε) := (ENNReal.ofReal_add hε (by positivity)).symm
    _ ≤ ENNReal.ofReal (64 ^ 9 * ε) := ENNReal.ofReal_le_ofReal (by nlinarith)

/-- Step `step:5.21-peierls`, with exponent `a = 1` and `C₀ = 64⁹`. -/
theorem oneDependentPeierlsStep : OneDependentPeierlsStep :=
  ⟨64 ^ 9, 1, by positivity, one_pos, fun _ _ hν _ hε hcl z => by
    rw [Real.rpow_one]
    exact measure_not_inInfiniteSiteCluster_le hν hε hcl z⟩

/-- Step `step:5.21-site-density` (Grimmett, *Percolation*, Theorem 8.92 in the printed proof),
with `C = 64⁹`: Bernoulli site percolation is `1`-dependent. -/
theorem siteDensityNearOneStep : SiteDensityNearOneStep := by
  refine ⟨64 ^ 9, by positivity, fun q hq z => ?_⟩
  refine measure_not_inInfiniteSiteCluster_le (kDependentPlanar_bernoulliFieldPlanar 1 q hq)
    (sub_nonneg.mpr (by exact_mod_cast hq)) (fun s => ?_) z
  have hs : {η : PlanarCarrier → Bool | η s = false} = {η | η s = true}ᶜ := by
    ext η
    simp
  have hm : MeasurableSet {η : PlanarCarrier → Bool | η s = true} := by
    have h := (measurable_pi_apply s : Measurable fun f : PlanarCarrier → Bool => f s)
      (measurableSet_singleton (true : Bool))
    simpa [Set.preimage, Set.mem_singleton_iff] using h
  rw [hs, prob_compl_eq_one_sub hm,
    bernoulliFieldPlanar_oneSite, ENNReal.ofReal_sub _ (NNReal.coe_nonneg q), ENNReal.ofReal_one]

end Rigidity.Proofs.Section5
