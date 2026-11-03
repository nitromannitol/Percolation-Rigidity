import Rigidity.Proofs.Section5.GoodEventMeasurable
import Rigidity.Steps.Section5.GoodEventDensity

/-!
# Lemma 5.26: the corrected-plane quantifier of the printed good event

This file is not used by the main theorems. The draft statement `GoodEventDensityStmt`
(Lemma 5.26) asks for the null-measurability of the good event, proved in
`GoodEventMeasurable.lean`. This file studies the measurability in the product σ-algebra of the
printed good event `eventGPrinted` (existential `G_1`, `G_3` on the edge `(x, x + e₁)`; replaced
in the corrected draft by [C31], [C32]). The events `G_2(x, K)`
and `G_3(x, C_χ)` quantify over all corrected planes `ℓ` of slope `e₁` of the infinite cluster, on
every environment. This file records what that quantifier is on every environment (not only
almost surely).

The corrected planes of slope `e₁` on `𝒞_∞(ω)` form an affine space `Γ_ω = ℓ₀ + S_ω`, where `S_ω`
is the space of harmonic functions of `A₁(𝒞_∞)` with sublinear growth
(`isCorrectedPlane_add_smul_sub`: `ℓ + t (ℓ - ℓ')` is a corrected plane).

* `not_mem_eventG2_of_two_planes`: if two corrected planes do not differ by a constant, then
  `G_2(x, K)` fails for every `x` and `K` (the oscillation of `ℓ + t (ℓ - ℓ')` on a cube containing
  two points where `ℓ - ℓ'` differs is unbounded in `t`).
* `mem_eventG2_of_no_plane`, `mem_eventG3Edge_iff_of_no_plane`: if there is no corrected plane, then
  `G_2(x, K)` holds and `G_3(x, C_χ)` reduces to the adjacency of `x` and `x + e₁` in `𝒞_∞`.
* `eventG2_subset_planeDichotomy`: `G_2(x, K)` lies in the event that the corrected plane of slope
  `e₁` either does not exist or is unique up to additive constants.
* `mem_eventG2_iff_of_unique`, `eventG2_inter_eventG3Edge`: with a corrected plane unique up to
  constants, `G_2(x, K)` is its oscillation bound; `G_2(x, K) ∩ G_3(x, C_χ) = planeGoodEvent x C_χ K`
  on every environment.
* `eventGPrinted_eq_inter_planeGoodEvent`, `measurableSet_eventGPrinted_of_planeGoodEvent`: since
  `G_1` is measurable, the measurability of the printed good event follows from that of
  `planeGoodEvent 0 C_χ K`.

Hence `G_2 ∩ G_3` is the union of the event where no corrected plane exists (with the adjacency)
and the event where the corrected plane exists, is unique up to constants, and satisfies the
conditions of `G_2` and `G_3`. The existence event is the projection of a Borel subset of
`Configuration 2 × (Vertex 2 → ℝ)` (analytic), the uniqueness event is co-analytic, and
`G(0, C_χ, K)` is co-analytic. On null sets of environments the space `S_ω` is nontrivial (two
half-planes joined by one edge carry a harmonic function of logarithmic growth) and can be
infinite-dimensional, so the sections of the corrected-plane relation are neither singletons nor
countable nor σ-compact, and neither the Lusin–Souslin theorem
(`MeasurableSet.image_of_measurable_injOn`) nor the Lusin–Novikov or Arsenin–Kunugui
uniformization theorems applies. The measurability of `G(0, C_χ, K)` in the product σ-algebra is
therefore open; its null-measurability is proved in
`Rigidity.Proofs.Section5.GoodEventMeasurable`.
-/

open LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

open Rigidity.Section5 Rigidity.Steps.Section5

variable {ω : Configuration 2}

/-- The corrected planes of a given slope form an affine space: `u + t (u - v)` is a corrected
plane whenever `u` and `v` are. -/
theorem isCorrectedPlane_add_smul_sub {C : OpenComponent ω} {q : Fin 2 → ℝ} {u v : C → ℝ}
    (hu : IsCorrectedPlane C q u) (hv : IsCorrectedPlane C q v) (t : ℝ) :
    IsCorrectedPlane C q (u + t • (u - v)) := by
  refine ⟨(harmonicGrowthSpace C 1).add_mem hu.1
    ((harmonicGrowthSpace C 1).smul_mem t ((harmonicGrowthSpace C 1).sub_mem hu.1 hv.1)), ?_⟩
  intro ε hε
  have hc : 0 < 1 + 2 * |t| := by positivity
  obtain ⟨R₁, hR₁, H₁⟩ := hu.2 (ε / (1 + 2 * |t|)) (div_pos hε hc)
  obtain ⟨R₂, -, H₂⟩ := hv.2 (ε / (1 + 2 * |t|)) (div_pos hε hc)
  refine ⟨max R₁ R₂, lt_max_of_lt_left hR₁, fun R hR x hx => ?_⟩
  have h₁ := H₁ R (le_of_max_le_left hR) x hx
  have h₂ := H₂ R (le_of_max_le_right hR) x hx
  set s := componentSlope C q x
  have hR0 : 0 ≤ R := hR₁.le.trans (le_of_max_le_left hR)
  have key : (u + t • (u - v)) x - s = (1 + t) * (u x - s) - t * (v x - s) := by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring
  have hδ : ε / (1 + 2 * |t|) * R * (1 + 2 * |t|) = ε * R := by
    field_simp
  rw [key]
  calc |(1 + t) * (u x - s) - t * (v x - s)|
      ≤ |1 + t| * |u x - s| + |t| * |v x - s| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul]
    _ ≤ (1 + |t|) * (ε / (1 + 2 * |t|) * R) + |t| * (ε / (1 + 2 * |t|) * R) := by
        gcongr
        exact (abs_add_le 1 t).trans (by rw [abs_one])
    _ = ε * R := by rw [← hδ]; ring

/-- Two corrected planes of slope `e₁` that do not differ by a constant force the failure of
`G_2(x, K)`, for every `x` and every `K`. -/
theorem not_mem_eventG2_of_two_planes (h : HasUniqueInfiniteOpenComponent ω)
    {ℓ ℓ' : uniqueInfiniteComponent h → ℝ}
    (hℓ : IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ)
    (hℓ' : IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ')
    {y z : uniqueInfiniteComponent h} (hyz : ℓ y - ℓ' y ≠ ℓ z - ℓ' z) (x : Vertex 2) (K : ℝ) :
    ω ∉ eventG2 x K := by
  rintro ⟨h', H⟩
  -- choose the ordered pair `(a, b)` on which `ℓ - ℓ'` increases
  obtain ⟨a, b, hD⟩ : ∃ a b : uniqueInfiniteComponent h, 0 < (ℓ a - ℓ' a) - (ℓ b - ℓ' b) := by
    rcases lt_or_gt_of_ne hyz with hlt | hlt
    · exact ⟨z, y, by linarith⟩
    · exact ⟨y, z, by linarith⟩
  set D := (ℓ a - ℓ' a) - (ℓ b - ℓ' b)
  -- a cube around `x` of radius at least `K` containing `a` and `b`
  set N : ℕ := (|a.val 0 - x 0| + |a.val 1 - x 1| + |b.val 0 - x 0| + |b.val 1 - x 1|).toNat
    + ⌈K⌉₊ with hN
  have hNz : |a.val 0 - x 0| + |a.val 1 - x 1| + |b.val 0 - x 0| + |b.val 1 - x 1| ≤ (N : ℤ) := by
    rw [hN]; push_cast; linarith [Int.self_le_toNat
      (|a.val 0 - x 0| + |a.val 1 - x 1| + |b.val 0 - x 0| + |b.val 1 - x 1|)]
  have ha : a.val ∈ cubeAt x N := by
    intro i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;>
      linarith [abs_nonneg (a.val 0 - x 0), abs_nonneg (a.val 1 - x 1),
        abs_nonneg (b.val 0 - x 0), abs_nonneg (b.val 1 - x 1)]
  have hb : b.val ∈ cubeAt x N := by
    intro i
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;>
      linarith [abs_nonneg (a.val 0 - x 0), abs_nonneg (a.val 1 - x 1),
        abs_nonneg (b.val 0 - x 0), abs_nonneg (b.val 1 - x 1)]
  have hKN : K ≤ (N : ℝ) := by
    rw [hN]; push_cast
    have : (0 : ℝ) ≤ ((|a.val 0 - x 0| + |a.val 1 - x 1| + |b.val 0 - x 0| +
      |b.val 1 - x 1|).toNat : ℝ) := Nat.cast_nonneg _
    linarith [Nat.le_ceil K]
  -- the corrected plane `ℓ + t (ℓ - ℓ')` with oscillation `4N + 1` between `a` and `b`
  set t := (4 * (N : ℝ) - (ℓ a - ℓ b) + 1) / D
  have htD : t * D = 4 * (N : ℝ) - (ℓ a - ℓ b) + 1 := div_mul_cancel₀ _ hD.ne'
  have hbound := H (ℓ + t • (ℓ - ℓ')) (isCorrectedPlane_add_smul_sub hℓ hℓ' t) N hKN a b ha hb
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at hbound
  have : ℓ a + t * (ℓ a - ℓ' a) - (ℓ b + t * (ℓ b - ℓ' b)) = ℓ a - ℓ b + t * D := by
    simp only [D]; ring
  linarith

/-- Without a corrected plane of slope `e₁`, the event `G_2(x, K)` holds. -/
theorem mem_eventG2_of_no_plane (h : HasUniqueInfiniteOpenComponent ω)
    (hno : ∀ ℓ, ¬IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ)
    (x : Vertex 2) (K : ℝ) : ω ∈ eventG2 x K :=
  ⟨h, fun ℓ hℓ => (hno ℓ hℓ).elim⟩

/-- Without a corrected plane of slope `e₁`, the event `G_3(x, C_χ)` is the adjacency of `x` and
`x + e₁` in `𝒞_∞`. -/
theorem mem_eventG3Edge_iff_of_no_plane (h : HasUniqueInfiniteOpenComponent ω)
    (hno : ∀ ℓ, ¬IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ)
    (x : Vertex 2) (Cχ : ℝ) :
    ω ∈ eventG3Edge x Cχ ↔ ∃ hx : x ∈ (uniqueInfiniteComponent h).supp,
      ∃ hx' : x + e1 ∈ (uniqueInfiniteComponent h).supp,
        (componentGraph _).Adj ⟨x, hx⟩ ⟨x + e1, hx'⟩ := by
  constructor
  · rintro ⟨h', hx, hx', hadj, -⟩
    exact ⟨hx, hx', hadj⟩
  · rintro ⟨hx, hx', hadj⟩
    exact ⟨h, hx, hx', hadj, fun ℓ hℓ => (hno ℓ hℓ).elim⟩

/-- The dichotomy event: the infinite cluster is unique and its corrected plane of slope `e₁`
either does not exist or is unique up to additive constants. -/
def planeDichotomy : Set (Configuration 2) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω,
    (∀ ℓ, ¬IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ) ∨
    ∃ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ ∧
      ∀ ℓ', IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ' →
        ∀ y z, ℓ' y - ℓ' z = ℓ y - ℓ z}

/-- `G_2(x, K)` lies in the dichotomy event: on `G_2(x, K)` the corrected plane of slope `e₁`
either does not exist or is unique up to additive constants. -/
theorem eventG2_subset_planeDichotomy (x : Vertex 2) (K : ℝ) : eventG2 x K ⊆ planeDichotomy := by
  intro ω hω
  obtain ⟨h, -⟩ := id hω
  refine ⟨h, ?_⟩
  by_cases hex : ∃ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ
  · obtain ⟨ℓ, hℓ⟩ := hex
    refine Or.inr ⟨ℓ, hℓ, fun ℓ' hℓ' y z => ?_⟩
    by_contra hne
    exact not_mem_eventG2_of_two_planes h hℓ' hℓ (y := y) (z := z)
      (fun h' => hne (by linarith)) x K hω
  · exact Or.inl fun ℓ hℓ => hex ⟨ℓ, hℓ⟩

/-- With a corrected plane `ℓ` of slope `e₁` unique up to additive constants, `G_2(x, K)` is the
oscillation bound for `ℓ`. -/
theorem mem_eventG2_iff_of_unique (h : HasUniqueInfiniteOpenComponent ω)
    {ℓ : uniqueInfiniteComponent h → ℝ}
    (hℓ : IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ)
    (hu : ∀ ℓ', IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ' →
      ∀ y z, ℓ' y - ℓ' z = ℓ y - ℓ z) (x : Vertex 2) (K : ℝ) :
    ω ∈ eventG2 x K ↔ ∀ R' : ℕ, K ≤ R' → ∀ y z : uniqueInfiniteComponent h,
      y.val ∈ cubeAt x R' → z.val ∈ cubeAt x R' → ℓ y - ℓ z ≤ 4 * R' := by
  constructor
  · rintro ⟨h', H⟩
    exact H ℓ hℓ
  · intro H
    refine ⟨h, fun ℓ' hℓ' R' hR y z hy hz => ?_⟩
    rw [hu ℓ' hℓ' y z]
    exact H R' hR y z hy hz

/-- The event `G_2(x, K) ∩ G_3(x, C_χ)` in terms of the dichotomy: `x` and `x + e₁` are adjacent
in `𝒞_∞`, and either there is no corrected plane of slope `e₁`, or there is one, unique up to
additive constants, satisfying the oscillation bound of `G_2(x, K)` and the increment bound of
`G_3(x, C_χ)`. -/
def planeGoodEvent (x : Vertex 2) (Cχ K : ℝ) : Set (Configuration 2) :=
  {ω | ∃ h : HasUniqueInfiniteOpenComponent ω, ∃ hx : x ∈ (uniqueInfiniteComponent h).supp,
    ∃ hx' : x + e1 ∈ (uniqueInfiniteComponent h).supp,
      (componentGraph _).Adj ⟨x, hx⟩ ⟨x + e1, hx'⟩ ∧
      ((∀ ℓ, ¬IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ) ∨
        ∃ ℓ, IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ ∧
          (∀ ℓ', IsCorrectedPlane (uniqueInfiniteComponent h) (Pi.single 0 1) ℓ' →
            ∀ y z, ℓ' y - ℓ' z = ℓ y - ℓ z) ∧
          (∀ R' : ℕ, K ≤ R' → ∀ y z : uniqueInfiniteComponent h,
            y.val ∈ cubeAt x R' → z.val ∈ cubeAt x R' → ℓ y - ℓ z ≤ 4 * R') ∧
          Cχ ≤ ℓ ⟨x + e1, hx'⟩ - ℓ ⟨x, hx⟩)}

/-- `G_2(x, K) ∩ G_3(x, C_χ)` is the dichotomy event `planeGoodEvent x C_χ K`, on every
environment. -/
theorem eventG2_inter_eventG3Edge (x : Vertex 2) (Cχ K : ℝ) :
    eventG2 x K ∩ eventG3Edge x Cχ = planeGoodEvent x Cχ K := by
  ext ω
  constructor
  · rintro ⟨h2, h, hx, hx', hadj, H3⟩
    refine ⟨h, hx, hx', hadj, ?_⟩
    obtain ⟨h', hd⟩ := eventG2_subset_planeDichotomy x K h2
    rcases hd with hno | ⟨ℓ, hℓ, hu⟩
    · exact Or.inl hno
    · exact Or.inr ⟨ℓ, hℓ, hu, (mem_eventG2_iff_of_unique h hℓ hu x K).1 h2, H3 ℓ hℓ⟩
  · rintro ⟨h, hx, hx', hadj, hno | ⟨ℓ, hℓ, hu, h2, h3⟩⟩
    · exact ⟨mem_eventG2_of_no_plane h hno x K, h, hx, hx', hadj, fun ℓ hℓ => (hno ℓ hℓ).elim⟩
    · refine ⟨(mem_eventG2_iff_of_unique h hℓ hu x K).2 h2, h, hx, hx', hadj, fun ℓ' hℓ' => ?_⟩
      rw [hu ℓ' hℓ']
      exact h3

/-- The good event is `G_1(x, K) ∩ planeGoodEvent x C_χ K`, on every environment. -/
theorem eventGPrinted_eq_inter_planeGoodEvent (Cf : ℕ) (R c₁ : ℝ) (x : Vertex 2) (Cχ K : ℝ) :
    eventGPrinted Cf R c₁ x Cχ K = eventG1Exists Cf R c₁ x K ∩ planeGoodEvent x Cχ K := by
  rw [eventGPrinted, Set.inter_assoc, eventG2_inter_eventG3Edge]

/-- The reduction of `GoodEventMeasurableStep`: since `G_1(0, K)` is measurable
(`measurableSet_eventG1Exists`), the measurability of the good event is the measurability of the
dichotomy events `planeGoodEvent 0 C_χ K`. -/
theorem measurableSet_eventGPrinted_of_planeGoodEvent
    (hP : ∀ Cχ K : ℝ, MeasurableSet (planeGoodEvent 0 Cχ K)) :
    ∀ (Cf : ℕ) (R c₁ Cχ K : ℝ), MeasurableSet (eventGPrinted Cf R c₁ 0 Cχ K) :=
  fun Cf R c₁ Cχ K => by
  rw [eventGPrinted_eq_inter_planeGoodEvent]
  exact (measurableSet_eventG1Exists Cf R c₁ 0 K).inter (hP Cχ K)

end Rigidity.Proofs.Section5
