import LatticeProb.Site
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
# A discrete Sobolev inequality with mixed differences

For a function `g` on `ℤ^d`, the mixed forward difference in the directions of a set `S` of
coordinates is `D_S g(y) = ∑_{U ⊆ S} (-1)^{|S| - |U|} g(y + ∑_{j ∈ U} e_j)` (`mixedDiff`); it is
the composition of the forward differences `D_j g(y) = g(y + e_j) - g(y)`, `j ∈ S`
(`mixedDiff_insert`). The discrete Sobolev inequality bounds the value of `g` at a corner `x₀` of
the box `x₀ + [0, n]^T` (the coordinates outside `T` fixed) by
`|g(x₀)| ≤ ∑_{S ⊆ T} (n + 1)^{-(|T| - |S|)} ∑_{y ∈ box} |D_S g(y)|`
(`abs_le_sum_mixedDiff`): in one direction, `g(x₀)` is the average over `k ≤ n` of
`g(x₀ + k e_i) - ∑_{j < k} D_i g(x₀ + j e_i)`, and the general case follows by induction on `T`.

With `T` all the coordinates, the mixed differences of order at most `d` of a discrete harmonic
function are bounded in `ℓ²` by iterated Caccioppoli inequalities, and the inequality gives the
interior `L^∞` bound of discrete harmonic functions by their normalized `ℓ²` norm, an ingredient
of the excess decay (`HarmonicRegularity`) of discrete harmonic functions on lattice balls.
-/

namespace Rigidity.Proofs.Regularity

open Finset LatticeProb

variable {d : ℕ}

/-- The vertex `∑_{j ∈ U} e_j`. -/
def shiftSum (U : Finset (Fin d)) : Fin d → ℤ := ∑ j ∈ U, unit j

/-- The mixed forward difference `D_S g(y) = ∑_{U ⊆ S} (-1)^{|S| - |U|} g(y + ∑_{j ∈ U} e_j)`. -/
def mixedDiff (S : Finset (Fin d)) (g : (Fin d → ℤ) → ℝ) (y : Fin d → ℤ) : ℝ :=
  ∑ U ∈ S.powerset, (-1 : ℝ) ^ (S.card - U.card) * g (y + shiftSum U)

theorem mixedDiff_empty (g : (Fin d → ℤ) → ℝ) (y : Fin d → ℤ) : mixedDiff ∅ g y = g y := by
  simp [mixedDiff, shiftSum]

theorem shiftSum_insert {U : Finset (Fin d)} {i : Fin d} (hi : i ∉ U) :
    shiftSum (insert i U) = unit i + shiftSum U :=
  Finset.sum_insert hi

/-- Adding a direction to a mixed difference takes one more forward difference. -/
theorem mixedDiff_insert {S : Finset (Fin d)} {i : Fin d} (hi : i ∉ S) (g : (Fin d → ℤ) → ℝ)
    (y : Fin d → ℤ) :
    mixedDiff (insert i S) g y = mixedDiff S g (y + unit i) - mixedDiff S g y := by
  rw [mixedDiff, Finset.sum_powerset_insert hi]
  have h1 : ∀ U ∈ S.powerset, (-1 : ℝ) ^ ((insert i S).card - U.card) * g (y + shiftSum U) =
      -((-1 : ℝ) ^ (S.card - U.card) * g (y + shiftSum U)) := by
    intro U hU
    have hUS := card_le_card (mem_powerset.1 hU)
    rw [card_insert_of_notMem hi, Nat.succ_sub hUS, pow_succ]
    ring
  have h2 : ∀ U ∈ S.powerset, (-1 : ℝ) ^ ((insert i S).card - (insert i U).card) *
      g (y + shiftSum (insert i U)) =
        (-1 : ℝ) ^ (S.card - U.card) * g ((y + unit i) + shiftSum U) := by
    intro U hU
    have hiU : i ∉ U := fun h => hi (mem_powerset.1 hU h)
    rw [card_insert_of_notMem hi, card_insert_of_notMem hiU, Nat.add_sub_add_right,
      shiftSum_insert hiU, add_assoc]
  rw [sum_congr rfl h1, sum_congr rfl h2, sum_neg_distrib, mixedDiff, mixedDiff]
  ring

/-- Mixed differences commute with translations. -/
theorem mixedDiff_comp_add (S : Finset (Fin d)) (g : (Fin d → ℤ) → ℝ) (v y : Fin d → ℤ) :
    mixedDiff S (fun x => g (x + v)) y = mixedDiff S g (y + v) := by
  simp only [mixedDiff]
  refine sum_congr rfl fun U _ => ?_
  rw [add_right_comm]

/-- Mixed differences are linear. -/
theorem mixedDiff_sub (S : Finset (Fin d)) (g₁ g₂ : (Fin d → ℤ) → ℝ) (y : Fin d → ℤ) :
    mixedDiff S (fun x => g₁ x - g₂ x) y = mixedDiff S g₁ y - mixedDiff S g₂ y := by
  simp only [mixedDiff, mul_sub, sum_sub_distrib]

/-- The mixed difference of the forward difference `D_i g` in the directions `S ∌ i`. -/
theorem mixedDiff_forwardDiff {S : Finset (Fin d)} {i : Fin d} (hi : i ∉ S)
    (g : (Fin d → ℤ) → ℝ) (y : Fin d → ℤ) :
    mixedDiff S (fun x => g (x + unit i) - g x) y = mixedDiff (insert i S) g y := by
  rw [mixedDiff_sub, mixedDiff_comp_add, mixedDiff_insert hi]

/-- The box `x₀ + [0, n]^T`, the coordinates outside `T` equal to those of `x₀`. -/
noncomputable def latticeBox (T : Finset (Fin d)) (x₀ : Fin d → ℤ) (n : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun j => if j ∈ T then Icc (x₀ j) (x₀ j + n) else {x₀ j}

theorem latticeBox_empty (x₀ : Fin d → ℤ) (n : ℕ) : latticeBox ∅ x₀ n = {x₀} := by
  ext y
  simp only [latticeBox, Fintype.mem_piFinset, Finset.notMem_empty, if_false, mem_singleton]
  exact ⟨fun h => funext h, fun h j => by rw [h]⟩

theorem add_smul_unit_apply (x₀ : Fin d → ℤ) (k : ℤ) (i j : Fin d) :
    (x₀ + k • unit i) j = if j = i then x₀ j + k else x₀ j := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, unit, Pi.single_apply]
  split_ifs <;> ring

theorem mem_latticeBox {T : Finset (Fin d)} {x₀ y : Fin d → ℤ} {n : ℕ} :
    y ∈ latticeBox T x₀ n ↔ ∀ j, (j ∈ T → x₀ j ≤ y j ∧ y j ≤ x₀ j + n) ∧ (j ∉ T → y j = x₀ j) := by
  simp only [latticeBox, Fintype.mem_piFinset]
  refine forall_congr' fun j => ?_
  split_ifs with h
  · simp [mem_Icc, h]
  · simp [h]

/-- The box `x₀ + [0, n]^{T ∪ {i}}` is the disjoint union over `k ≤ n` of the boxes
`x₀ + k e_i + [0, n]^T`. -/
theorem latticeBox_insert {T : Finset (Fin d)} {i : Fin d} (hi : i ∉ T) (x₀ : Fin d → ℤ)
    (n : ℕ) :
    latticeBox (insert i T) x₀ n =
      (range (n + 1)).biUnion fun k => latticeBox T (x₀ + (k : ℤ) • unit i) n := by
  ext y
  simp only [mem_biUnion, mem_range, mem_latticeBox, add_smul_unit_apply]
  constructor
  · intro hy
    obtain ⟨hyi, _⟩ := hy i
    have hyi' := hyi (mem_insert_self i T)
    refine ⟨(y i - x₀ i).toNat, by omega, fun j => ⟨fun hjT => ?_, fun hjT => ?_⟩⟩
    · have hji : j ≠ i := fun h => hi (h ▸ hjT)
      simpa [hji] using (hy j).1 (mem_insert_of_mem hjT)
    · by_cases hji : j = i
      · subst hji
        rw [if_pos rfl]
        omega
      · simpa [hji] using (hy j).2 (fun h => hjT ((mem_insert.1 h).resolve_left hji))
  · rintro ⟨k, hk, hy⟩ j
    refine ⟨fun hj => ?_, fun hj => ?_⟩
    · by_cases hji : j = i
      · subst hji
        have := (hy j).2 hi
        rw [if_pos rfl] at this
        omega
      · have hjT : j ∈ T := (mem_insert.1 hj).resolve_left hji
        simpa [hji] using (hy j).1 hjT
    · have hji : j ≠ i := fun h => hj (h ▸ mem_insert_self i T)
      have hjT : j ∉ T := fun h => hj (mem_insert_of_mem h)
      simpa [hji] using (hy j).2 hjT

theorem latticeBox_pairwiseDisjoint {T : Finset (Fin d)} {i : Fin d} (hi : i ∉ T)
    (x₀ : Fin d → ℤ) (n : ℕ) :
    ((range (n + 1) : Set ℕ)).PairwiseDisjoint
      fun k => latticeBox T (x₀ + (k : ℤ) • unit i) n := by
  intro k _ k' _ hkk'
  rw [Function.onFun, Finset.disjoint_left]
  intro y hy hy'
  rw [mem_latticeBox] at hy hy'
  have h1 := (hy i).2 hi
  have h2 := (hy' i).2 hi
  rw [add_smul_unit_apply, if_pos rfl] at h1 h2
  exact hkk' (by omega)

/-- **One direction.** `|g(x₀)|` is at most the average of `|g|` on `x₀ + [0, n] e_i` plus the sum
of `|D_i g|` there. -/
theorem abs_le_average_add_sum_forwardDiff (g : (Fin d → ℤ) → ℝ) (x₀ : Fin d → ℤ) (i : Fin d)
    (n : ℕ) :
    |g x₀| ≤ ((n : ℝ) + 1)⁻¹ * ∑ k ∈ range (n + 1), |g (x₀ + (k : ℤ) • unit i)| +
      ∑ k ∈ range (n + 1),
        |g (x₀ + (k : ℤ) • unit i + unit i) - g (x₀ + (k : ℤ) • unit i)| := by
  set D := ∑ k ∈ range (n + 1),
    |g (x₀ + (k : ℤ) • unit i + unit i) - g (x₀ + (k : ℤ) • unit i)| with hD
  have hstep : ∀ k ∈ range (n + 1), |g x₀| ≤ |g (x₀ + (k : ℤ) • unit i)| + D := by
    intro k hk
    have htel := sum_range_sub (fun j : ℕ => g (x₀ + (j : ℤ) • unit i)) k
    have hsucc : ∀ j : ℕ, x₀ + ((j + 1 : ℕ) : ℤ) • unit i = x₀ + (j : ℤ) • unit i + unit i := by
      intro j; push_cast; rw [add_smul, one_smul, add_assoc]
    simp only [hsucc, Nat.cast_zero, zero_smul, add_zero] at htel
    have hle : |∑ j ∈ range k, (g (x₀ + (j : ℤ) • unit i + unit i) - g (x₀ + (j : ℤ) • unit i))|
        ≤ D := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by
        have := mem_range.1 hk; omega)) fun _ _ _ => abs_nonneg _
    have : g x₀ = g (x₀ + (k : ℤ) • unit i) -
        ∑ j ∈ range k, (g (x₀ + (j : ℤ) • unit i + unit i) - g (x₀ + (j : ℤ) • unit i)) := by
      rw [htel]; ring
    rw [this]
    exact (abs_sub _ _).trans (add_le_add le_rfl hle)
  have hsum := sum_le_sum hstep
  rw [sum_const, card_range, nsmul_eq_mul, sum_add_distrib, sum_const, card_range,
    nsmul_eq_mul] at hsum
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  push_cast at hsum
  have e : |g x₀| = ((n : ℝ) + 1)⁻¹ * (((n : ℝ) + 1) * |g x₀|) := by field_simp
  rw [e]
  calc ((n : ℝ) + 1)⁻¹ * (((n : ℝ) + 1) * |g x₀|)
      ≤ ((n : ℝ) + 1)⁻¹ * (∑ k ∈ range (n + 1), |g (x₀ + (k : ℤ) • unit i)| +
          ((n : ℝ) + 1) * D) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((n : ℝ) + 1)⁻¹ * ∑ k ∈ range (n + 1), |g (x₀ + (k : ℤ) • unit i)| + D := by
        field_simp

/-- Exchange of the sum over the slices `k ≤ n` with the sum over the subsets of directions. -/
theorem sum_range_sum_powerset_latticeBox {T : Finset (Fin d)} {i : Fin d} (hi : i ∉ T)
    (x₀ : Fin d → ℤ) (n : ℕ) (a : Finset (Fin d) → ℝ) (G : Finset (Fin d) → (Fin d → ℤ) → ℝ) :
    ∑ k ∈ range (n + 1), ∑ S ∈ T.powerset,
        a S * ∑ y ∈ latticeBox T (x₀ + (k : ℤ) • unit i) n, G S y =
      ∑ S ∈ T.powerset, a S * ∑ y ∈ latticeBox (insert i T) x₀ n, G S y := by
  rw [sum_comm]
  refine sum_congr rfl fun S _ => ?_
  rw [← mul_sum, latticeBox_insert hi, sum_biUnion (latticeBox_pairwiseDisjoint hi x₀ n)]

/-- **Discrete Sobolev inequality with mixed differences**:
`|g(x₀)| ≤ ∑_{S ⊆ T} (n + 1)^{-(|T| - |S|)} ∑_{y ∈ x₀ + [0, n]^T} |D_S g(y)|`. -/
theorem abs_le_sum_mixedDiff (n : ℕ) (T : Finset (Fin d)) :
    ∀ (g : (Fin d → ℤ) → ℝ) (x₀ : Fin d → ℤ),
      |g x₀| ≤ ∑ S ∈ T.powerset, (((n : ℝ) + 1)⁻¹) ^ (T.card - S.card) *
        ∑ y ∈ latticeBox T x₀ n, |mixedDiff S g y| := by
  induction T using Finset.induction_on with
  | empty =>
    intro g x₀
    simp [latticeBox_empty, mixedDiff_empty]
  | insert i T hi ih =>
    intro g x₀
    set c := ((n : ℝ) + 1)⁻¹ with hc
    have hc0 : 0 ≤ c := by positivity
    have h1 := abs_le_average_add_sum_forwardDiff g x₀ i n
    have hA : ∀ k ∈ range (n + 1), |g (x₀ + (k : ℤ) • unit i)| ≤
        ∑ S ∈ T.powerset, c ^ (T.card - S.card) *
          ∑ y ∈ latticeBox T (x₀ + (k : ℤ) • unit i) n, |mixedDiff S g y| :=
      fun k _ => ih g _
    have hB : ∀ k ∈ range (n + 1),
        |g (x₀ + (k : ℤ) • unit i + unit i) - g (x₀ + (k : ℤ) • unit i)| ≤
          ∑ S ∈ T.powerset, c ^ (T.card - S.card) *
            ∑ y ∈ latticeBox T (x₀ + (k : ℤ) • unit i) n, |mixedDiff (insert i S) g y| := by
      intro k _
      have := ih (fun x => g (x + unit i) - g x) (x₀ + (k : ℤ) • unit i)
      refine this.trans (le_of_eq (sum_congr rfl fun S hS => ?_))
      congr 1
      refine sum_congr rfl fun y _ => ?_
      rw [mixedDiff_forwardDiff (fun h => hi (mem_powerset.1 hS h))]
    have hsumA := sum_le_sum hA
    have hsumB := sum_le_sum hB
    rw [sum_range_sum_powerset_latticeBox hi] at hsumA hsumB
    rw [sum_powerset_insert hi]
    have e1 : ∀ S ∈ T.powerset, c ^ ((insert i T).card - S.card) =
        c * c ^ (T.card - S.card) := by
      intro S hS
      rw [card_insert_of_notMem hi, Nat.succ_sub (card_le_card (mem_powerset.1 hS)), pow_succ']
    have e2 : ∀ S ∈ T.powerset, c ^ ((insert i T).card - (insert i S).card) =
        c ^ (T.card - S.card) := by
      intro S hS
      have hiS : i ∉ S := fun h => hi (mem_powerset.1 hS h)
      rw [card_insert_of_notMem hi, card_insert_of_notMem hiS, Nat.add_sub_add_right]
    have hsplit :
        ∑ S ∈ T.powerset, c ^ ((insert i T).card - S.card) *
            ∑ y ∈ latticeBox (insert i T) x₀ n, |mixedDiff S g y| +
          ∑ S ∈ T.powerset, c ^ ((insert i T).card - (insert i S).card) *
            ∑ y ∈ latticeBox (insert i T) x₀ n, |mixedDiff (insert i S) g y| =
        c * ∑ S ∈ T.powerset, c ^ (T.card - S.card) *
            ∑ y ∈ latticeBox (insert i T) x₀ n, |mixedDiff S g y| +
          ∑ S ∈ T.powerset, c ^ (T.card - S.card) *
            ∑ y ∈ latticeBox (insert i T) x₀ n, |mixedDiff (insert i S) g y| := by
      congr 1
      · rw [mul_sum]
        refine sum_congr rfl fun S hS => ?_
        rw [e1 S hS]; ring
      · exact sum_congr rfl fun S hS => by rw [e2 S hS]
    rw [hsplit]
    have := mul_le_mul_of_nonneg_left hsumA hc0
    linarith

end Rigidity.Proofs.Regularity
