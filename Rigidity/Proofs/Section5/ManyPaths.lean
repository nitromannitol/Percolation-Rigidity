import Rigidity.Steps.Section5.NoThickPaths
import Rigidity.Proofs.Section5.LoopFromCrossings
import PercolationClusterHomogenization.Proofs.Planar.ManyPaths

/-!
# Lemma 5.19: many disjoint paths from `γ` to the support of `u`

This file proves `ManyPathsStep` (`step:5.19-many-paths`, corrected draft L2040-2043). No
literature input is used: the only planar topology is the following
discrete fact about the winding number `windingNumber` of Lemma 5.14.

* `exists_eq_of_crossing`: a lattice loop in the annulus `Q_{2m} \ Q_m` with nonzero winding
  number around the origin meets every lattice path from `Q_m` to the complement of `Q_{2m}`.
  Its proof uses the sum `windAt β y` of the angle increments of the loop `β` seen from `y`. For
  adjacent lattice points `y`, `y'` off the loop, the increment `θ(y) - θ(y')` along a unit step
  `a → b` of the loop equals `h(b) - h(a)` with `h(p) = arg ((p - y) / (p - y'))`: the two sides
  agree modulo `2π`, and all four principal arguments lie in `(-π/2, π/2)` because two nonzero
  lattice vectors differing by a unit vector have a positive inner product. Summing over the
  closed loop gives `windAt β y = windAt β y'` (`windAt_eq_of_step`). Far from the loop the
  increments telescope (`windAt_eq_zero_of_not_mem_cube`), and `windAt` is constant on `Q_m`.

At each scale `m = S₀ 2^j` the loop of Lemma 5.14 meets the path of Lemma 5.18 from `Q_R` to the
complement of `Q_{2m+1}`, where `u ≠ 0`, and the bi-infinite path `γ`, which visits `Q_R` and
leaves every cube. Walking along the loop from its meeting point with the path of Lemma 5.18 to
its first vertex on `γ` and
reversing gives an arc `ρ` from `γ(k)` to a vertex where `u ≠ 0`, meeting `γ` only at its initial
point (`exists_arc_of_loop`). As `S₀` exceeds the scale of the stretch of `γ` between its first
and last visits to `Q_R`, each `k` lies on one of the two tails of `γ`; infinitely many scales
share a tail, and `N` of them give the paths. Arcs at different scales lie in disjoint annuli.
-/

open LatticeProb.Percolation Rigidity.Section5 Rigidity.Steps.Section5

namespace Rigidity.Proofs.Section5

/-! ### The winding number of a lattice loop around a lattice point -/

/-! ### Arcs of the loops from `γ` to the support of `u` -/

variable {ω : Configuration 2}

open Fin.NatCast

/-- The index `min i n` of `Fin (n + 1)`. -/
def finClamp (n i : ℕ) : Fin (n + 1) := ⟨min i n, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- At a scale `m`, a loop of `𝒞_∞` in `Q_{2m} \ Q_m` with nonzero winding number, a path of
`𝒞_∞` from `Q_m` to the complement of `Q_{2m}` on which `u ≠ 0`, and a bi-infinite path `γ`
visiting `Q_m` give an arc of the loop from a vertex `γ k` to a vertex where `u ≠ 0`, meeting `γ`
only at its initial point. -/
theorem exists_arc_of_loop {C : OpenComponent ω} {u : C → ℝ} {m n : ℕ} {β : Fin (n + 1) → C}
    (hβa : ∀ i, (componentGraph C).Adj (β i) (β (i + 1)))
    (hβm : ∀ i, (β i).val ∈ cube (2 * m) \ cube m)
    (hβw : windingNumber (fun i => (β i).val) ≠ 0) {n' : ℕ} {π : Fin (n' + 1) → C}
    (hπa : ∀ i : Fin n', (componentGraph C).Adj (π i.castSucc) (π i.succ))
    (hπ0 : (π 0).val ∈ cube m) (hπL : (π (Fin.last n')).val ∉ cube (2 * m))
    (hπu : ∀ i, u (π i) ≠ 0) {γ : ℤ → C} (hγi : Function.Injective γ)
    (hγa : ∀ k, (componentGraph C).Adj (γ k) (γ (k + 1))) {c : ℤ} (hc : (γ c).val ∈ cube m) :
    ∃ (k : ℤ) (ℓ : ℕ) (ρ : ℕ → C), (∀ i < ℓ, (componentGraph C).Adj (ρ i) (ρ (i + 1))) ∧
      ρ 0 = γ k ∧ (∀ i, 0 < i → i ≤ ℓ → ρ i ∉ Set.range γ) ∧
      (∀ i ≤ ℓ, (ρ i).val ∈ cube (2 * m) \ cube m) ∧ u (ρ ℓ) ≠ 0 := by
  have hβs : ∀ i, latticeL1Dist (β i).val (β (i + 1)).val = 1 := fun i =>
    latticeL1Dist_eq_one_of_adj (hβa i)
  have hw : windAt (fun i => (β i).val) 0 ≠ 0 := by
    intro h
    apply hβw
    rw [windingNumber_eq_windAt, h, zero_div]
  -- the loop meets the path where `u ≠ 0`
  obtain ⟨i0, -, t0, ht0⟩ := exists_eq_of_crossing (β := fun i => (β i).val) hβs hβm hw
    (P := fun i => (π (finClamp n' i)).val) (L := n')
    (fun i hi => by
      have e1 : finClamp n' i = Fin.castSucc ⟨i, hi⟩ := Fin.ext (by simp [finClamp]; omega)
      have e2 : finClamp n' (i + 1) = Fin.succ ⟨i, hi⟩ := Fin.ext (by simp [finClamp]; omega)
      simp only [e1, e2]
      exact latticeL1Dist_eq_one_of_adj (hπa ⟨i, hi⟩))
    (by rwa [show finClamp n' 0 = 0 from Fin.ext (by simp [finClamp])])
    (by rwa [show finClamp n' n' = Fin.last n' from Fin.ext (by simp [finClamp])])
  have ht0' : β t0 = π (finClamp n' i0) := Subtype.ext ht0
  -- the loop meets `γ`
  have hfin : {k : ℤ | (γ k).val ∈ cube (2 * m)}.Finite :=
    (cube_finite (2 * m)).preimage (Subtype.val_injective.comp hγi).injOn
  obtain ⟨B, hB⟩ := hfin.bddAbove
  have hn1 : (γ (c + ((max c (B + 1) - c).toNat : ℤ))).val ∉ cube (2 * m) := by
    intro h
    have := hB h
    omega
  obtain ⟨i1, -, t1, ht1⟩ := exists_eq_of_crossing (β := fun i => (β i).val) hβs hβm hw
    (P := fun i => (γ (c + (i : ℤ))).val) (L := (max c (B + 1) - c).toNat)
    (fun i _ => by
      have := latticeL1Dist_eq_one_of_adj (hγa (c + i))
      rwa [show c + (i : ℤ) + 1 = c + ((i + 1 : ℕ) : ℤ) by push_cast; ring] at this)
    (by simpa using hc) hn1
  have ht1' : β t1 = γ (c + i1) := Subtype.ext ht1
  -- walk along the loop from `β t0` to its first vertex on `γ`
  have hex : ∃ s : ℕ, β (t0 + (s : Fin (n + 1))) ∈ Set.range γ :=
    ⟨(t1 - t0).val, by rw [Fin.cast_val_eq_self, show t0 + (t1 - t0) = t1 by abel]; exact ⟨_, ht1'.symm⟩⟩
  classical
  obtain ⟨s, ⟨k, hk⟩, hmin⟩ : ∃ s : ℕ, β (t0 + (s : Fin (n + 1))) ∈ Set.range γ ∧
      ∀ s' < s, β (t0 + (s' : Fin (n + 1))) ∉ Set.range γ :=
    ⟨Nat.find hex, Nat.find_spec hex, fun s' h => Nat.find_min hex h⟩
  refine ⟨k, s, fun i => β (t0 + ((s - i : ℕ) : Fin (n + 1))), fun i hi => ?_, ?_,
    fun i hi hle => hmin _ (by omega), fun i _ => hβm _, ?_⟩
  · show (componentGraph C).Adj (β (t0 + ((s - i : ℕ) : Fin (n + 1))))
      (β (t0 + ((s - (i + 1) : ℕ) : Fin (n + 1))))
    rw [show s - i = s - (i + 1) + 1 by omega, Nat.cast_succ, ← add_assoc]
    exact (hβa _).symm
  · show β (t0 + ((s - 0 : ℕ) : Fin (n + 1))) = γ k
    rw [Nat.sub_zero]
    exact hk.symm
  · show u (β (t0 + ((s - s : ℕ) : Fin (n + 1)))) ≠ 0
    rw [Nat.sub_self, Nat.cast_zero, add_zero, ht0']
    exact hπu _

/-- **Step `step:5.19-many-paths`** of Lemma 5.19: the loops of Lemma 5.14 at the scales
`S₀ 2^j` and the nonzero paths of Lemma 5.18 give, for every `N`, `N` disjoint paths outside
`Q_{R+1}` from vertices of `γ` on one tail to vertices where `u ≠ 0`, meeting `γ` only at their
initial points. -/
theorem manyPathsStep : ManyPathsStep := by
  intro ω C f u hL hN γ hγi hγa R hR0 hRf hc N
  obtain ⟨c, hc⟩ := hc
  obtain ⟨M, hM⟩ := hL
  -- the visits of `γ` to `Q_R` lie in a stretch `γ [a, b]`, inside a cube `Q_S`
  have hfin : {k : ℤ | (γ k).val ∈ cube R}.Finite :=
    (cube_finite R).preimage (Subtype.val_injective.comp hγi).injOn
  obtain ⟨b, hb⟩ := hfin.bddAbove
  obtain ⟨a, ha⟩ := hfin.bddBelow
  obtain ⟨S, -, hS⟩ := exists_subset_cube ((Set.finite_Icc a b).image fun k => (γ k).val)
  have hscale : ∀ j : ℕ, M + S + R + 1 ≤ (M + S + R + 1) * 2 ^ j := fun j =>
    Nat.le_mul_of_pos_right _ (by positivity)
  have scale : ∀ j : ℕ, ∃ (k : ℤ) (ℓ : ℕ) (ρ : ℕ → C),
      (∀ i < ℓ, (componentGraph C).Adj (ρ i) (ρ (i + 1))) ∧ ρ 0 = γ k ∧
      (∀ i, 0 < i → i ≤ ℓ → ρ i ∉ Set.range γ) ∧
      (∀ i ≤ ℓ, (ρ i).val ∈ cube (2 * ((M + S + R + 1) * 2 ^ j)) \
        cube ((M + S + R + 1) * 2 ^ j)) ∧ u (ρ ℓ) ≠ 0 := by
    intro j
    have hm := hscale j
    obtain ⟨n, β, hβa, hβm, hβw⟩ := hM ((M + S + R + 1) * 2 ^ j) (by omega)
    obtain ⟨n', π, hπa, hπ0, hπL, hπu⟩ :=
      hN R hR0 hRf (2 * ((M + S + R + 1) * 2 ^ j) + 1) (by omega)
    exact exists_arc_of_loop hβa hβm hβw hπa (cube_mono (by omega) hπ0)
      (fun h => hπL (cube_mono (by omega) h)) hπu hγi hγa (cube_mono (by omega) hc)
  choose k ℓ ρ hρa hρ0 hργ hρm hρu using scale
  -- each arc starts on one of the two tails of `γ`
  have hside : ∀ j, k j < a ∨ b < k j := by
    intro j
    by_contra h
    push Not at h
    have hmem : (γ (k j)).val ∈ cube S := hS ⟨k j, ⟨h.1, h.2⟩, rfl⟩
    have hout := (hρm j 0 (Nat.zero_le _)).2
    rw [hρ0 j] at hout
    exact hout (cube_mono (by have := hscale j; omega) hmem)
  obtain ⟨P, hP, hinf⟩ : ∃ P : ℤ → Prop, (∀ k₁ k₂ n, P k₁ → P k₂ → min k₁ k₂ ≤ n →
      n ≤ max k₁ k₂ → (γ n).val ∉ cube R) ∧ {j | P (k j)}.Infinite := by
    rcases Set.infinite_union.1 (show ({j | b < k j} ∪ {j | b < k j}ᶜ).Infinite by
      rw [Set.union_compl_self]; exact Set.infinite_univ) with h | h
    · exact ⟨(b < ·), fun k₁ k₂ n h1 h2 hn _ hmem => by have := hb hmem; omega, h⟩
    · exact ⟨(· < a), fun k₁ k₂ n h1 h2 _ hn hmem => by have := ha hmem; omega,
        h.mono fun j hj => (hside j).resolve_right hj⟩
  set e := hinf.natEmbedding
  have hJ : ∀ i₁ i₂ : Fin N, i₁ ≠ i₂ → (e i₁.val).val ≠ (e i₂.val).val := fun i₁ i₂ h h' =>
    h (Fin.ext (e.injective (Subtype.ext h')))
  refine ⟨fun i => k (e i.val).val, fun i => ℓ (e i.val).val, fun i => ρ (e i.val).val,
    fun i => hρa _, fun i => hρ0 _, fun i => hργ _, fun i j hj h => ?_, fun i => hρu _,
    fun i₁ i₂ h j₁ hj₁ j₂ hj₂ heq => ?_,
    fun i₁ i₂ n h1 h2 => hP _ _ n (e i₁.val).2 (e i₂.val).2 h1 h2⟩
  · exact (hρm _ j hj).2 (cube_mono (by have := hscale (e i.val).val; omega) h)
  · have hdisj : ∀ j₁ j₂ : ℕ, j₁ < j₂ → ∀ x y : C,
        x.val ∈ cube (2 * ((M + S + R + 1) * 2 ^ j₁)) →
        y.val ∉ cube ((M + S + R + 1) * 2 ^ j₂) → x ≠ y := by
      intro j₁ j₂ hj x y hx hy hxy
      have hle : 2 * ((M + S + R + 1) * 2 ^ j₁) ≤ (M + S + R + 1) * 2 ^ j₂ :=
        calc 2 * ((M + S + R + 1) * 2 ^ j₁) = (M + S + R + 1) * 2 ^ (j₁ + 1) := by ring
          _ ≤ (M + S + R + 1) * 2 ^ j₂ :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hj)
      exact hy (hxy ▸ cube_mono hle hx)
    rcases lt_or_gt_of_ne (hJ i₁ i₂ h) with hlt | hlt
    · exact hdisj _ _ hlt _ _ (hρm _ j₁ hj₁).1 (hρm _ j₂ hj₂).2 heq
    · exact hdisj _ _ hlt _ _ (hρm _ j₂ hj₂).1 (hρm _ j₁ hj₁).2 heq.symm

end Rigidity.Proofs.Section5
