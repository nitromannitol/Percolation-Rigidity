import Rigidity.Percolation.Bootstrap.Composition

/-!
# Relays of seeds along face orthants

A *relay* moves the target of a connection estimate: if a seed path `γ` is joined inside a region
`W` to a target `T` at level `p₀`, and from every vertex `x` of `T` some face orthant of a cube
`x + Q_n` with `n ≥ n₁` lies in a new target `T'` while the cube lies in `W`, then `γ` is joined
inside `W` to `T'` at level `p₀ + δ`, losing a controlled amount of probability. The open cluster
of `γ`, which meets `T` at a vertex far from `γ`, is a seed there, so the seed-to-face-orthant
estimate applies; the composition lemma gives the bound.
-/

noncomputable section

namespace Rigidity.Percolation

open LatticeProb.Percolation MeasureTheory ProbabilityTheory Rigidity.External
open scoped unitInterval

variable {d : ℕ}

/-! ### Finite cubes -/

/-- The cube `c + Q_r` as a finite set. -/
def cubeFinset (c : Vertex d) (r : ℕ) : Finset (Vertex d) :=
  Fintype.piFinset fun i => Finset.Icc (c i - r) (c i + r)

/-- The finite cube is the cube. -/
theorem coe_cubeFinset (c : Vertex d) (r : ℕ) :
    ((cubeFinset c r : Finset (Vertex d)) : Set (Vertex d)) = cubeAt c r := by
  ext y
  simp only [cubeFinset, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_Icc, mem_cubeAt,
    abs_le]
  exact forall_congr' fun i => ⟨fun ⟨h1, h2⟩ => ⟨by omega, by omega⟩,
    fun ⟨h1, h2⟩ => ⟨by omega, by omega⟩⟩

/-- Membership in a finite cube. -/
theorem mem_cubeFinset {c y : Vertex d} {r : ℕ} : y ∈ cubeFinset c r ↔ y ∈ cubeAt c r := by
  rw [← Finset.mem_coe, coe_cubeFinset]

/-! ### Monotonicity in the level -/

/-- Connections between regions form an increasing event. -/
theorem isUpperSet_connectsRegions (B L R : Set (Vertex d)) :
    IsUpperSet {ω : Configuration d | ConnectsRegions ω B L R} := by
  rintro ω η hωη ⟨x, hxB, hxL, y, hyB, hyR, h⟩
  exact ⟨x, hxB, hxL, y, hyB, hyR, h.mono (openIn_mono_configuration hωη B)⟩

/-- Increasing events are more likely at higher levels. -/
theorem latticeBondLaw_real_mono_level {p q : unitInterval} (hpq : p ≤ q)
    {A : Set (Configuration d)} (hA : IsUpperSet A) (hAm : MeasurableSet A) :
    (latticeBondLaw d p).real A ≤ (latticeBondLaw d q).real A := by
  rw [← bondMarkLaw_real_preimage_threshold p hAm, ← bondMarkLaw_real_preimage_threshold q hAm]
  exact measureReal_mono fun ω hω => hA (thresholdBondMarks_mono hpq ω) hω

/-- Connections between regions are more likely at higher levels. -/
theorem connectsRegions_mono_level {p q : unitInterval} (hpq : p ≤ q) (B L R : Set (Vertex d)) :
    (latticeBondLaw d p).real {ω | ConnectsRegions ω B L R} ≤
      (latticeBondLaw d q).real {ω | ConnectsRegions ω B L R} :=
  latticeBondLaw_real_mono_level hpq (isUpperSet_connectsRegions B L R)
    (measurableSet_connectsRegions B L R)

/-- Connections persist in larger regions and to larger targets. -/
theorem connectsRegions_mono {ω : Configuration d} {B B' L L' R R' : Set (Vertex d)}
    (h : ConnectsRegions ω B L R) (hB : B ⊆ B') (hL : L ⊆ L') (hR : R ⊆ R') :
    ConnectsRegions ω B' L' R' := by
  obtain ⟨x, hxB, hxL, y, hyB, hyR, hxy⟩ := h
  exact ⟨x, hB hxB, hL hxL, y, hB hyB, hR hyR, reachable_openIn_mono hB hxy⟩

/-! ### Seeds from clusters -/

/-- An open walk inside `C` from a vertex of a cube to a vertex outside it reaches the shell of
the cube inside `C` and the cube. -/
theorem exists_cubeShell_of_walk_inter {ω : Configuration d} {C : Set (Vertex d)} {c : Vertex d}
    {N : ℕ} : ∀ {x y : Vertex d} (_w : (openIn ω C).Walk x y), x ∈ C → x ∈ cubeAt c N →
      y ∉ cubeAt c N →
      ∃ v ∈ cubeShell c N, (openIn ω (C ∩ cubeAt c N)).Reachable x v
  | _, _, .nil, _, hx, hy => absurd hx hy
  | x, _, .cons (v := z) h w, hxC, hx, hy => by
    by_cases hsh : ∃ i, |x i - c i| = N
    · exact ⟨x, ⟨hx, hsh⟩, SimpleGraph.Reachable.refl _⟩
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
      obtain ⟨v, hvs, hr⟩ := exists_cubeShell_of_walk_inter w h.2.2 hz hy
      exact ⟨v, hvs, (SimpleGraph.Adj.reachable
        (show (openIn ω (C ∩ cubeAt c N)).Adj x z from ⟨h.1, ⟨hxC, hx⟩, ⟨h.2.2, hz⟩⟩)).trans hr⟩

/-- A set lattice-connected inside itself to `γ` is a seed at each of its vertices whose cube of
radius `u` misses `γ`. -/
theorem hasSeedPath_of_connected {S' γ : Finset (Vertex d)} {x : Vertex d} {u : ℕ}
    (hconn : ∀ z ∈ S', ∃ g ∈ γ, (openIn (allOpen d) (S' : Set (Vertex d))).Reachable g z)
    (hx : x ∈ S') (hfar : ∀ g ∈ γ, g ∉ cubeAt x u) :
    HasSeedPath (S' : Set (Vertex d)) x u := by
  obtain ⟨g, hg, hgx⟩ := hconn x hx
  obtain ⟨w⟩ := hgx.symm
  obtain ⟨v, hv, hr⟩ := exists_cubeShell_of_walk_inter w (Finset.mem_coe.2 hx)
    (fun i => by simp) (hfar g hg)
  exact ⟨Finset.mem_coe.2 hx, v, hv, hr⟩

/-! ### The relay step -/

/-- **Relay step.** Let `u < n₁` be as in the seed-to-face-orthant estimate at level `p_s` with
failure `η`. Suppose `γ` is joined inside `W` to `T` at level `p₀ ≥ p_s` with probability at least
`1 - e`, that from every vertex `x ∈ T` the cube `x + Q_u` misses `γ`, and that some face orthant
of a cube `x + Q_n`, `n ≥ n₁`, lies in `T'` with the cube in `W`. Then `γ` is joined inside `W` to
`T'` at level `p₀ + δ` with probability at least `1 - e - η / (1 - p₀)^K - (1 - δ)^K`. -/
theorem relay_step [NeZero d] {p_s p₀ : unitInterval} (hps : p_s ≤ p₀) (hp₀ : (p₀ : ℝ) < 1)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : (p₀ : ℝ) + δ ≤ 1) {u n₁ : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (hseed : ∀ n, n₁ ≤ n → ∀ (c : Vertex d) (a : Fin d) (τ : Fin d → ℤˣ)
      (S : Set (Vertex d)), HasSeedPath S c u →
        1 - η < (latticeBondLaw d p_s).real
          {ω | ConnectsRegions ω (cubeAt c n) S (faceOrthant c a τ n)})
    (γ W T T' : Finset (Vertex d)) (hγW : γ ⊆ W)
    (hfar : ∀ x ∈ T, ∀ g ∈ γ, g ∉ cubeAt x u)
    (hmove : ∀ x ∈ T, ∃ (a : Fin d) (τ : Fin d → ℤˣ) (n : ℕ), n₁ ≤ n ∧
      faceOrthant x a τ n ⊆ (T' : Set (Vertex d)) ∧ cubeAt x n ⊆ (W : Set (Vertex d)))
    (e : ℝ) (K : ℕ)
    (h₁ : 1 - e ≤ (latticeBondLaw d p₀).real {ω | ConnectsRegions ω (W : Set (Vertex d)) γ T}) :
    1 - (e + (η / (1 - (p₀ : ℝ)) ^ K + (1 - δ) ^ K)) ≤
      (latticeBondLaw d (raisedLevel p₀ δ hδ.le hδ1)).real
        {ω | ConnectsRegions ω (W : Set (Vertex d)) γ T'} := by
  refine composition_prob p₀ hp₀ δ hδ hδ1 γ W T T' hγW e η hη K h₁ ?_
  intro S' _ hS'W hconn ⟨x, hxT, hxS'⟩ _
  obtain ⟨a, τ, n, hn, hface, hcube⟩ := hmove x hxT
  have hseedS : HasSeedPath (S' : Set (Vertex d)) x u :=
    hasSeedPath_of_connected hconn hxS' (hfar x hxT)
  have h := hseed n hn x a τ _ hseedS
  have hlev := connectsRegions_mono_level hps (cubeAt x n) (S' : Set (Vertex d))
    (faceOrthant x a τ n)
  refine le_trans (le_of_lt (h.trans_le hlev)) (measureReal_mono ?_)
  intro ω hω
  exact connectsRegions_mono hω hcube le_rfl hface

/-! ### Moving a cube -/

/-- The integer sign of a unit. -/
theorem units_coe_eq_one_or (u : ℤˣ) : (u : ℤ) = 1 ∨ (u : ℤ) = -1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

/-- The unit `1` or `-1` according to the sign of an integer. -/
def signUnit (z : ℤ) : ℤˣ := if 0 ≤ z then 1 else -1

/-- From every vertex of `c + Q_w`, a face orthant of the cube of radius `w` around the vertex
lies in the cube translated by `sg w` in direction `j`, and the cube of radius `w` around the
vertex lies in `c + Q_{2w}`. -/
theorem exists_faceOrthant_translate (c : Vertex d) (w : ℕ) (j : Fin d) (sg : ℤˣ) {x : Vertex d}
    (hx : x ∈ cubeAt c w) :
    ∃ τ : Fin d → ℤˣ, faceOrthant x j τ w ⊆ cubeAt (Function.update c j (c j + sg * w)) w ∧
      cubeAt x w ⊆ cubeAt c (2 * w) := by
  classical
  refine ⟨fun i => if i = j then sg else signUnit (c i - x i), ?_, ?_⟩
  · rintro y ⟨hy, hyj, hyi⟩ i
    simp only [↓reduceIte] at hyj
    by_cases hij : i = j
    · subst hij
      simp only [Function.update_self]
      have hxi := hx i
      rcases units_coe_eq_one_or sg with hsg | hsg <;> rw [hsg] at hyj ⊢ <;>
        rw [abs_le] at hxi ⊢ <;> constructor <;> linarith [hxi.1, hxi.2]
    · simp only [Function.update_of_ne hij]
      have h1 := hyi i hij
      simp only [hij, ↓reduceIte, signUnit] at h1
      have hxi := hx i
      have hyxi := hy i
      rw [abs_le] at hxi hyxi ⊢
      split_ifs at h1 with hs
      · simp only [Units.val_one, one_mul] at h1
        constructor <;> linarith [hxi.1, hxi.2, hyxi.1, hyxi.2]
      · simp only [Units.val_neg, Units.val_one, neg_mul, one_mul, neg_nonneg,
          sub_nonpos] at h1
        push Not at hs
        constructor <;> linarith [hxi.1, hxi.2, hyxi.1, hyxi.2]
  · intro y hy i
    have h1 := hy i
    have h2 := hx i
    have h3 : |y i - c i| ≤ |y i - x i| + |x i - c i| := by
      have := abs_sub_le (y i) (x i) (c i)
      linarith
    push_cast
    linarith

/-- The number of steps of length `w` separating `c` from `t`, coordinate by coordinate. -/
def stepPotential (t c : Vertex d) (w : ℕ) : ℕ := ∑ j, (t j - c j).natAbs / w

/-- A step of length `w ≤ |t_j - c_j|` towards `t` in direction `j`. -/
def stepToward (t c : Vertex d) (w : ℕ) (j : Fin d) : Vertex d :=
  Function.update c j (c j + (signUnit (t j - c j) : ℤ) * w)

/-- A step towards `t` lowers the potential by one. -/
theorem stepPotential_stepToward (t c : Vertex d) {w : ℕ} (hw : 0 < w) (j : Fin d)
    (hj : (w : ℤ) ≤ |t j - c j|) :
    stepPotential t (stepToward t c w j) w + 1 = stepPotential t c w := by
  classical
  have hcoord : (t j - stepToward t c w j j).natAbs / w + 1 = (t j - c j).natAbs / w := by
    have hnat : (t j - stepToward t c w j j).natAbs + w = (t j - c j).natAbs := by
      simp only [stepToward, Function.update_self, signUnit]
      split_ifs with hs
      · simp only [Units.val_one, one_mul]
        rw [abs_of_nonneg hs] at hj
        omega
      · simp only [Units.val_neg, Units.val_one, neg_mul, one_mul]
        push Not at hs
        rw [abs_of_neg hs] at hj
        omega
    rw [← hnat, Nat.add_div_right _ hw]
  unfold stepPotential
  rw [← Finset.sum_erase_add (s := Finset.univ)
      (f := fun i => (t i - stepToward t c w j i).natAbs / w) (Finset.mem_univ j),
    ← Finset.sum_erase_add (s := Finset.univ) (f := fun i => (t i - c i).natAbs / w)
      (Finset.mem_univ j)]
  have hrest : ∑ x ∈ Finset.univ.erase j, (t x - stepToward t c w j x).natAbs / w =
      ∑ x ∈ Finset.univ.erase j, (t x - c x).natAbs / w := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [stepToward, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [hrest, add_assoc, hcoord]

/-- If the potential is zero, every coordinate of `c` is within `w` of that of `t`. -/
theorem abs_sub_lt_of_stepPotential_eq_zero {t c : Vertex d} {w : ℕ} (hw : 0 < w)
    (h : stepPotential t c w = 0) (j : Fin d) : |t j - c j| < w := by
  have hj : (t j - c j).natAbs / w = 0 := by
    unfold stepPotential at h
    exact Nat.eq_zero_of_le_zero (h ▸ Finset.single_le_sum
      (f := fun i => (t i - c i).natAbs / w) (fun i _ => Nat.zero_le _) (Finset.mem_univ j))
  rw [Nat.div_eq_zero_iff] at hj
  rcases hj with hj | hj
  · omega
  · rw [← Int.natCast_natAbs]
    exact_mod_cast hj

/-- If the potential is positive, some coordinate of `c` is at least `w` away from that of
`t`. -/
theorem exists_le_abs_sub_of_stepPotential_pos {t c : Vertex d} {w : ℕ}
    (h : 0 < stepPotential t c w) : ∃ j, (w : ℤ) ≤ |t j - c j| := by
  by_contra hcon
  push Not at hcon
  apply Nat.lt_irrefl 0
  calc 0 < stepPotential t c w := h
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      rw [Nat.div_eq_zero_iff]
      right
      have := hcon j
      rw [← Int.natCast_natAbs] at this
      exact_mod_cast this

/-- A step towards `t` is the translation of the centre by `w` in direction `j`. -/
theorem stepToward_eq (t c : Vertex d) (w : ℕ) (j : Fin d) :
    stepToward t c w j = Function.update c j (c j + (signUnit (t j - c j) : ℤ) * w) := rfl

/-- **Navigation.** A cube of radius `w` moved by steps of length `w` towards `t`, through a
safe set of centres whose doubled cubes lie in `W` and are far from `γ`, carries a connection
estimate from its starting position to any target containing the cubes near `t`; each step
costs `η / (1 - p_max)^K + (1 - δ)^K` and raises the level by `δ`. -/
theorem navigate [NeZero d] {p_s : unitInterval} {u n₁ : ℕ} {η : ℝ} (hη : 0 ≤ η)
    (hseed : ∀ n, n₁ ≤ n → ∀ (c : Vertex d) (a : Fin d) (τ : Fin d → ℤˣ)
      (S : Set (Vertex d)), HasSeedPath S c u →
        1 - η < (latticeBondLaw d p_s).real
          {ω | ConnectsRegions ω (cubeAt c n) S (faceOrthant c a τ n)})
    (γ W B : Finset (Vertex d)) (hγW : γ ⊆ W) (t : Vertex d) {w : ℕ} (hw : n₁ ≤ w)
    (hw0 : 0 < w) (Safe : Set (Vertex d))
    (hcube : ∀ c ∈ Safe, cubeAt c (2 * w) ⊆ (W : Set (Vertex d)))
    (hfar : ∀ c ∈ Safe, ∀ x ∈ cubeAt c w, ∀ g ∈ γ, g ∉ cubeAt x u)
    (hstep : ∀ c ∈ Safe, ∀ j, (w : ℤ) ≤ |t j - c j| → stepToward t c w j ∈ Safe)
    (hfinal : ∀ c ∈ Safe, (∀ j, |t j - c j| < w) → cubeAt c w ⊆ (B : Set (Vertex d)))
    (δ : ℝ) (hδ : 0 < δ) (pmax : ℝ) (hpmax : pmax < 1) (K : ℕ) :
    ∀ N : ℕ, ∀ c ∈ Safe, stepPotential t c w = N → ∀ (p₀ q : unitInterval), p_s ≤ p₀ →
      (p₀ : ℝ) + N * δ ≤ q → (q : ℝ) ≤ pmax → ∀ e : ℝ,
      1 - e ≤ (latticeBondLaw d p₀).real
        {ω | ConnectsRegions ω (W : Set (Vertex d)) γ (cubeFinset c w)} →
      1 - (e + N * (η / (1 - pmax) ^ K + (1 - δ) ^ K)) ≤
        (latticeBondLaw d q).real {ω | ConnectsRegions ω (W : Set (Vertex d)) γ B} := by
  intro N
  induction N with
  | zero =>
    intro c hc hpot p₀ q hps hlvl hq e he
    have hsub : cubeAt c w ⊆ (B : Set (Vertex d)) :=
      hfinal c hc (abs_sub_lt_of_stepPotential_eq_zero hw0 hpot)
    have hpq : p₀ ≤ q := by
      change (p₀ : ℝ) ≤ q
      simpa using hlvl
    have hmono := connectsRegions_mono_level hpq (W : Set (Vertex d)) (γ : Set (Vertex d))
      (cubeFinset c w : Set (Vertex d))
    simp only [Nat.cast_zero, zero_mul, add_zero]
    refine he.trans (hmono.trans (measureReal_mono ?_))
    intro ω hω
    refine connectsRegions_mono hω le_rfl le_rfl ?_
    rw [coe_cubeFinset]
    exact hsub
  | succ N ih =>
    intro c hc hpot p₀ q hps hlvl hq e he
    obtain ⟨j, hj⟩ := exists_le_abs_sub_of_stepPotential_pos (t := t) (c := c) (w := w)
      (by omega)
    set c' := stepToward t c w j with hc'
    have hc'safe : c' ∈ Safe := hstep c hc j hj
    have hpot' : stepPotential t c' w = N := by
      have := stepPotential_stepToward t c hw0 j hj
      rw [← hc'] at this
      omega
    have hNδ : 0 ≤ (N : ℝ) * δ := by positivity
    have hp₀1 : (p₀ : ℝ) < 1 := by
      have : (p₀ : ℝ) ≤ q := by push_cast at hlvl; nlinarith
      linarith
    have hδ1 : (p₀ : ℝ) + δ ≤ 1 := by
      push_cast at hlvl
      have := q.property.2
      nlinarith
    have hrelay := relay_step (le_trans hps le_rfl) hp₀1 δ hδ hδ1 hη hseed γ W
      (cubeFinset c w) (cubeFinset c' w) hγW
      (fun x hx => hfar c hc x (mem_cubeFinset.1 hx))
      (fun x hx => by
        obtain ⟨τ, hface, hcub⟩ := exists_faceOrthant_translate c w j
          (signUnit (t j - c j)) (mem_cubeFinset.1 hx)
        refine ⟨j, τ, w, hw, ?_, hcub.trans (hcube c hc)⟩
        rw [coe_cubeFinset]
        exact hface)
      e K he
    have hstepcost : η / (1 - (p₀ : ℝ)) ^ K ≤ η / (1 - pmax) ^ K := by
      have hp₀max : (p₀ : ℝ) ≤ pmax := by push_cast at hlvl; nlinarith
      apply div_le_div_of_nonneg_left hη (pow_pos (by linarith) _)
      exact pow_le_pow_left₀ (by linarith) (by linarith) K
    have hps' : p_s ≤ raisedLevel p₀ δ hδ.le hδ1 := by
      change (p_s : ℝ) ≤ (p₀ : ℝ) + δ
      have : (p_s : ℝ) ≤ p₀ := hps
      linarith
    have hlvl' : ((raisedLevel p₀ δ hδ.le hδ1 : unitInterval) : ℝ) + N * δ ≤ q := by
      change (p₀ : ℝ) + δ + N * δ ≤ q
      push_cast at hlvl
      linarith
    have := ih c' hc'safe hpot' (raisedLevel p₀ δ hδ.le hδ1) q hps' hlvl' hq
      (e + (η / (1 - pmax) ^ K + (1 - δ) ^ K))
      (le_trans (by linarith) hrelay)
    push_cast
    linarith

end Rigidity.Percolation
