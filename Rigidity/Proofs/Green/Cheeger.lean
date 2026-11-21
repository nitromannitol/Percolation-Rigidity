import Rigidity.Proofs.Green.LocalNash

/-!
# Faber-Krahn inequalities from isoperimetric inequalities for large sets

A vertex set `B` of a locally finite graph satisfies the isoperimetric inequality of dimension `D`
with constant `κ` above the size `s₀` (`IsoperimetricOn G B D κ s₀`) if every finite `U ⊆ B` with
at least `s₀` vertices has at least `κ |U|^{(D-1)/D}` boundary edges. Small sets are not
constrained; on an infinite connected graph every nonempty finite set has at least one boundary
edge, which is all that is used for them.

For `0 < κ ≤ 1` and `s₀ ≥ 1`, every nonempty `U` inside a finite `Ω ⊆ B` then has at least
`h |U|` boundary edges, `h = κ |Ω|^{-1/D} / s₀`, and the discrete co-area inequality
`∑_{y} ∑_{v ∼ y} (φ y - φ v)⁺ ≥ h ∑ φ` for nonnegative `φ` supported in `Ω`
(`coarea_le_sum_pos_sub`, proved by peeling off the lowest level of `φ`) applied to `φ = g²`,
together with Cauchy-Schwarz, gives the Faber-Krahn inequality with constant
`κ² / (4 Δ s₀²)` for degrees at most `Δ` (`faberKrahnOn_of_isoperimetricOn`). This is the
discrete Cheeger inequality for the first Dirichlet eigenvalue.
-/

open scoped Classical

namespace Rigidity.Green

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The number of edges from `U` to its complement. -/
noncomputable def edgeBoundaryCard (G : SimpleGraph V) [G.LocallyFinite] (U : Finset V) : ℕ :=
  ∑ y ∈ U, ((G.neighborFinset y).filter (fun v => v ∉ U)).card

/-- The isoperimetric inequality of dimension `D` with constant `κ` for the finite subsets of `B`
with at least `s₀` vertices. -/
def IsoperimetricOn (G : SimpleGraph V) [G.LocallyFinite] (B : Set V) (D κ s₀ : ℝ) : Prop :=
  ∀ U : Finset V, (↑U : Set V) ⊆ B → s₀ ≤ U.card →
    κ * (U.card : ℝ) ^ ((D - 1) / D) ≤ edgeBoundaryCard G U

/-- The isoperimetric inequality passes to subsets. -/
theorem IsoperimetricOn.mono {B B' : Set V} {D κ s₀ : ℝ} (h : IsoperimetricOn G B D κ s₀)
    (hB : B' ⊆ B) : IsoperimetricOn G B' D κ s₀ :=
  fun U hU hs => h U (hU.trans hB) hs

/-- A nonempty finite vertex set of an infinite connected graph has a boundary edge. -/
theorem one_le_edgeBoundaryCard [Infinite V] (hG : G.Connected) {U : Finset V}
    (hU : U.Nonempty) : 1 ≤ edgeBoundaryCard G U := by
  obtain ⟨u, hu⟩ := hU
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset U
  obtain ⟨p⟩ := hG.preconnected u z
  obtain ⟨dt, -, hd1, hd2⟩ := p.exists_boundary_dart (↑U) hu hz
  have hmem : dt.snd ∈ (G.neighborFinset dt.fst).filter (fun v => v ∉ U) :=
    Finset.mem_filter.2 ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 dt.adj, hd2⟩
  have hpos : 0 < ((G.neighborFinset dt.fst).filter (fun v => v ∉ U)).card :=
    Finset.card_pos.2 ⟨_, hmem⟩
  exact le_trans hpos (Finset.single_le_sum (f := fun y =>
    ((G.neighborFinset y).filter (fun v => v ∉ U)).card) (fun _ _ => Nat.zero_le _) hd1)

/-- The boundary count as a double sum of indicators. -/
theorem edgeBoundaryCard_eq_sum (U : Finset V) :
    (edgeBoundaryCard G U : ℝ) =
      ∑ y ∈ U, ∑ v ∈ G.neighborFinset y, if v ∈ U then (0 : ℝ) else 1 := by
  rw [edgeBoundaryCard, Nat.cast_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  split_ifs <;> simp_all

/-- **Discrete co-area inequality.** If every nonempty `U ⊆ Ω` has at least `h |U|` boundary
edges, then every nonnegative `φ` vanishing off `Ω` satisfies
`h ∑_S φ ≤ ∑_{y ∈ S} ∑_{v ∼ y} max (φ y - φ v) 0` over its support `S`. -/
theorem coarea_le_sum_pos_sub {Ω : Finset V} {h : ℝ}
    (hiso : ∀ U : Finset V, U ⊆ Ω → U.Nonempty → h * U.card ≤ edgeBoundaryCard G U) :
    ∀ (k : ℕ) (S : Finset V) (φ : V → ℝ), S.card = k → S ⊆ Ω → (∀ y ∈ S, 0 < φ y) →
      (∀ y, y ∉ S → φ y = 0) →
      h * ∑ y ∈ S, φ y ≤ ∑ y ∈ S, ∑ v ∈ G.neighborFinset y, max (φ y - φ v) 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro S φ hk hSΩ hpos hzero
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS]
  set m := (S.image φ).min' (hS.image φ) with hm
  have hmS : ∃ y₀ ∈ S, φ y₀ = m := by
    have := Finset.min'_mem (S.image φ) (hS.image φ)
    rw [← hm, Finset.mem_image] at this
    exact this
  have hmle : ∀ y ∈ S, m ≤ φ y := fun y hy =>
    Finset.min'_le _ _ (Finset.mem_image_of_mem φ hy)
  obtain ⟨y₀, hy₀S, hy₀m⟩ := hmS
  have hmpos : 0 < m := hy₀m ▸ hpos y₀ hy₀S
  set ψ : V → ℝ := fun y => if y ∈ S then φ y - m else 0 with hψ
  set S' := S.filter (fun y => m < φ y) with hS'
  have hS'S : S' ⊆ S := Finset.filter_subset _ _
  have hcard : S'.card < S.card := by
    refine Finset.card_lt_card ⟨hS'S, fun hsub => ?_⟩
    have := (Finset.mem_filter.1 (hsub hy₀S)).2
    linarith
  have hψpos : ∀ y ∈ S', 0 < ψ y := by
    intro y hy
    have hy' := Finset.mem_filter.1 hy
    simp only [hψ, if_pos hy'.1]
    linarith [hy'.2]
  have hψzero : ∀ y, y ∉ S' → ψ y = 0 := by
    intro y hy
    by_cases hyS : y ∈ S
    · have hle : φ y ≤ m := by
        by_contra hlt
        exact hy (Finset.mem_filter.2 ⟨hyS, lt_of_not_ge hlt⟩)
      simp only [hψ, if_pos hyS]
      linarith [hmle y hyS]
    · simp only [hψ, if_neg hyS]
  have hψnn : ∀ y, 0 ≤ ψ y := by
    intro y
    by_cases hyS : y ∈ S
    · simp only [hψ, if_pos hyS]; linarith [hmle y hyS]
    · simp only [hψ, if_neg hyS]; exact le_rfl
  have hIH := ih S'.card (hk ▸ hcard) S' ψ rfl (hS'S.trans hSΩ) hψpos hψzero
  have hsplit : ∀ y ∈ S, ∑ v ∈ G.neighborFinset y, max (φ y - φ v) 0 =
      ∑ v ∈ G.neighborFinset y, max (ψ y - ψ v) 0 +
        m * ∑ v ∈ G.neighborFinset y, if v ∈ S then (0 : ℝ) else 1 := by
    intro y hy
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : v ∈ S
    · simp only [hψ, if_pos hy, if_pos hv, mul_zero, add_zero]
      congr 1
      ring
    · simp only [hψ, if_pos hy, if_neg hv, hzero v hv, mul_one, sub_zero]
      rw [max_eq_left (hpos y hy).le, max_eq_left (by linarith [hmle y hy])]
      ring
  have hψS : ∑ y ∈ S, ∑ v ∈ G.neighborFinset y, max (ψ y - ψ v) 0 =
      ∑ y ∈ S', ∑ v ∈ G.neighborFinset y, max (ψ y - ψ v) 0 := by
    refine (Finset.sum_subset hS'S fun y _ hy => ?_).symm
    refine Finset.sum_eq_zero fun v _ => ?_
    rw [hψzero y hy, zero_sub]
    exact max_eq_right (by linarith [hψnn v])
  have hsumφ : ∑ y ∈ S, φ y = ∑ y ∈ S', ψ y + m * S.card := by
    have h1 : ∑ y ∈ S, φ y = ∑ y ∈ S, (ψ y + m) := by
      refine Finset.sum_congr rfl fun y hy => ?_
      simp only [hψ, if_pos hy]; ring
    have h2 : ∑ y ∈ S, ψ y = ∑ y ∈ S', ψ y :=
      (Finset.sum_subset hS'S fun y _ hy => hψzero y hy).symm
    rw [h1, Finset.sum_add_distrib, h2, Finset.sum_const, nsmul_eq_mul]
    ring
  have hbdry := hiso S hSΩ hS
  rw [edgeBoundaryCard_eq_sum] at hbdry
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hψS, ← Finset.mul_sum, hsumφ]
  have hmb : m * (h * S.card) ≤ m * ∑ y ∈ S, ∑ v ∈ G.neighborFinset y,
      (if v ∈ S then (0 : ℝ) else 1) := mul_le_mul_of_nonneg_left hbdry hmpos.le
  nlinarith [hIH, hmb]

/-- **Faber-Krahn from isoperimetry.** On an infinite connected graph with degrees at most `Δ`,
the isoperimetric inequality of dimension `D` with constant `0 < κ ≤ 1` above the size `s₀ ≥ 1`
on `B` gives the Faber-Krahn inequality on `B` with constant `κ² / (4 Δ s₀²)`. -/
theorem faberKrahnOn_of_isoperimetricOn [Infinite V] (hG : G.Connected) {Δ : ℕ}
    (hΔ : BoundedDegree G Δ) {B : Set V} {D κ s₀ : ℝ} (hD : 0 < D) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hs₀ : 1 ≤ s₀) (hiso : IsoperimetricOn G B D κ s₀) :
    FaberKrahnOn G B D (κ ^ 2 / (4 * Δ * s₀ ^ 2)) := by
  intro Ω T g hΩB hg hΩT hΩN
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => degree_pos hG v
  set X := ∑ y ∈ Ω, g y ^ 2 with hX
  set E := ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (g y - g v) ^ 2 with hE
  have hXnn : 0 ≤ X := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hEnn : 0 ≤ E := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  rcases Ω.eq_empty_or_nonempty with hΩ0 | hΩne
  · have hX0 : X = 0 := by rw [hX, hΩ0, Finset.sum_empty]
    rw [hX0, mul_zero]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hEnn
  have hΩcard : (1 : ℝ) ≤ Ω.card := by exact_mod_cast Finset.card_pos.2 hΩne
  have hΩpos : (0 : ℝ) < Ω.card := by linarith
  have hΔpos : (0 : ℝ) < Δ := by
    have := (hdeg (hΩne.choose)).trans_le (hΔ _)
    exact_mod_cast this
  set q := (Ω.card : ℝ) ^ (-1 / D) with hq
  have hqpos : 0 < q := Real.rpow_pos_of_pos hΩpos _
  have hq1 : q ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hΩcard
    (div_nonpos_of_nonpos_of_nonneg (by norm_num) hD.le)
  set h := κ * q / s₀ with hh
  have hhnn : 0 ≤ h := by positivity
  -- every nonempty subset of `Ω` has at least `h |U|` boundary edges
  have hiso' : ∀ U : Finset V, U ⊆ Ω → U.Nonempty → h * U.card ≤ edgeBoundaryCard G U := by
    intro U hUΩ hUne
    have hUcard : (1 : ℝ) ≤ U.card := by exact_mod_cast Finset.card_pos.2 hUne
    have hUpos : (0 : ℝ) < U.card := by linarith
    have hUΩc : (U.card : ℝ) ≤ Ω.card := by exact_mod_cast Finset.card_le_card hUΩ
    rcases le_or_gt s₀ U.card with hbig | hsmall
    · have hI := hiso U ((Finset.coe_subset.2 hUΩ).trans hΩB) hbig
      have hsplitU : (U.card : ℝ) ^ ((D - 1) / D) = U.card * (U.card : ℝ) ^ (-1 / D) := by
        rw [show (D - 1) / D = 1 + -1 / D by field_simp; ring, Real.rpow_add hUpos,
          Real.rpow_one]
      have hqU : q ≤ (U.card : ℝ) ^ (-1 / D) :=
        Real.rpow_le_rpow_of_nonpos hUpos hUΩc
          (div_nonpos_of_nonpos_of_nonneg (by norm_num) hD.le)
      have hh_le : h ≤ κ * q := by
        rw [hh]
        exact div_le_self (by positivity) hs₀
      calc h * U.card ≤ κ * q * U.card := mul_le_mul_of_nonneg_right hh_le hUpos.le
        _ ≤ κ * (U.card * (U.card : ℝ) ^ (-1 / D)) := by
            rw [show κ * q * U.card = κ * (U.card * q) by ring]
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hqU hUpos.le) hκ.le
        _ = κ * (U.card : ℝ) ^ ((D - 1) / D) := by rw [hsplitU]
        _ ≤ edgeBoundaryCard G U := hI
    · have h1 : (1 : ℝ) ≤ edgeBoundaryCard G U := by
        exact_mod_cast one_le_edgeBoundaryCard hG hUne
      have hκq : κ * q ≤ 1 := by nlinarith
      have hs₀pos : 0 < s₀ := by linarith
      calc h * U.card = κ * q * (U.card / s₀) := by rw [hh]; ring
        _ ≤ 1 * 1 := by
            refine mul_le_mul hκq ?_ (by positivity) (by norm_num)
            rw [div_le_one hs₀pos]
            exact hsmall.le
        _ ≤ edgeBoundaryCard G U := by linarith
  -- the co-area inequality for `g²` on its support
  set S := Ω.filter (fun y => g y ≠ 0) with hS
  have hco := coarea_le_sum_pos_sub hiso' S.card S (fun y => g y ^ 2) rfl
    (Finset.filter_subset _ _)
    (fun y hy => by
      have := (Finset.mem_filter.1 hy).2
      positivity)
    (fun y hy => by
      have : g y = 0 := by
        by_contra hne
        exact hy (Finset.mem_filter.2 ⟨hg y hne, hne⟩)
      simp [this])
  have hXS : ∑ y ∈ S, g y ^ 2 = X := by
    refine Finset.sum_subset (Finset.filter_subset _ _) fun y hyΩ hyS => ?_
    have : g y = 0 := by
      by_contra hne
      exact hyS (Finset.mem_filter.2 ⟨hyΩ, hne⟩)
    simp [this]
  rw [hXS] at hco
  have hST : S ⊆ T := (Finset.filter_subset _ _).trans hΩT
  have hTg : ∀ y, g y ≠ 0 → y ∈ T := fun y hy => hΩT (hg y hy)
  have hTNg : ∀ y v : V, g y ≠ 0 → G.Adj y v → v ∈ T := fun y v hy hadj => hΩN y (hg y hy) v hadj
  have habs : ∑ y ∈ S, ∑ v ∈ G.neighborFinset y, max (g y ^ 2 - g v ^ 2) 0 ≤
      ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, |g y ^ 2 - g v ^ 2| := by
    calc _ ≤ ∑ y ∈ S, ∑ v ∈ G.neighborFinset y, |g y ^ 2 - g v ^ 2| :=
          Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun v _ =>
            max_le (le_abs_self _) (abs_nonneg _)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hST
          (fun _ _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hcs := sum_abs_sub_sq_le (G := G) g T
  have hplus : ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (g y + g v) ^ 2 ≤ 4 * Δ * X := by
    rw [sum_sq_add_eq g T hTg hTNg]
    have hW : ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, g y * g v ≤
        ∑ y ∈ T, (G.degree y : ℝ) * g y ^ 2 := by
      have h1 := sum_sq_sub_eq (G := G) g T hTg hTNg
      have h2 : (0 : ℝ) ≤ ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (g y - g v) ^ 2 :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      linarith
    have hdegX : ∑ y ∈ T, (G.degree y : ℝ) * g y ^ 2 ≤ Δ * X := by
      have hsub : ∑ y ∈ T, (G.degree y : ℝ) * g y ^ 2 = ∑ y ∈ Ω, (G.degree y : ℝ) * g y ^ 2 := by
        refine (Finset.sum_subset hΩT fun y _ hy => ?_).symm
        have : g y = 0 := by
          by_contra hne
          exact hy (hg y hne)
        simp [this]
      rw [hsub, hX, Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      have : (G.degree y : ℝ) ≤ Δ := by exact_mod_cast hΔ y
      nlinarith [sq_nonneg (g y)]
    linarith
  have hkey : h * X ≤ Real.sqrt E * Real.sqrt (4 * Δ * X) :=
    hco.trans (habs.trans (hcs.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hplus)
      (Real.sqrt_nonneg _))))
  -- squaring
  have hsq : (h * X) ^ 2 ≤ E * (4 * Δ * X) := by
    have h0 : 0 ≤ h * X := mul_nonneg hhnn hXnn
    have := pow_le_pow_left₀ h0 hkey 2
    rw [mul_pow, mul_pow, Real.sq_sqrt hEnn, Real.sq_sqrt (by positivity)] at this
    nlinarith [this]
  have hqq : q ^ 2 * (Ω.card : ℝ) ^ (2 / D) = 1 := by
    rw [hq, ← Real.rpow_natCast, ← Real.rpow_mul hΩpos.le, ← Real.rpow_add hΩpos]
    rw [show -1 / D * ((2 : ℕ) : ℝ) + 2 / D = 0 by push_cast; ring, Real.rpow_zero]
  have hs₀pos : 0 < s₀ := by linarith
  rcases eq_or_lt_of_le hXnn with hX0 | hXpos
  · rw [← hX0, mul_zero]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) hEnn
  have hred : h ^ 2 * X ≤ 4 * Δ * E := by
    have : h ^ 2 * X * X ≤ 4 * Δ * E * X := by nlinarith [hsq]
    exact le_of_mul_le_mul_right this hXpos
  have hh2 : h ^ 2 = κ ^ 2 * q ^ 2 / s₀ ^ 2 := by rw [hh]; ring
  rw [hh2] at hred
  have hc : (Ω.card : ℝ) ^ (2 / D) * (κ ^ 2 * q ^ 2 / s₀ ^ 2 * X) = κ ^ 2 / s₀ ^ 2 * X := by
    rw [show (Ω.card : ℝ) ^ (2 / D) * (κ ^ 2 * q ^ 2 / s₀ ^ 2 * X) =
      κ ^ 2 / s₀ ^ 2 * X * (q ^ 2 * (Ω.card : ℝ) ^ (2 / D)) by ring, hqq, mul_one]
  have hfin : κ ^ 2 / s₀ ^ 2 * X ≤ (Ω.card : ℝ) ^ (2 / D) * (4 * Δ * E) := by
    rw [← hc]
    exact mul_le_mul_of_nonneg_left hred (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hfrac : κ ^ 2 / (4 * Δ * s₀ ^ 2) * X = (κ ^ 2 / s₀ ^ 2 * X) / (4 * Δ) := by
    field_simp
  rw [hfrac, div_le_iff₀ (by positivity)]
  linarith

end Rigidity.Green
