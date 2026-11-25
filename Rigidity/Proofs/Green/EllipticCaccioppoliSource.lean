import Rigidity.Proofs.Green.HarmonicReplacement

/-!
# The Caccioppoli inequality with a bounded source term

Let `G` be a locally finite graph with degrees at most `D`, `P` a set of vertices closed under
adjacency (an infinite cluster), `δ : V → ℝ` changing by at most `1` along edges (the distance to a
centre), and `B_ρ = {x : P x, δ x < ρ}` finite sets. For `r > 0`, a constant `c` and `u` with
`|Δu| ≤ F` on `B_{2r+1}`,

  `Σ_{x ∈ B_r} Σ_{y ∈ B_r, y ∼ x} (u(y) - u(x))² ≤ 2 r² F² |B_{2r+2}| + (4D + 2) r^{-2} Σ_{B_{2r+2}} (u - c)²`

(`pairEnergy_le_of_laplacian`), and the gradient energy `Σ_{x ∈ B_r} (Σ_{y ∈ B_r, y ∼ x} |u(y) - u(x)|)²`
is at most `D` times the left side (`gradEnergyOn_le`). Proof: test `-Δu` with `ζ²(u - c)`,
`ζ = 1` on `δ ≤ r + 1`, `ζ = 0` on `δ ≥ 2r + 1`, `|ζ(x) - ζ(y)| ≤ 1/r` along edges, and use, edge
by edge, `(ζ_y² b - ζ_x² a)(b - a) ≥ (ζ_x² + ζ_y²)(b - a)²/4 - (ζ_y - ζ_x)²(a + b)²/2`. This is the
energy estimate `‖∇v‖_{L̲²(B_r)} ≤ C (r^{-1} ‖v - c‖_{L̲²(B_{3r})} + r F)` of the proof of Theorem 3 of
Dario–Gu given here.
-/

open scoped Classical
open Finset

namespace Rigidity.Green

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {D : ℕ}

variable (G) in
/-- `Σ_{x ∈ S} Σ_{y ∈ S, y ∼ x} (u(y) - u(x))²`. -/
noncomputable def pairEnergy (S : Finset V) (u : V → ℝ) : ℝ :=
  ∑ x ∈ S, ∑ y ∈ S.filter (fun y => G.Adj x y), (u y - u x) ^ 2

variable (G) in
/-- `Σ_{x ∈ S} (Σ_{y ∈ S, y ∼ x} |u(y) - u(x)|)²`. -/
noncomputable def gradEnergyOn (S : Finset V) (u : V → ℝ) : ℝ :=
  ∑ x ∈ S, (∑ y ∈ S.filter (fun y => G.Adj x y), |u y - u x|) ^ 2

theorem gradEnergyOn_le (hdeg : ∀ x, G.degree x ≤ D) (S : Finset V) (u : V → ℝ) :
    gradEnergyOn G S u ≤ D * pairEnergy G S u := by
  unfold gradEnergyOn pairEnergy
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have h1 := sq_sum_le_card_mul_sum_sq (s := S.filter fun y => G.Adj x y)
    (f := fun y => |u y - u x|)
  simp only [sq_abs] at h1
  have h2 : ((S.filter fun y => G.Adj x y).card : ℝ) ≤ D := by
    have : (S.filter fun y => G.Adj x y).card ≤ G.degree x := by
      rw [← G.card_neighborFinset_eq_degree]
      exact Finset.card_le_card fun y hy => (G.mem_neighborFinset x y).2 (Finset.mem_filter.1 hy).2
    exact_mod_cast this.trans (hdeg x)
  have h3 : 0 ≤ ∑ y ∈ S.filter (fun y => G.Adj x y), (u y - u x) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith

/-- The cutoff `max 0 (min 1 ((2r + 1 - δ)/r))`. -/
noncomputable def ballCutoff (δ : V → ℝ) (r : ℝ) (x : V) : ℝ := max 0 (min 1 ((2 * r + 1 - δ x) / r))

theorem abs_max_zero_min_one_sub_le (a b : ℝ) :
    |max 0 (min 1 a) - max 0 (min 1 b)| ≤ |a - b| := by
  have h1 := neg_abs_le (a - b)
  have h2 := le_abs_self (a - b)
  rw [abs_le]
  simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

/-- The edge inequality of the Caccioppoli estimate. -/
theorem edge_caccioppoli (s t a b : ℝ) :
    1 / 4 * (s ^ 2 + t ^ 2) * (b - a) ^ 2 ≤
      (t ^ 2 * b - s ^ 2 * a) * (b - a) + 1 / 2 * ((t - s) ^ 2 * (a + b) ^ 2) := by
  nlinarith [sq_nonneg ((t + s) * (b - a) + 2 * ((t - s) * (a + b))),
    sq_nonneg ((t - s) * (b - a))]

/-- **The Caccioppoli inequality with a source.** -/
theorem pairEnergy_le_of_laplacian (hdeg : ∀ x, G.degree x ≤ D) {δ : V → ℝ}
    (hδ : ∀ x y, G.Adj x y → |δ x - δ y| ≤ 1) {P : V → Prop} (hP : ∀ x y, G.Adj x y → P x → P y)
    {B : ℝ → Finset V} (hB : ∀ ρ x, x ∈ B ρ ↔ P x ∧ δ x < ρ) {r : ℝ} (hr : 0 < r)
    (u : V → ℝ) (c : ℝ) {F : ℝ} (hF0 : 0 ≤ F)
    (hF : ∀ x ∈ B (2 * r + 1), |LatticeProb.Graph.laplacian G u x| ≤ F) :
    pairEnergy G (B r) u ≤ 2 * r ^ 2 * F ^ 2 * (B (2 * r + 2)).card +
      (4 * D + 2) / r ^ 2 * ∑ x ∈ B (2 * r + 2), (u x - c) ^ 2 := by
  set W := B (2 * r + 2) with hW
  set T := B (2 * r + 1) with hT
  set ζ := ballCutoff δ r with hζ
  have hζ0 : ∀ x, 0 ≤ ζ x := fun x => le_max_left _ _
  have hζ1 : ∀ x, ζ x ≤ 1 := fun x => max_le zero_le_one (min_le_left _ _)
  have hζeq1 : ∀ x, δ x ≤ r + 1 → ζ x = 1 := by
    intro x hx
    have : 1 ≤ (2 * r + 1 - δ x) / r := by rw [le_div_iff₀ hr]; linarith
    simp only [hζ, ballCutoff, min_eq_left this, max_eq_right zero_le_one]
  have hζeq0 : ∀ x, 2 * r + 1 ≤ δ x → ζ x = 0 := by
    intro x hx
    have : (2 * r + 1 - δ x) / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le
    simp only [hζ, ballCutoff]
    rw [min_eq_right (this.trans zero_le_one), max_eq_left this]
  have hζlip : ∀ x y, G.Adj x y → (ζ y - ζ x) ^ 2 ≤ 1 / r ^ 2 := by
    intro x y hxy
    have h1 := abs_max_zero_min_one_sub_le ((2 * r + 1 - δ y) / r) ((2 * r + 1 - δ x) / r)
    have h2 : |(2 * r + 1 - δ y) / r - (2 * r + 1 - δ x) / r| ≤ 1 / r := by
      rw [div_sub_div_same, abs_div, abs_of_pos hr]
      have e : 2 * r + 1 - δ y - (2 * r + 1 - δ x) = δ x - δ y := by ring
      rw [e]
      exact div_le_div_of_nonneg_right (hδ x y hxy) hr.le
    have h3 : |ζ y - ζ x| ≤ 1 / r := h1.trans h2
    rw [← sq_abs, show 1 / r ^ 2 = (1 / r) ^ 2 by ring]
    exact pow_le_pow_left₀ (abs_nonneg _) h3 2
  -- the test function
  set φ : V → ℝ := fun x => if x ∈ T then ζ x ^ 2 * (u x - c) else 0 with hφ
  have hTW : T ⊆ W := fun x hx => by
    rw [hT, hB] at hx; rw [hW, hB]; exact ⟨hx.1, by linarith [hx.2]⟩
  have hφT : ∀ x, x ∉ T → φ x = 0 := fun x hx => if_neg hx
  have hφeq : ∀ x, P x → φ x = ζ x ^ 2 * (u x - c) := by
    intro x hx
    by_cases hxT : x ∈ T
    · exact if_pos hxT
    · have : 2 * r + 1 ≤ δ x := by
        rw [hT, hB] at hxT; push Not at hxT; exact hxT hx
      rw [show φ x = 0 from if_neg hxT, hζeq0 x this]; ring
  have hNW : ∀ x ∈ T, ∀ y, G.Adj x y → y ∈ W := by
    intro x hx y hxy
    rw [hT, hB] at hx
    rw [hW, hB]
    refine ⟨hP x y hxy hx.1, ?_⟩
    obtain ⟨hl, hu⟩ := abs_le.1 (hδ x y hxy)
    linarith [hx.2]
  -- the identity `Σ_W Σ_{y ∼ x} (φ y - φ x)(u y - u x) = -2 Σ_T φ Δu`
  have hS1 : ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, φ x * (u y - u x) =
      ∑ x ∈ T, φ x * LatticeProb.Graph.laplacian G u x := by
    have e : ∀ x, ∑ y ∈ G.neighborFinset x, φ x * (u y - u x) =
        φ x * LatticeProb.Graph.laplacian G u x := fun x => by
      rw [LatticeProb.Graph.laplacian, Finset.mul_sum]
    simp_rw [e]
    exact (Finset.sum_subset hTW fun x _ hx => by rw [hφT x hx, zero_mul]).symm
  have hswap : ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, φ x * (u y - u x) =
      ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, φ y * (u x - u y) :=
    sum_sum_neighborFinset_comm W (fun x y => φ x * (u y - u x)) fun a b hab hne => by
      have ha : a ∈ T := by
        by_contra h
        exact hne (by rw [hφT a h, zero_mul])
      exact ⟨hTW ha, hNW a ha b hab⟩
  have hident : ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, (φ y - φ x) * (u y - u x) =
      -2 * ∑ x ∈ T, φ x * LatticeProb.Graph.laplacian G u x := by
    have e : ∀ x ∈ W, ∑ y ∈ G.neighborFinset x, (φ y - φ x) * (u y - u x) =
        -(∑ y ∈ G.neighborFinset x, φ x * (u y - u x)) -
          ∑ y ∈ G.neighborFinset x, φ y * (u x - u y) := by
      intro x _
      rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [Finset.sum_congr rfl e, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← hswap, hS1]
    ring
  -- the source term
  have hsrc : -2 * ∑ x ∈ T, φ x * LatticeProb.Graph.laplacian G u x ≤
      2 * F * ∑ x ∈ W, |u x - c| := by
    have h1 : ∀ x ∈ T, -(φ x * LatticeProb.Graph.laplacian G u x) ≤ F * |u x - c| := by
      intro x hx
      have hPx : P x := ((hB _ x).1 hx).1
      rw [hφeq x hPx]
      have hLx := hF x hx
      have hz := hζ0 x
      have hz1 := hζ1 x
      have hz2 : ζ x ^ 2 ≤ 1 := by nlinarith
      calc -(ζ x ^ 2 * (u x - c) * LatticeProb.Graph.laplacian G u x)
          ≤ |ζ x ^ 2 * (u x - c) * LatticeProb.Graph.laplacian G u x| := neg_le_abs _
        _ = ζ x ^ 2 * |u x - c| * |LatticeProb.Graph.laplacian G u x| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _)]
        _ ≤ 1 * |u x - c| * F := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hz2 (abs_nonneg _)) hLx (abs_nonneg _)
          positivity
        _ = F * |u x - c| := by ring
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at h2
    have h3 : ∑ x ∈ T, |u x - c| ≤ ∑ x ∈ W, |u x - c| :=
      Finset.sum_le_sum_of_subset_of_nonneg hTW fun _ _ _ => abs_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h3 hF0]
  -- the cutoff term
  have hcut : ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, (ζ y - ζ x) ^ 2 * ((u x - c) + (u y - c)) ^ 2 ≤
      4 * D / r ^ 2 * ∑ x ∈ W, (u x - c) ^ 2 := by
    have hpt : ∀ x ∈ W, ∀ y ∈ G.neighborFinset x,
        (ζ y - ζ x) ^ 2 * ((u x - c) + (u y - c)) ^ 2 ≤
          2 / r ^ 2 * ((u x - c) ^ 2 + if y ∈ W then (u y - c) ^ 2 else 0) := by
      intro x hx y hy
      have hxy : G.Adj x y := (G.mem_neighborFinset x y).1 hy
      by_cases hyW : y ∈ W
      · rw [if_pos hyW]
        have h1 := hζlip x y hxy
        have h2 : ((u x - c) + (u y - c)) ^ 2 ≤ 2 * ((u x - c) ^ 2 + (u y - c) ^ 2) := by
          nlinarith [sq_nonneg ((u x - c) - (u y - c))]
        calc (ζ y - ζ x) ^ 2 * ((u x - c) + (u y - c)) ^ 2
            ≤ 1 / r ^ 2 * (2 * ((u x - c) ^ 2 + (u y - c) ^ 2)) :=
              mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
          _ = 2 / r ^ 2 * ((u x - c) ^ 2 + (u y - c) ^ 2) := by ring
      · rw [if_neg hyW, add_zero]
        have hPy : P y := hP x y hxy ((hB _ x).1 hx).1
        have hδy : 2 * r + 2 ≤ δ y := by
          rw [hW, hB] at hyW; push Not at hyW; exact hyW hPy
        obtain ⟨hl, hu⟩ := abs_le.1 (hδ x y hxy)
        rw [hζeq0 y (by linarith), hζeq0 x (by linarith)]
        have : 0 ≤ 2 / r ^ 2 * (u x - c) ^ 2 := by positivity
        simpa using this
    have hsum1 := Finset.sum_le_sum fun x hx => Finset.sum_le_sum (hpt x hx)
    have hdeg' : ∀ x, ∑ y ∈ G.neighborFinset x, (u x - c) ^ 2 ≤ D * (u x - c) ^ 2 := by
      intro x
      rw [Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg x) (sq_nonneg _)
    have hswap2 : ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, (if y ∈ W then (u y - c) ^ 2 else 0) ≤
        D * ∑ x ∈ W, (u x - c) ^ 2 := by
      have hc := sum_sum_neighborFinset_comm (G := G) W
        (fun a b => if a ∈ W ∧ b ∈ W then (u b - c) ^ 2 else 0) fun a b _ hne => by
          by_contra h
          exact hne (if_neg h)
      have e1 : ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, (if y ∈ W then (u y - c) ^ 2 else 0) =
          ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, (if x ∈ W ∧ y ∈ W then (u y - c) ^ 2 else 0) :=
        Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y _ => by
          by_cases hy : y ∈ W
          · rw [if_pos hy, if_pos ⟨hx, hy⟩]
          · rw [if_neg hy, if_neg fun h => hy h.2]
      rw [e1, hc, Finset.mul_sum]
      refine Finset.sum_le_sum fun y hy => ?_
      calc ∑ x ∈ G.neighborFinset y, (if x ∈ W ∧ y ∈ W then (u y - c) ^ 2 else 0)
          ≤ ∑ x ∈ G.neighborFinset y, (u y - c) ^ 2 :=
            Finset.sum_le_sum fun x _ => by split_ifs <;> [exact le_rfl; exact sq_nonneg _]
        _ ≤ D * (u y - c) ^ 2 := by
            rw [Finset.sum_const, G.card_neighborFinset_eq_degree, nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdeg y) (sq_nonneg _)
    have hsplit : ∑ x ∈ W, ∑ y ∈ G.neighborFinset x,
        2 / r ^ 2 * ((u x - c) ^ 2 + if y ∈ W then (u y - c) ^ 2 else 0) =
        2 / r ^ 2 * (∑ x ∈ W, ∑ y ∈ G.neighborFinset x, (u x - c) ^ 2 +
          ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, (if y ∈ W then (u y - c) ^ 2 else 0)) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    have hA : ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, (u x - c) ^ 2 ≤ D * ∑ x ∈ W, (u x - c) ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum fun x _ => hdeg' x
    rw [hsplit] at hsum1
    have hr2 : 0 ≤ 2 / r ^ 2 := by positivity
    calc _ ≤ 2 / r ^ 2 * (∑ x ∈ W, ∑ y ∈ G.neighborFinset x, (u x - c) ^ 2 +
          ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, (if y ∈ W then (u y - c) ^ 2 else 0)) := hsum1
      _ ≤ 2 / r ^ 2 * (D * ∑ x ∈ W, (u x - c) ^ 2 + D * ∑ x ∈ W, (u x - c) ^ 2) :=
          mul_le_mul_of_nonneg_left (add_le_add hA hswap2) hr2
      _ = 4 * D / r ^ 2 * ∑ x ∈ W, (u x - c) ^ 2 := by ring
  -- the edge inequality, summed
  have hedge : ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, 1 / 4 * (ζ x ^ 2 + ζ y ^ 2) * (u y - u x) ^ 2 ≤
      ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, (φ y - φ x) * (u y - u x) +
        1 / 2 * ∑ x ∈ W, ∑ y ∈ G.neighborFinset x,
          (ζ y - ζ x) ^ 2 * ((u x - c) + (u y - c)) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x hx => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun y hy => ?_
    have hxy : G.Adj x y := (G.mem_neighborFinset x y).1 hy
    have hPx : P x := ((hB _ x).1 hx).1
    rw [hφeq x hPx, hφeq y (hP x y hxy hPx)]
    have := edge_caccioppoli (ζ x) (ζ y) (u x - c) (u y - c)
    have e : u y - c - (u x - c) = u y - u x := by ring
    rw [e] at this
    exact this
  -- the lower bound by the energy on `B_r`
  have hlow : 1 / 2 * pairEnergy G (B r) u ≤
      ∑ x ∈ W, ∑ y ∈ G.neighborFinset x, 1 / 4 * (ζ x ^ 2 + ζ y ^ 2) * (u y - u x) ^ 2 := by
    have hrW : B r ⊆ W := fun x hx => by
      rw [hB] at hx; rw [hW, hB]; exact ⟨hx.1, by linarith [hx.2]⟩
    unfold pairEnergy
    rw [Finset.mul_sum]
    refine (Finset.sum_le_sum fun x hx => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hrW fun x _ _ => Finset.sum_nonneg fun y _ =>
        by have := hζ0 x; have := hζ0 y; positivity)
    rw [Finset.mul_sum]
    have hsub : (B r).filter (fun y => G.Adj x y) ⊆ G.neighborFinset x := fun y hy =>
      (G.mem_neighborFinset x y).2 (Finset.mem_filter.1 hy).2
    refine (Finset.sum_le_sum fun y hy => ?_).trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun y _ _ =>
        by have := hζ0 x; have := hζ0 y; positivity)
    have hy' := (Finset.mem_filter.1 hy).1
    rw [hB] at hx hy'
    rw [hζeq1 x (by linarith [hx.2]), hζeq1 y (by linarith [hy'.2])]
    norm_num
  -- the source by Young's inequality
  have hyoung : 2 * F * ∑ x ∈ W, |u x - c| ≤
      r ^ 2 * F ^ 2 * W.card + 1 / r ^ 2 * ∑ x ∈ W, (u x - c) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum]
    have : ∀ x ∈ W, 2 * F * |u x - c| ≤ r ^ 2 * F ^ 2 + 1 / r ^ 2 * (u x - c) ^ 2 := by
      intro x _
      have hr2 : 0 < r ^ 2 := by positivity
      have key : 0 ≤ (r ^ 2 * F - |u x - c|) ^ 2 := sq_nonneg _
      have h1 : 2 * F * |u x - c| * r ^ 2 ≤ r ^ 2 * F ^ 2 * r ^ 2 + (u x - c) ^ 2 := by
        nlinarith [sq_abs (u x - c)]
      calc 2 * F * |u x - c| = 2 * F * |u x - c| * r ^ 2 / r ^ 2 :=
            (mul_div_cancel_right₀ _ (ne_of_gt hr2)).symm
        _ ≤ (r ^ 2 * F ^ 2 * r ^ 2 + (u x - c) ^ 2) / r ^ 2 :=
            div_le_div_of_nonneg_right h1 hr2.le
        _ = r ^ 2 * F ^ 2 + 1 / r ^ 2 * (u x - c) ^ 2 := by
            rw [add_div, mul_div_cancel_right₀ _ (ne_of_gt hr2)]; ring
    calc ∑ x ∈ W, 2 * F * |u x - c| ≤ ∑ x ∈ W, (r ^ 2 * F ^ 2 + 1 / r ^ 2 * (u x - c) ^ 2) :=
          Finset.sum_le_sum this
      _ = r ^ 2 * F ^ 2 * W.card + ∑ x ∈ W, 1 / r ^ 2 * (u x - c) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]; ring
  rw [hident] at hedge
  have hfin : 1 / 2 * pairEnergy G (B r) u ≤ r ^ 2 * F ^ 2 * W.card +
      1 / r ^ 2 * ∑ x ∈ W, (u x - c) ^ 2 +
        1 / 2 * (4 * D / r ^ 2 * ∑ x ∈ W, (u x - c) ^ 2) := by
    linarith [hlow, hedge, hsrc, hcut, hyoung]
  calc pairEnergy G (B r) u ≤ 2 * (r ^ 2 * F ^ 2 * W.card +
      1 / r ^ 2 * ∑ x ∈ W, (u x - c) ^ 2 +
        1 / 2 * (4 * D / r ^ 2 * ∑ x ∈ W, (u x - c) ^ 2)) := by linarith
    _ = 2 * r ^ 2 * F ^ 2 * W.card + (4 * D + 2) / r ^ 2 * ∑ x ∈ W, (u x - c) ^ 2 := by ring

end Rigidity.Green
