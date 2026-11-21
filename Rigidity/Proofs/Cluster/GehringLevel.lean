import Rigidity.Proofs.Cluster.GehringCubes
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The level-set estimate behind Gehring's lemma

Let `g ≥ 0` satisfy the reverse Hölder inequality
`avg_□ g ≤ A (avg_{enl □} g^θ)^{1/θ}` on every proper triadic subcube `□` of a triadic cube `P`,
`enl □` being the cube with the same center and side `3^j` times larger. If `avg_P g ≤ τ`, then

`∑_{x ∈ P, g x > τ} g x ≤ 2 · 9^d A^θ τ^{1-θ} ∑_{x ∈ enl P, g x > δτ} g(x)^θ`

whenever `2 (A δ)^θ ≤ 1` (`level_set_estimate`). This is the Calderón–Zygmund step of the proof of
Gehring's lemma (Giusti, *Direct methods in the calculus of variations*, Theorem 6.6), on triadic
cubes of `ℤ^d`: the maximal triadic subcubes of `P` on which the average of `g` exceeds `τ` cover
the points where `g > τ` (single points are cubes, so no differentiation theorem is needed), each has
average at most `3^d τ` since its parent does not exceed `τ`, and Vitali's selection
(`exists_vitali_subfamily`, by decreasing scale) extracts subcubes with disjoint enlargements whose
next enlargements cover them; the reverse Hölder inequality bounds the size of each selected
enlargement by the integral of `g^θ` over its points where `g > δτ` (`card_le_of_reverse_holder`).
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation
open scoped BigOperators Classical

variable {d : ℕ}

/-- The average of `F` over a finite set. -/
noncomputable def avg {V : Type*} (S : Finset V) (F : V → ℝ) : ℝ := (∑ x ∈ S, F x) / S.card

theorem idx_zero (x : Vertex d) : idx 0 x = x := by
  funext i
  simp [idx, halfSide]

theorem cube_zero (x : Vertex d) : cube 0 x = {x} := by
  ext y
  rw [mem_cube_iff, Finset.mem_singleton, idx_zero, idx_zero]

theorem avg_cube_zero (x : Vertex d) (F : Vertex d → ℝ) : avg (cube 0 x) F = F x := by
  rw [avg, cube_zero]
  simp

theorem card_enl_succ (j k : ℕ) (x : Vertex d) :
    ((enl (j + 1) k x).card : ℝ) = (3 : ℝ) ^ d * (enl j k x).card := by
  rw [card_enl, card_enl, ← add_assoc, pow_succ, mul_pow, mul_comm]

/-- **Vitali's selection.** In a finite family, if the enlargement `E a` meets `E b` and `a` has the
smaller scale, then `Q a ⊆ E' b`; then a subfamily with pairwise disjoint enlargements has the
property that every `Q a` lies in some `E' b` of it. -/
theorem exists_vitali_subfamily {α V : Type*} [DecidableEq α] [DecidableEq V] (sc : α → ℕ) (E Q E' : α → Finset V) :
    ∀ F : Finset α, (∀ a ∈ F, (E a).Nonempty) →
      (∀ a ∈ F, ∀ b ∈ F, sc a ≤ sc b → (E a ∩ E b).Nonempty → Q a ⊆ E' b) →
      ∃ S ⊆ F, (∀ a ∈ S, ∀ b ∈ S, a ≠ b → Disjoint (E a) (E b)) ∧
        ∀ a ∈ F, ∃ b ∈ S, Q a ⊆ E' b := by
  intro F
  induction F using Finset.strongInduction with
  | H F ih =>
    intro hE hgeom
    rcases F.eq_empty_or_nonempty with hF | hF
    · refine ⟨∅, Finset.empty_subset _, by simp, ?_⟩
      intro a ha
      rw [hF] at ha
      simp at ha
    · obtain ⟨b, hb, hmax⟩ := F.exists_max_image sc hF
      set F' := F.filter (fun a => Disjoint (E a) (E b)) with hF'
      have hbF' : b ∉ F' := by
        intro h
        rw [Finset.mem_filter] at h
        obtain ⟨y, hy⟩ := hE b hb
        exact Finset.disjoint_left.mp h.2 hy hy
      have hss : F' ⊂ F := by
        refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _, fun h => hbF' ?_⟩
        rw [h]
        exact hb
      obtain ⟨S', hS'F', hdisj, hcov⟩ := ih F' hss
        (fun a ha => hE a (Finset.filter_subset _ _ ha))
        (fun a ha c hc => hgeom a (Finset.filter_subset _ _ ha) c (Finset.filter_subset _ _ hc))
      refine ⟨insert b S', ?_, ?_, ?_⟩
      · exact Finset.insert_subset hb (hS'F'.trans (Finset.filter_subset _ _))
      · intro a ha c hc hac
        rw [Finset.mem_insert] at ha hc
        rcases ha with rfl | ha <;> rcases hc with rfl | hc
        · exact absurd rfl hac
        · exact (Finset.mem_filter.mp (hS'F' hc)).2.symm
        · exact (Finset.mem_filter.mp (hS'F' ha)).2
        · exact hdisj a ha c hc hac
      · intro a ha
        by_cases hdis : Disjoint (E a) (E b)
        · obtain ⟨c, hc, hsub⟩ := hcov a (Finset.mem_filter.mpr ⟨ha, hdis⟩)
          exact ⟨c, Finset.mem_insert_of_mem hc, hsub⟩
        · refine ⟨b, Finset.mem_insert_self _ _, hgeom a ha b hb (hmax a ha) ?_⟩
          rwa [Finset.not_disjoint_iff_nonempty_inter] at hdis

/-- **The size of a set on which a reverse Hölder inequality holds above a level.** If
`τ < A (avg_E g^θ)^{1/θ}` and `2 (A δ)^θ ≤ 1`, then `|E| ≤ 2 A^θ τ^{-θ} ∑_{x ∈ E, g x > δτ} g(x)^θ`. -/
theorem card_le_of_reverse_holder {V : Type*} {E : Finset V} (hE : E.Nonempty) {g : V → ℝ}
    (hg : ∀ x, 0 ≤ g x) {θ A δ τ : ℝ} (hθ : 0 < θ) (hA : 0 < A) (hδ : 0 < δ)
    (hAδ : 2 * (A * δ) ^ θ ≤ 1) (hτ : 0 < τ)
    (hRH : τ < A * avg E (fun x => g x ^ θ) ^ (1 / θ)) :
    (E.card : ℝ) ≤ 2 * A ^ θ / τ ^ θ * ∑ x ∈ E, if δ * τ < g x then g x ^ θ else 0 := by
  have hcard : (0 : ℝ) < E.card := by exact_mod_cast hE.card_pos
  have hcard' : (E.card : ℝ) ≠ 0 := hcard.ne'
  set m := avg E (fun x => g x ^ θ) with hm
  have hm0 : 0 ≤ m := div_nonneg (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (hg x) _)
    hcard.le
  have hAθ : 0 < A ^ θ := Real.rpow_pos_of_pos hA θ
  have hτθ : 0 < τ ^ θ := Real.rpow_pos_of_pos hτ θ
  have hτθ' : τ ^ θ ≠ 0 := hτθ.ne'
  have hAθ' : A ^ θ ≠ 0 := hAθ.ne'
  -- `τ^θ / A^θ < m`
  have h1 : τ ^ θ / A ^ θ < m := by
    have h2 : τ / A < m ^ (1 / θ) := by
      rw [div_lt_iff₀ hA]
      linarith
    have h3 := Real.rpow_lt_rpow (div_pos hτ hA).le h2 hθ
    rwa [Real.div_rpow hτ.le hA.le, ← Real.rpow_mul hm0, one_div_mul_cancel hθ.ne',
      Real.rpow_one] at h3
  -- splitting the sum of `g^θ`
  have hsplit : ∑ x ∈ E, g x ^ θ ≤
      (∑ x ∈ E, if δ * τ < g x then g x ^ θ else 0) + E.card * (δ ^ θ * τ ^ θ) := by
    have h4 : ∀ x ∈ E, g x ^ θ ≤
        (if δ * τ < g x then g x ^ θ else 0) + δ ^ θ * τ ^ θ := by
      intro x _
      split_ifs with h
      · have : 0 ≤ δ ^ θ * τ ^ θ := by positivity
        linarith
      · rw [zero_add, ← Real.mul_rpow hδ.le hτ.le]
        exact Real.rpow_le_rpow (hg x) (not_lt.mp h) hθ.le
    calc ∑ x ∈ E, g x ^ θ ≤ ∑ x ∈ E, ((if δ * τ < g x then g x ^ θ else 0) + δ ^ θ * τ ^ θ) :=
          Finset.sum_le_sum h4
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hδθ : δ ^ θ ≤ 1 / (2 * A ^ θ) := by
    rw [Real.mul_rpow hA.le hδ.le] at hAδ
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hmdef : m * E.card = ∑ x ∈ E, g x ^ θ := by
    rw [hm, avg]
    field_simp
  set T := ∑ x ∈ E, if δ * τ < g x then g x ^ θ else 0 with hT
  -- `|E| τ^θ / A^θ < T + |E| τ^θ / (2 A^θ)`
  have h5 : E.card * (τ ^ θ / A ^ θ) < T + E.card * (τ ^ θ / (2 * A ^ θ)) := by
    have h6 : E.card * (τ ^ θ / A ^ θ) < m * E.card := by
      rw [mul_comm m]
      exact mul_lt_mul_of_pos_left h1 hcard
    have h7 : E.card * (δ ^ θ * τ ^ θ) ≤ E.card * (τ ^ θ / (2 * A ^ θ)) := by
      refine mul_le_mul_of_nonneg_left ?_ hcard.le
      calc δ ^ θ * τ ^ θ ≤ 1 / (2 * A ^ θ) * τ ^ θ := mul_le_mul_of_nonneg_right hδθ hτθ.le
        _ = τ ^ θ / (2 * A ^ θ) := by ring
    linarith
  have h8 : E.card * (τ ^ θ / (2 * A ^ θ)) ≤ T := by
    have : E.card * (τ ^ θ / A ^ θ) = 2 * (E.card * (τ ^ θ / (2 * A ^ θ))) := by
      ring
    linarith
  calc (E.card : ℝ) = 2 * A ^ θ / τ ^ θ * (E.card * (τ ^ θ / (2 * A ^ θ))) := by
        field_simp
    _ ≤ 2 * A ^ θ / τ ^ θ * T := mul_le_mul_of_nonneg_left h8 (by positivity)

/-- **The level-set estimate.** If `g ≥ 0` satisfies the reverse Hölder inequality on the proper
triadic subcubes of the cube `P = cube n x₀` with enlargement `enl j`, `avg_P g ≤ τ` and
`2 (A δ)^θ ≤ 1`, then
`∑_{x ∈ P, g x > τ} g x ≤ 2 · 9^d A^θ τ^{1-θ} ∑_{x ∈ enl j n x₀, g x > δτ} g(x)^θ`. -/
theorem level_set_estimate {θ A δ τ : ℝ} (hθ : 0 < θ) (hA : 0 < A) (hδ : 0 < δ)
    (hAδ : 2 * (A * δ) ^ θ ≤ 1) (hτ : 0 < τ) (j n : ℕ) (x₀ : Vertex d) {g : Vertex d → ℝ}
    (hg : ∀ x, 0 ≤ g x)
    (hRH : ∀ k < n, ∀ y ∈ cube n x₀,
      avg (cube k y) g ≤ A * avg (enl j k y) (fun x => g x ^ θ) ^ (1 / θ))
    (hP : avg (cube n x₀) g ≤ τ) :
    ∑ x ∈ (cube n x₀).filter (fun x => τ < g x), g x ≤
      2 * 9 ^ d * A ^ θ * τ ^ (1 - θ) *
        ∑ x ∈ (enl j n x₀).filter (fun x => δ * τ < g x), g x ^ θ := by
  set P := cube n x₀ with hPdef
  set good : ℕ → Vertex d → Prop := fun k y => τ < avg (cube k y) g with hgood
  set Y := P.filter (fun y => ∃ k < n, good k y) with hY
  set s : Vertex d → ℕ := fun y => Nat.findGreatest (fun k => good k y) (n - 1) with hs
  have hPy : ∀ y ∈ P, cube n y = P := fun y hy => cube_eq_of_mem hy
  have hs_spec : ∀ y ∈ Y, good (s y) y ∧ s y < n := by
    intro y hy
    obtain ⟨k, hk, hgk⟩ := (Finset.mem_filter.mp hy).2
    refine ⟨Nat.findGreatest_spec (P := fun k => good k y) (by omega) hgk, ?_⟩
    have := Nat.findGreatest_le (P := fun k => good k y) (n - 1)
    show Nat.findGreatest (fun k => good k y) (n - 1) < n
    omega
  have hs_max : ∀ y ∈ Y, ∀ k, s y < k → k ≤ n - 1 → ¬ good k y := fun y _ k hk hkn =>
    Nat.findGreatest_is_greatest (P := fun k => good k y) hk hkn
  have hs_ge : ∀ y, ∀ k, k ≤ n - 1 → good k y → k ≤ s y := fun y k hk hgk =>
    Nat.le_findGreatest (P := fun k => good k y) hk hgk
  -- the maximal cubes
  have hQY : ∀ y ∈ Y, ∀ z ∈ cube (s y) y, z ∈ Y ∧ s z = s y := by
    intro y hy z hz
    obtain ⟨hgy, hsy⟩ := hs_spec y hy
    have hyP : y ∈ P := (Finset.mem_filter.mp hy).1
    have hzP : z ∈ P := by
      rw [← hPy y hyP]
      exact cube_mono hsy.le y hz
    have hcz : cube (s y) z = cube (s y) y := cube_eq_of_mem hz
    have hgz : good (s y) z := by
      simp only [hgood] at hgy ⊢
      rw [hcz]
      exact hgy
    have hzY : z ∈ Y := Finset.mem_filter.mpr ⟨hzP, s y, hsy, hgz⟩
    refine ⟨hzY, le_antisymm ?_ (hs_ge z (s y) (by omega) hgz)⟩
    by_contra hlt'
    have hlt : s y < s z := not_le.mp hlt'
    obtain ⟨hgz', hsz⟩ := hs_spec z hzY
    have hyz : y ∈ cube (s y) z := mem_cube_comm.mp hz
    have hcy : cube (s z) y = cube (s z) z := cube_eq_of_mem (cube_mono hlt.le z hyz)
    refine hs_max y hy (s z) hlt (by omega) ?_
    simp only [hgood] at hgz' ⊢
    rw [hcy]
    exact hgz'
  have hQmem : ∀ y ∈ Y, y ∈ cube (s y) y := fun y _ => mem_cube_self _ y
  have hQsub : ∀ y ∈ Y, cube (s y) y ⊆ Y := fun y hy z hz => (hQY y hy z hz).1
  have hQeq : ∀ y ∈ Y, ∀ z ∈ cube (s y) y, cube (s z) z = cube (s y) y := by
    intro y hy z hz
    rw [(hQY y hy z hz).2]
    exact cube_eq_of_mem hz
  -- each maximal cube has average at most `3^d τ`
  have hQavg : ∀ y ∈ Y, (∑ z ∈ cube (s y) y, g z) / (cube (s y) y).card ≤ 3 ^ d * τ := by
    intro y hy
    obtain ⟨_, hsy⟩ := hs_spec y hy
    have hyP : y ∈ P := (Finset.mem_filter.mp hy).1
    have hpar : avg (cube (s y + 1) y) g ≤ τ := by
      by_cases hlast : s y + 1 ≤ n - 1
      · have := hs_max y hy (s y + 1) (Nat.lt_succ_self _) hlast
        simp only [hgood, not_lt] at this
        exact this
      · have hn : s y + 1 = n := by omega
        rw [hn, hPy y hyP]
        exact hP
    have hcpos := card_cube_pos (s y) y
    have h1 : ∑ z ∈ cube (s y) y, g z ≤ ∑ z ∈ cube (s y + 1) y, g z :=
      Finset.sum_le_sum_of_subset_of_nonneg (cube_subset_succ _ y) fun z _ _ => hg z
    have h2 : ∑ z ∈ cube (s y + 1) y, g z ≤ τ * (cube (s y + 1) y).card := by
      rw [avg, div_le_iff₀ (card_cube_pos _ y)] at hpar
      exact hpar
    rw [card_cube_succ] at h2
    rw [div_le_iff₀ hcpos]
    calc ∑ z ∈ cube (s y) y, g z ≤ τ * ((3 : ℝ) ^ d * (cube (s y) y).card) := h1.trans h2
      _ = 3 ^ d * τ * (cube (s y) y).card := by ring
  have hsumY : ∑ y ∈ Y, g y ≤ Y.card * (3 ^ d * τ) := by
    rw [sum_eq_sum_avg (fun y => cube (s y) y) hQmem hQsub hQeq g]
    calc ∑ y ∈ Y, (∑ z ∈ cube (s y) y, g z) / (cube (s y) y).card ≤ ∑ y ∈ Y, 3 ^ d * τ :=
          Finset.sum_le_sum hQavg
      _ = Y.card * (3 ^ d * τ) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- the points where `g > τ` lie in the maximal cubes
  have hXY : P.filter (fun x => τ < g x) ⊆ Y := by
    intro x hx
    rw [Finset.mem_filter] at hx
    have hgx : good 0 x := by
      simp only [hgood]
      rw [avg_cube_zero]
      exact hx.2
    have hn : 0 < n := by
      by_contra h0
      have h0' : n = 0 := by omega
      have h1 : cube 0 x = P := by
        rw [← h0']
        exact hPy x hx.1
      simp only [hgood] at hgx
      rw [h1] at hgx
      linarith
    exact Finset.mem_filter.mpr ⟨hx.1, 0, hn, hgx⟩
  have hsumX : ∑ x ∈ P.filter (fun x => τ < g x), g x ≤ ∑ y ∈ Y, g y :=
    Finset.sum_le_sum_of_subset_of_nonneg hXY fun x _ _ => hg x
  -- Vitali's selection among the maximal cubes
  obtain ⟨S, hSY, hdisj, hcov⟩ := exists_vitali_subfamily s (fun y => enl j (s y) y)
    (fun y => cube (s y) y)
    (fun y => enl (j + 1) (s y) y) Y
    (fun y _ => ⟨y, cube_subset_enl j _ y (mem_cube_self _ y)⟩)
    (fun a _ b _ hab hne => cube_subset_enl_succ_of_inter hab hne)
  have hYcard : (Y.card : ℝ) ≤ ∑ b ∈ S, ((enl (j + 1) (s b) b).card : ℝ) := by
    have h1 : Y ⊆ S.biUnion fun b => enl (j + 1) (s b) b := by
      intro y hy
      obtain ⟨b, hb, hsub⟩ := hcov y hy
      exact Finset.mem_biUnion.mpr ⟨b, hb, hsub (hQmem y hy)⟩
    have h2 := (Finset.card_le_card h1).trans Finset.card_biUnion_le
    exact_mod_cast h2
  set I : Vertex d → ℝ := fun x => if δ * τ < g x then g x ^ θ else 0 with hI
  have hI0 : ∀ x, 0 ≤ I x := fun x => by
    simp only [hI]
    split_ifs
    · exact Real.rpow_nonneg (hg x) _
    · exact le_rfl
  have hsel : ∀ b ∈ S, ((enl j (s b) b).card : ℝ) ≤
      2 * A ^ θ / τ ^ θ * ∑ x ∈ enl j (s b) b, I x := by
    intro b hb
    have hbY := hSY hb
    obtain ⟨hgb, hsb⟩ := hs_spec b hbY
    have hbP : b ∈ P := (Finset.mem_filter.mp hbY).1
    refine card_le_of_reverse_holder ⟨b, cube_subset_enl j _ b (mem_cube_self _ b)⟩ hg hθ hA hδ
      hAδ hτ ?_
    exact lt_of_lt_of_le hgb (hRH (s b) hsb b hbP)
  have hunion : ∑ b ∈ S, ∑ x ∈ enl j (s b) b, I x ≤ ∑ x ∈ enl j n x₀, I x := by
    have hpd : (S : Set (Vertex d)).PairwiseDisjoint (fun b => enl j (s b) b) :=
      fun a ha b hb hab => hdisj a ha b hb hab
    refine ((Finset.sum_biUnion hpd).symm.le).trans
      (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun x _ _ => hI0 x)
    intro x hx
    obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx
    have hbP : b ∈ P := (Finset.mem_filter.mp (hSY hb)).1
    rw [← enl_eq_of_mem (j := j) hbP]
    exact enl_subset_enl (hs_spec b (hSY hb)).2.le j b hxb
  have hfilter : ∑ x ∈ (enl j n x₀).filter (fun x => δ * τ < g x), g x ^ θ =
      ∑ x ∈ enl j n x₀, I x :=
    Finset.sum_filter _ _
  rw [hfilter]
  have hτθ : 0 < τ ^ θ := Real.rpow_pos_of_pos hτ θ
  have hpow : τ ^ (1 - θ) = τ / τ ^ θ := by
    rw [Real.rpow_sub hτ, Real.rpow_one]
  rw [hpow]
  have hS : ∑ b ∈ S, ((enl (j + 1) (s b) b).card : ℝ) ≤
      3 ^ d * (2 * A ^ θ / τ ^ θ * ∑ x ∈ enl j n x₀, I x) := by
    calc ∑ b ∈ S, ((enl (j + 1) (s b) b).card : ℝ)
        = 3 ^ d * ∑ b ∈ S, ((enl j (s b) b).card : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun b _ => card_enl_succ j (s b) b
      _ ≤ 3 ^ d * ∑ b ∈ S, 2 * A ^ θ / τ ^ θ * ∑ x ∈ enl j (s b) b, I x :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hsel) (by positivity)
      _ = 3 ^ d * (2 * A ^ θ / τ ^ θ * ∑ b ∈ S, ∑ x ∈ enl j (s b) b, I x) := by
          congr 1
          rw [Finset.mul_sum]
      _ ≤ 3 ^ d * (2 * A ^ θ / τ ^ θ * ∑ x ∈ enl j n x₀, I x) := by
          gcongr
  calc ∑ x ∈ P.filter (fun x => τ < g x), g x ≤ Y.card * (3 ^ d * τ) := hsumX.trans hsumY
    _ ≤ (3 ^ d * (2 * A ^ θ / τ ^ θ * ∑ x ∈ enl j n x₀, I x)) * (3 ^ d * τ) :=
        mul_le_mul_of_nonneg_right (hYcard.trans hS) (by positivity)
    _ = 2 * 9 ^ d * A ^ θ * (τ / τ ^ θ) * ∑ x ∈ enl j n x₀, I x := by
        rw [show (9 : ℝ) ^ d = 3 ^ d * 3 ^ d by rw [← mul_pow]; norm_num]
        ring

end Rigidity.Proofs.Cluster
