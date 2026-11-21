import Rigidity.Proofs.Cluster.GehringLevel

/-!
# Higher integrability on one triadic cube

From the level-set estimate we integrate over the levels `τ_k = τ₀ 2^k`, `τ₀ = avg_P g`, by a
discrete layer-cake formula: for `0 ≤ G ≤ τ_K`,
`G^ε ≤ τ₀^ε + ∑_{k < K, τ_k < G} (τ_{k+1}^ε - τ_k^ε)` (`rpow_le_layer_sum`), and
`∑_{k < K, τ_k < G} τ_k^a ≤ 2^a/(2^a - 1) G^a` (`sum_geometric_levels_le`). The result is the
estimate on a single triadic cube `P`

`∑_P g^{1+ε} ≤ (avg_P g)^ε ∑_P g + η ∑_{enl P} g^{1+ε}`,
`η = (2^ε - 1) · 2 · 9^d A^θ · 2^a/(2^a - 1) · δ^{-a}`, `a = 1 + ε - θ`

(`sum_rpow_le_of_reverse_holder`), in which `η → 0` as `ε → 0`; this is the form in which Gehring's
lemma is proved in Giusti, *Direct methods in the calculus of variations*, Theorem 6.6.
-/

namespace Rigidity.Proofs.Cluster

open LatticeProb.Percolation
open scoped BigOperators Classical

variable {d : ℕ}

/-- **The discrete layer-cake bound.** For `t₀ > 0`, `ε > 0` and `0 ≤ G ≤ t₀ 2^K`,
`G^ε ≤ t₀^ε + ∑_{k < K, t₀ 2^k < G} ((t₀ 2^{k+1})^ε - (t₀ 2^k)^ε)`. -/
theorem rpow_le_layer_sum {t₀ ε : ℝ} (ht₀ : 0 < t₀) (hε : 0 < ε) (K : ℕ) {G : ℝ} (hG : 0 ≤ G)
    (hGK : G ≤ t₀ * 2 ^ K) :
    G ^ ε ≤ t₀ ^ ε + ∑ k ∈ Finset.range K,
      (if t₀ * 2 ^ k < G then (t₀ * 2 ^ (k + 1)) ^ ε - (t₀ * 2 ^ k) ^ ε else 0) := by
  have hmono : ∀ k : ℕ, (t₀ * 2 ^ k) ^ ε ≤ (t₀ * 2 ^ (k + 1)) ^ ε := fun k =>
    Real.rpow_le_rpow (mul_pos ht₀ (pow_pos (two_pos : (0 : ℝ) < 2) k)).le
      (by rw [pow_succ]; nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) k]) hε.le
  have key : ∀ K : ℕ,
      (G ≤ t₀ * 2 ^ K → G ^ ε ≤ t₀ ^ ε + ∑ k ∈ Finset.range K,
        (if t₀ * 2 ^ k < G then (t₀ * 2 ^ (k + 1)) ^ ε - (t₀ * 2 ^ k) ^ ε else 0)) ∧
      (t₀ * 2 ^ K < G → (t₀ * 2 ^ K) ^ ε ≤ t₀ ^ ε + ∑ k ∈ Finset.range K,
        (if t₀ * 2 ^ k < G then (t₀ * 2 ^ (k + 1)) ^ ε - (t₀ * 2 ^ k) ^ ε else 0)) := by
    intro K
    induction K with
    | zero =>
        constructor
        · intro h
          simp only [pow_zero, mul_one] at h
          simp only [Finset.range_zero, Finset.sum_empty, add_zero]
          exact Real.rpow_le_rpow hG h hε.le
        · intro _
          simp
    | succ K ih =>
        rw [Finset.sum_range_succ]
        constructor
        · intro hle
          by_cases hK : G ≤ t₀ * 2 ^ K
          · have h1 := ih.1 hK
            have h2 : 0 ≤ (if t₀ * 2 ^ K < G then (t₀ * 2 ^ (K + 1)) ^ ε - (t₀ * 2 ^ K) ^ ε
                else 0) := by
              split_ifs
              · linarith [hmono K]
              · exact le_rfl
            linarith
          · have hK' : t₀ * 2 ^ K < G := not_le.mp hK
            have h1 := ih.2 hK'
            rw [if_pos hK']
            have h3 : G ^ ε ≤ (t₀ * 2 ^ (K + 1)) ^ ε := Real.rpow_le_rpow hG hle hε.le
            linarith
        · intro hlt
          have hK : t₀ * 2 ^ K < G := lt_of_le_of_lt
            (by rw [pow_succ]; nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) K]) hlt
          have h1 := ih.2 hK
          rw [if_pos hK]
          linarith
  exact (key K).1 hGK

/-- **The geometric sum over the levels below `G`.** For `t₀ > 0`, `a > 0` and `G ≥ 0`,
`∑_{k < K, t₀ 2^k < G} (t₀ 2^k)^a ≤ 2^a/(2^a - 1) G^a`. -/
theorem sum_geometric_levels_le {t₀ a : ℝ} (ht₀ : 0 < t₀) (ha : 0 < a) (K : ℕ) {G : ℝ}
    (hG : 0 ≤ G) :
    ∑ k ∈ Finset.range K, (if t₀ * 2 ^ k < G then (t₀ * 2 ^ k) ^ a else 0) ≤
      2 ^ a / (2 ^ a - 1) * G ^ a := by
  have hr1 : 1 < (2 : ℝ) ^ a := Real.one_lt_rpow (by norm_num) ha
  have hr0 : 0 < (2 : ℝ) ^ a - 1 := by linarith
  have hr0' : (2 : ℝ) ^ a - 1 ≠ 0 := hr0.ne'
  have h2a0 : (2 : ℝ) ^ a ≠ 0 := by positivity
  have key : ∀ K : ℕ, ∀ G : ℝ, 0 ≤ G →
      (G ≤ t₀ → ∑ k ∈ Finset.range K, (if t₀ * 2 ^ k < G then (t₀ * 2 ^ k) ^ a else 0) = 0) ∧
      (t₀ < G → ∑ k ∈ Finset.range K, (if t₀ * 2 ^ k < G then (t₀ * 2 ^ k) ^ a else 0) ≤
        ((2 : ℝ) ^ a * G ^ a - t₀ ^ a) / ((2 : ℝ) ^ a - 1)) := by
    intro K
    induction K with
    | zero =>
        intro G hG
        refine ⟨fun _ => by simp, fun hlt => ?_⟩
        simp only [Finset.range_zero, Finset.sum_empty]
        have h1 : t₀ ^ a ≤ G ^ a := Real.rpow_le_rpow ht₀.le hlt.le ha.le
        have h2 : G ^ a ≤ (2 : ℝ) ^ a * G ^ a := by
          have := Real.rpow_nonneg hG a
          nlinarith
        exact div_nonneg (by linarith) hr0.le
    | succ K ih =>
        intro G hG
        have hshift : ∑ k ∈ Finset.range (K + 1),
            (if t₀ * 2 ^ k < G then (t₀ * 2 ^ k) ^ a else 0) =
            (2 : ℝ) ^ a * ∑ k ∈ Finset.range K,
              (if t₀ * 2 ^ k < G / 2 then (t₀ * 2 ^ k) ^ a else 0) +
              (if t₀ < G then t₀ ^ a else 0) := by
          rw [Finset.sum_range_succ', Finset.mul_sum]
          congr 1
          · refine Finset.sum_congr rfl fun k _ => ?_
            have hiff : t₀ * 2 ^ (k + 1) < G ↔ t₀ * 2 ^ k < G / 2 := by
              rw [lt_div_iff₀ two_pos, pow_succ]
              constructor <;> intro h <;> linarith
            by_cases h : t₀ * 2 ^ k < G / 2
            · rw [if_pos (hiff.mpr h), if_pos h, pow_succ,
                show t₀ * (2 ^ k * 2) = 2 * (t₀ * 2 ^ k) by ring,
                Real.mul_rpow (by norm_num) (mul_pos ht₀ (pow_pos (two_pos : (0 : ℝ) < 2) k)).le]
            · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h, mul_zero]
          · simp
        rw [hshift]
        have hG2 : 0 ≤ G / 2 := div_nonneg hG zero_le_two
        have hrG : (2 : ℝ) ^ a * (G / 2) ^ a = G ^ a := by
          rw [Real.div_rpow hG zero_le_two]
          field_simp
        constructor
        · intro hle
          rw [(ih (G / 2) hG2).1 (by linarith), if_neg (not_lt.mpr hle)]
          simp
        · intro hlt
          rw [if_pos hlt]
          by_cases h2 : t₀ < G / 2
          · have h3 := (ih (G / 2) hG2).2 h2
            have h4 : (2 : ℝ) ^ a * ∑ k ∈ Finset.range K,
                (if t₀ * 2 ^ k < G / 2 then (t₀ * 2 ^ k) ^ a else 0) ≤
                (2 : ℝ) ^ a * (((2 : ℝ) ^ a * (G / 2) ^ a - t₀ ^ a) / ((2 : ℝ) ^ a - 1)) :=
              mul_le_mul_of_nonneg_left h3 (by linarith)
            rw [hrG] at h4
            calc (2 : ℝ) ^ a * ∑ k ∈ Finset.range K,
                  (if t₀ * 2 ^ k < G / 2 then (t₀ * 2 ^ k) ^ a else 0) + t₀ ^ a
                ≤ (2 : ℝ) ^ a * ((G ^ a - t₀ ^ a) / ((2 : ℝ) ^ a - 1)) + t₀ ^ a := by linarith
              _ = ((2 : ℝ) ^ a * G ^ a - t₀ ^ a) / ((2 : ℝ) ^ a - 1) := by
                  field_simp
                  ring
          · rw [(ih (G / 2) hG2).1 (not_lt.mp h2), mul_zero, zero_add]
            have h1 : t₀ ^ a ≤ G ^ a := Real.rpow_le_rpow ht₀.le hlt.le ha.le
            rw [le_div_iff₀ hr0]
            nlinarith
  have hGa : 0 ≤ G ^ a := Real.rpow_nonneg hG a
  have hbound : ((2 : ℝ) ^ a * G ^ a - t₀ ^ a) / ((2 : ℝ) ^ a - 1) ≤
      2 ^ a / (2 ^ a - 1) * G ^ a := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by linarith [Real.rpow_nonneg ht₀.le a]) hr0.le
  by_cases hlt : t₀ < G
  · exact ((key K G hG).2 hlt).trans hbound
  · rw [(key K G hG).1 (not_lt.mp hlt)]
    exact mul_nonneg (div_nonneg (by linarith) hr0.le) hGa

/-- **Higher integrability on one triadic cube.** Under the reverse Hölder inequality on the proper
triadic subcubes of `P = cube n x₀`, for `0 < ε`, with `a = 1 + ε - θ`,
`∑_P g^{1+ε} ≤ (avg_P g)^ε ∑_P g + η ∑_{enl j n x₀} g^{1+ε}`,
`η = (2^ε - 1) (2 · 9^d A^θ) (2^a/(2^a - 1)) (1/δ)^a`. -/
theorem sum_rpow_le_of_reverse_holder {θ A δ ε : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) (hA : 0 < A)
    (hδ : 0 < δ) (hAδ : 2 * (A * δ) ^ θ ≤ 1) (hε : 0 < ε) (j n : ℕ) (x₀ : Vertex d)
    {g : Vertex d → ℝ} (hg : ∀ x, 0 ≤ g x)
    (hRH : ∀ k < n, ∀ y ∈ cube n x₀,
      avg (cube k y) g ≤ A * avg (enl j k y) (fun x => g x ^ θ) ^ (1 / θ)) :
    ∑ x ∈ cube n x₀, g x ^ (1 + ε) ≤
      avg (cube n x₀) g ^ ε * ∑ x ∈ cube n x₀, g x +
        (2 ^ ε - 1) * (2 * 9 ^ d * A ^ θ) * (2 ^ (1 + ε - θ) / (2 ^ (1 + ε - θ) - 1)) *
          (1 / δ) ^ (1 + ε - θ) * ∑ x ∈ enl j n x₀, g x ^ (1 + ε) := by
  set P := cube n x₀ with hPdef
  set a := 1 + ε - θ with ha
  have ha0 : 0 < a := by linarith
  have h2a : 1 < (2 : ℝ) ^ a := Real.one_lt_rpow (by norm_num) ha0
  have h2ε : 1 ≤ (2 : ℝ) ^ ε := Real.one_le_rpow (by norm_num) hε.le
  have hη0 : 0 ≤ (2 ^ ε - 1) * (2 * 9 ^ d * A ^ θ) * (2 ^ a / (2 ^ a - 1)) * (1 / δ) ^ a := by
    have h1 : 0 < (2 : ℝ) ^ a - 1 := by linarith
    have h2 : 0 ≤ (2 : ℝ) ^ ε - 1 := by linarith
    have h3 : 0 < A ^ θ := Real.rpow_pos_of_pos hA θ
    have h4 : 0 ≤ (1 / δ) ^ a := Real.rpow_nonneg (div_nonneg zero_le_one hδ.le) a
    have h5 : 0 ≤ (2 : ℝ) * 9 ^ d * A ^ θ := by positivity
    have h6 : 0 ≤ (2 : ℝ) ^ a / (2 ^ a - 1) := div_nonneg (by positivity) h1.le
    exact mul_nonneg (mul_nonneg (mul_nonneg h2 h5) h6) h4
  have hrhs2 : 0 ≤ (2 ^ ε - 1) * (2 * 9 ^ d * A ^ θ) * (2 ^ a / (2 ^ a - 1)) * (1 / δ) ^ a *
      ∑ x ∈ enl j n x₀, g x ^ (1 + ε) :=
    mul_nonneg hη0 (Finset.sum_nonneg fun x _ => Real.rpow_nonneg (hg x) _)
  have hcard : (0 : ℝ) < P.card := card_cube_pos n x₀
  have hcard' : (P.card : ℝ) ≠ 0 := hcard.ne'
  have h1ε : (1 : ℝ) + ε ≠ 0 := ne_of_gt (by linarith)
  set τ₀ := avg P g with hτ₀
  have hτ₀0 : 0 ≤ τ₀ := div_nonneg (Finset.sum_nonneg fun x _ => hg x) hcard.le
  rcases hτ₀0.eq_or_lt with hzero | hpos
  · -- `g = 0` on `P`
    have hsum : ∑ x ∈ P, g x = 0 := by
      have : τ₀ * P.card = ∑ x ∈ P, g x := by
        rw [hτ₀, avg]
        field_simp
      rw [← this, ← hzero, zero_mul]
    have hg0 : ∀ x ∈ P, g x = 0 := (Finset.sum_eq_zero_iff_of_nonneg fun x _ => hg x).mp hsum
    have hlhs : ∑ x ∈ P, g x ^ (1 + ε) = 0 :=
      Finset.sum_eq_zero fun x hx => by
        rw [hg0 x hx, Real.zero_rpow h1ε]
    rw [hlhs, hsum, mul_zero, zero_add]
    exact hrhs2
  -- the levels
  set t : ℕ → ℝ := fun k => τ₀ * 2 ^ k with ht
  have htpos : ∀ k, 0 < t k := fun k => mul_pos hpos (pow_pos (two_pos : (0 : ℝ) < 2) k)
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt ((∑ x ∈ P, g x) / τ₀) (one_lt_two : (1 : ℝ) < 2)
  have hgK : ∀ x ∈ P, g x ≤ t K := by
    intro x hx
    have h1 : g x ≤ ∑ y ∈ P, g y := Finset.single_le_sum (fun y _ => hg y) hx
    have h2 : ∑ y ∈ P, g y < τ₀ * 2 ^ K := by
      rw [div_lt_iff₀ hpos] at hK
      linarith
    exact (h1.trans h2.le)
  -- pointwise layer cake
  have hpt : ∀ x ∈ P, g x ^ (1 + ε) ≤ τ₀ ^ ε * g x + ∑ k ∈ Finset.range K,
      ((t (k + 1)) ^ ε - (t k) ^ ε) * (if t k < g x then g x else 0) := by
    intro x hx
    have h1 := rpow_le_layer_sum hpos hε K (hg x) (hgK x hx)
    have h2 : g x ^ (1 + ε) = g x * g x ^ ε := by
      rw [Real.rpow_add' (hg x) h1ε, Real.rpow_one]
    rw [h2]
    calc g x * g x ^ ε ≤ g x * (τ₀ ^ ε + ∑ k ∈ Finset.range K,
          (if τ₀ * 2 ^ k < g x then (τ₀ * 2 ^ (k + 1)) ^ ε - (τ₀ * 2 ^ k) ^ ε else 0)) :=
          mul_le_mul_of_nonneg_left h1 (hg x)
      _ = τ₀ ^ ε * g x + ∑ k ∈ Finset.range K,
          ((t (k + 1)) ^ ε - (t k) ^ ε) * (if t k < g x then g x else 0) := by
          rw [mul_add, Finset.mul_sum, mul_comm (g x) (τ₀ ^ ε)]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [ht]
          split_ifs <;> ring
  have hsumP : ∑ x ∈ P, g x ^ (1 + ε) ≤ τ₀ ^ ε * ∑ x ∈ P, g x + ∑ k ∈ Finset.range K,
      ((t (k + 1)) ^ ε - (t k) ^ ε) * ∑ x ∈ P.filter (fun x => t k < g x), g x := by
    calc ∑ x ∈ P, g x ^ (1 + ε) ≤ ∑ x ∈ P, (τ₀ ^ ε * g x + ∑ k ∈ Finset.range K,
          ((t (k + 1)) ^ ε - (t k) ^ ε) * (if t k < g x then g x else 0)) := Finset.sum_le_sum hpt
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_filter, Finset.mul_sum]
  -- the level-set estimate at every level
  set CL : ℝ := 2 * 9 ^ d * A ^ θ with hCL
  have hCL0 : 0 ≤ CL := by
    have : 0 < A ^ θ := Real.rpow_pos_of_pos hA θ
    positivity
  set I : ℕ → Vertex d → ℝ := fun k x => if t k < g x / δ then (t k) ^ a else 0 with hI
  have hlevel : ∀ k ∈ Finset.range K,
      ((t (k + 1)) ^ ε - (t k) ^ ε) * ∑ x ∈ P.filter (fun x => t k < g x), g x ≤
        (2 ^ ε - 1) * CL * ∑ x ∈ enl j n x₀, g x ^ θ * I k x := by
    intro k _
    have hdiff : (t (k + 1)) ^ ε - (t k) ^ ε = (2 ^ ε - 1) * (t k) ^ ε := by
      simp only [ht]
      rw [pow_succ, show τ₀ * (2 ^ k * 2) = 2 * (τ₀ * 2 ^ k) by ring,
        Real.mul_rpow (by norm_num) (htpos k).le]
      ring
    have hτk : avg P g ≤ t k := by
      rw [← hτ₀]
      simp only [ht]
      have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      nlinarith
    have hls := level_set_estimate hθ hA hδ hAδ (htpos k) j n x₀ hg hRH hτk
    have hdiff0 : 0 ≤ (2 ^ ε - 1) * (t k) ^ ε :=
      mul_nonneg (by linarith) (Real.rpow_nonneg (htpos k).le _)
    rw [hdiff]
    calc (2 ^ ε - 1) * t k ^ ε * ∑ x ∈ P.filter (fun x => t k < g x), g x
        ≤ (2 ^ ε - 1) * t k ^ ε * (CL * t k ^ (1 - θ) *
            ∑ x ∈ (enl j n x₀).filter (fun x => δ * t k < g x), g x ^ θ) :=
          mul_le_mul_of_nonneg_left hls hdiff0
      _ = (2 ^ ε - 1) * CL * ∑ x ∈ enl j n x₀, g x ^ θ * I k x := by
          rw [Finset.sum_filter, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          have hiff : δ * t k < g x ↔ t k < g x / δ := by
            rw [lt_div_iff₀ hδ, mul_comm]
          have hpow : t k ^ ε * t k ^ (1 - θ) = t k ^ a := by
            rw [← Real.rpow_add (htpos k), ha]
            congr 1
            ring
          simp only [hI]
          by_cases h : δ * t k < g x
          · rw [if_pos h, if_pos (hiff.mp h), ← hpow]
            ring
          · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]
            ring
  -- summing the levels
  have hgeom : ∀ x ∈ enl j n x₀, ∑ k ∈ Finset.range K, I k x ≤
      2 ^ a / (2 ^ a - 1) * (g x / δ) ^ a := by
    intro x _
    exact sum_geometric_levels_le hpos ha0 K (div_nonneg (hg x) hδ.le)
  have hlevels : ∑ k ∈ Finset.range K,
      ((t (k + 1)) ^ ε - (t k) ^ ε) * ∑ x ∈ P.filter (fun x => t k < g x), g x ≤
        (2 ^ ε - 1) * CL * (2 ^ a / (2 ^ a - 1)) * (1 / δ) ^ a *
          ∑ x ∈ enl j n x₀, g x ^ (1 + ε) := by
    refine (Finset.sum_le_sum hlevel).trans ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    have hc0 : 0 ≤ (2 ^ ε - 1) * CL := mul_nonneg (by linarith) hCL0
    rw [mul_assoc ((2 ^ ε - 1) * CL), mul_assoc ((2 ^ ε - 1) * CL)]
    refine mul_le_mul_of_nonneg_left ?_ hc0
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    rw [← Finset.mul_sum]
    have hgθ : 0 ≤ g x ^ θ := Real.rpow_nonneg (hg x) θ
    calc g x ^ θ * ∑ k ∈ Finset.range K, I k x ≤ g x ^ θ * (2 ^ a / (2 ^ a - 1) * (g x / δ) ^ a) :=
          mul_le_mul_of_nonneg_left (hgeom x hx) hgθ
      _ = 2 ^ a / (2 ^ a - 1) * (1 / δ) ^ a * g x ^ (1 + ε) := by
          rw [div_eq_mul_one_div (g x) δ, Real.mul_rpow (hg x) (div_nonneg zero_le_one hδ.le),
            show (1 + ε) = θ + a by rw [ha]; ring,
            Real.rpow_add' (hg x) (ne_of_gt (by linarith))]
          ring
  calc ∑ x ∈ P, g x ^ (1 + ε) ≤ τ₀ ^ ε * ∑ x ∈ P, g x + ∑ k ∈ Finset.range K,
        ((t (k + 1)) ^ ε - (t k) ^ ε) * ∑ x ∈ P.filter (fun x => t k < g x), g x := hsumP
    _ ≤ τ₀ ^ ε * ∑ x ∈ P, g x + (2 ^ ε - 1) * CL * (2 ^ a / (2 ^ a - 1)) * (1 / δ) ^ a *
          ∑ x ∈ enl j n x₀, g x ^ (1 + ε) := by linarith

end Rigidity.Proofs.Cluster
