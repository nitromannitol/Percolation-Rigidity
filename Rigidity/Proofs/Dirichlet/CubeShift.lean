import Rigidity.Proofs.Dirichlet.CubeStokes

/-!
# Translated cubes

Two cubes of side `N` with corners `x` and `y` differ in at most `Σ_i |x_i − y_i| N^{d-1}` points
each way. By Cauchy–Schwarz on the symmetric difference,
`(N^{-d} (Σ_{x + □} h − Σ_{y + □} h))² ≤ (2 Σ_i |x_i − y_i| / N) N^{-d} (Σ_{x + □} h² + Σ_{y + □} h²)`.

This is Step 4 of the proof of Armstrong–Dario, Lemma 6.2: the mesoscopic averages
`p(x) = |□_n|^{-1} Σ_{x + □_n} ∇w` at points at distance at most `3^k` differ by
`C 3^{(k-n)/2}` times the normalized `L²` norm of `∇w` on `x + □_n + □_k`.
-/

open Finset LatticeProb

namespace Rigidity.Dirichlet

open Rigidity.Percolation LatticeProb.Percolation

variable {d : ℕ}

/-- The integers in `[a, a + N)` but not in `[b, b + N)` number at most `|a − b|`. -/
theorem card_Ico_sdiff_Ico_le (a b : ℤ) (N : ℕ) :
    #(Finset.Ico a (a + N) \ Finset.Ico b (b + N)) ≤ (a - b).natAbs := by
  have hsub : Finset.Ico a (a + N) \ Finset.Ico b (b + N) ⊆
      Finset.Ico a b ∪ Finset.Ico (b + N) (a + N) := by
    intro t ht
    simp only [Finset.mem_sdiff, Finset.mem_Ico, not_and, not_lt] at ht
    simp only [Finset.mem_union, Finset.mem_Ico]
    by_cases htb : t < b
    · exact Or.inl ⟨ht.1.1, htb⟩
    · exact Or.inr ⟨ht.2 (by omega), ht.1.2⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  rw [Int.card_Ico, Int.card_Ico]
  omega

/-- **Points of one cube missing from a translate**: `#(x + □ \ y + □) ≤ Σ_i |x_i − y_i| N^{d-1}`. -/
theorem card_cornerCube_sdiff_le (x y : Vertex d) (N : ℕ) :
    #((cornerCube x N).vertices \ (cornerCube y N).vertices) ≤
      (∑ i, (x i - y i).natAbs) * N ^ (d - 1) := by
  classical
  set I : Fin d → Finset ℤ := fun k => Finset.Ico (x k) (x k + (N : ℤ))
  have hsub : (cornerCube x N).vertices \ (cornerCube y N).vertices ⊆
      Finset.univ.biUnion fun i => Fintype.piFinset (Function.update I i
        (Finset.Ico (x i) (x i + N) \ Finset.Ico (y i) (y i + N))) := by
    intro z hz
    obtain ⟨hzx, hzy⟩ := Finset.mem_sdiff.mp hz
    rw [IntegerCube.mem_vertices] at hzx hzy
    push Not at hzy
    obtain ⟨i, hi⟩ := hzy
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Fintype.mem_piFinset.mpr fun k => ?_⟩
    by_cases hk : k = i
    · subst hk
      simp only [Function.update_self, Finset.mem_sdiff, Finset.mem_Ico]
      exact ⟨hzx k, fun h => absurd h.2 (not_lt.mpr (hi h.1))⟩
    · rw [Function.update_of_ne hk]
      exact Finset.mem_Ico.mpr (hzx k)
  refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := card_piFinset_update (cornerCube x N) i
    (Finset.Ico (x i) (x i + N) \ Finset.Ico (y i) (y i + N))
  simp only [cornerCube] at h
  rw [h]
  exact Nat.mul_le_mul_right _ (card_Ico_sdiff_Ico_le _ _ _)

/-- **Translated cube sums**: for cubes of side `N > 0` with corners `x`, `y`,
`(N^{-d} (Σ_{x + □} h − Σ_{y + □} h))² ≤
  (2 Σ_i |x_i − y_i| / N) · N^{-d} (Σ_{x + □} h² + Σ_{y + □} h²)`. -/
theorem sq_sum_cornerCube_sub_div_le (x y : Vertex d) {N : ℕ} (hN : 0 < N) (h : Vertex d → ℝ) :
    ((∑ z ∈ (cornerCube x N).vertices, h z - ∑ z ∈ (cornerCube y N).vertices, h z) /
        (N : ℝ) ^ d) ^ 2 ≤
      2 * (∑ i, ((x i - y i).natAbs : ℝ)) / N *
        ((∑ z ∈ (cornerCube x N).vertices, h z ^ 2 +
          ∑ z ∈ (cornerCube y N).vertices, h z ^ 2) / (N : ℝ) ^ d) := by
  classical
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hxy : x = y := Subsingleton.elim _ _
    subst hxy
    simp
  set A := (cornerCube x N).vertices
  set B := (cornerCube y N).vertices
  set D : ℝ := ∑ i, ((x i - y i).natAbs : ℝ)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hD : 0 ≤ D := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hsplit : ∑ z ∈ A, h z - ∑ z ∈ B, h z = ∑ z ∈ A \ B, h z - ∑ z ∈ B \ A, h z := by
    rw [← Finset.sum_inter_add_sum_sdiff A B h, ← Finset.sum_inter_add_sum_sdiff B A h,
      Finset.inter_comm B A]
    ring
  have hcardAB : (#(A \ B) : ℝ) ≤ D * (N : ℝ) ^ (d - 1) := by
    have := card_cornerCube_sdiff_le x y N
    simp only [D]
    exact_mod_cast this
  have hcardBA : (#(B \ A) : ℝ) ≤ D * (N : ℝ) ^ (d - 1) := by
    have := card_cornerCube_sdiff_le y x N
    have hsym : ∀ i, (y i - x i).natAbs = (x i - y i).natAbs := fun i => by
      rw [← Int.natAbs_neg, neg_sub]
    simp only [hsym] at this
    simp only [D]
    exact_mod_cast this
  have hsqA : ∑ z ∈ A \ B, h z ^ 2 ≤ ∑ z ∈ A, h z ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => sq_nonneg _
  have hsqB : ∑ z ∈ B \ A, h z ^ 2 ≤ ∑ z ∈ B, h z ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun _ _ _ => sq_nonneg _
  have hcsA := sq_sum_le_card_mul_sum_sq (s := A \ B) (f := h)
  have hcsB := sq_sum_le_card_mul_sum_sq (s := B \ A) (f := h)
  have h0A : 0 ≤ ∑ z ∈ A \ B, h z ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h0B : 0 ≤ ∑ z ∈ B \ A, h z ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hP : 0 ≤ (N : ℝ) ^ (d - 1) := by positivity
  have hmain : (∑ z ∈ A, h z - ∑ z ∈ B, h z) ^ 2 ≤
      2 * (D * (N : ℝ) ^ (d - 1)) * (∑ z ∈ A, h z ^ 2 + ∑ z ∈ B, h z ^ 2) := by
    rw [hsplit]
    have h2 : (∑ z ∈ A \ B, h z - ∑ z ∈ B \ A, h z) ^ 2 ≤
        2 * (∑ z ∈ A \ B, h z) ^ 2 + 2 * (∑ z ∈ B \ A, h z) ^ 2 := by
      nlinarith [sq_nonneg (∑ z ∈ A \ B, h z + ∑ z ∈ B \ A, h z)]
    refine h2.trans ?_
    have e1 : (∑ z ∈ A \ B, h z) ^ 2 ≤ D * (N : ℝ) ^ (d - 1) * ∑ z ∈ A, h z ^ 2 :=
      hcsA.trans (mul_le_mul hcardAB hsqA h0A (by positivity))
    have e2 : (∑ z ∈ B \ A, h z) ^ 2 ≤ D * (N : ℝ) ^ (d - 1) * ∑ z ∈ B, h z ^ 2 :=
      hcsB.trans (mul_le_mul hcardBA hsqB h0B (by positivity))
    nlinarith [e1, e2]
  have hpow : (N : ℝ) ^ d = (N : ℝ) ^ (d - 1) * N := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  rw [div_pow, div_le_iff₀ (by positivity)]
  refine hmain.trans (le_of_eq ?_)
  rw [hpow]
  field_simp

end Rigidity.Dirichlet
