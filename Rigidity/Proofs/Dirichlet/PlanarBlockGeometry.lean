import Rigidity.Proofs.Dirichlet.PlanarTileSums

/-!
# The block of tiles of Lemma 6.3

For the cube `□_m` of side `L = 3^m`, a depth `r` and tiles of side `K = 3^k` with
`2 (r + 3) + 3K ≤ L`, the block of `M` tiles per side starting at the first point `z₀` of the
triadic grid of scale `k` after the corner of `shrinkCube □_m (r + 3)`, with
`M = ⌊(L − 2(r + 3))/K⌋ − 2`, together with one more row and column of tiles, lies in
`shrinkCube □_m (r + 3)`, and covers `□_m` up to a layer of width `D = r + 3 + 3K`
(`blockGeometry`).
-/

open Finset LatticeProb LatticeHC LatticeProb.Percolation Rigidity.Percolation
open scoped Classical

namespace Rigidity.Dirichlet

/-- The corner of the block of tiles. -/
def blockCorner (m k r : ℕ) : Vertex 2 :=
  triadicGridCorner k fun t => (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.corner t + (r + 3 : ℕ)

/-- The number of tiles per side of the block. -/
def blockCount (m k r : ℕ) : ℕ := (3 ^ m - 2 * (r + 3)) / 3 ^ k - 2

theorem blockCorner_dvd (m k r : ℕ) (t : Fin 2) :
    (3 : ℤ) ^ k ∣ blockCorner m k r t + (3 : ℤ) ^ k / 2 :=
  (triadicGridCorner_spec k _ t).2.2

/-- **The geometry of the block.** -/
theorem blockGeometry {m k r : ℕ} (hbig : 2 * (r + 3) + 3 * 3 ^ k ≤ 3 ^ m) :
    (cornerCube (blockCorner m k r) ((blockCount m k r + 1) * 3 ^ k)).vertices ⊆
        (shrinkCube (⟨m, 0⟩ : TriadicCube 2).toIntegerCube (r + 3)).vertices ∧
      (∀ t, blockCorner m k r t ≤
        (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.corner t + (r + 3 + 3 * 3 ^ k : ℕ)) ∧
      (∀ t, (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.corner t +
          (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size ≤
        blockCorner m k r t + (blockCount m k r * 3 ^ k : ℕ) + (r + 3 + 3 * 3 ^ k : ℕ)) := by
  set K := 3 ^ k with hKdef
  set A := 3 ^ m - 2 * (r + 3) with hA
  set q := A / K with hq
  have hK : 0 < K := by positivity
  have h1 : q * K ≤ A := Nat.div_mul_le_self A K
  have h2 : A < q * K + K := by
    rw [hq]
    exact Nat.lt_div_mul_add hK
  have hq3 : 3 ≤ q := by
    rw [hq, Nat.le_div_iff_mul_le hK]
    omega
  have hM : blockCount m k r = q - 2 := rfl
  have hMK : (q - 2) * K = q * K - 2 * K := Nat.sub_mul q 2 K
  have hM1K : (q - 2 + 1) * K = q * K - K := by
    rw [show q - 2 + 1 = q - 1 by omega, Nat.sub_mul, one_mul]
  have hsize : (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.size = 3 ^ m := rfl
  have hspec := fun t => triadicGridCorner_spec k
    (fun t => (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.corner t + (r + 3 : ℕ)) t
  refine ⟨fun x hx => ?_, fun t => ?_, fun t => ?_⟩
  · rw [IntegerCube.mem_vertices] at hx
    rw [mem_shrinkCube_iff]
    intro t
    have h := hx t
    have hs := hspec t
    beta_reduce at hs
    simp only [cornerCube, blockCorner] at h ⊢
    generalize triadicGridCorner k (fun t => (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.corner t +
      ((r + 3 : ℕ) : ℤ)) t = Z at *
    rw [hM, hM1K] at h
    rw [hsize]
    have hqK : ((q * K - K : ℕ) : ℤ) = (q * K : ℕ) - (K : ℤ) := by
      rw [Nat.cast_sub (by nlinarith)]
    have hAZ : ((3 ^ m - 2 * (r + 3) : ℕ) : ℤ) = (A : ℤ) := rfl
    rw [hqK] at h
    have hA' : (A : ℤ) = ((3 ^ m : ℕ) : ℤ) - 2 * ((r + 3 : ℕ) : ℤ) := by
      rw [hA, Nat.cast_sub (by omega)]
      push_cast
      ring
    have h1' : ((q * K : ℕ) : ℤ) ≤ (A : ℤ) := by exact_mod_cast h1
    have hK' : ((3 ^ k : ℕ) : ℤ) = (K : ℤ) := rfl
    push_cast at hs h1' hA' ⊢
    constructor
    · linarith [hs.1, h.1]
    · have : ((3 ^ m - 2 * (r + 3) : ℕ) : ℤ) = (3 : ℤ) ^ m - 2 * ((r : ℤ) + 3) := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      rw [this]
      push_cast at h
      nlinarith [hs.2.1, h.2]
  · have hs := hspec t
    beta_reduce at hs
    simp only [blockCorner]
    generalize triadicGridCorner k (fun t => (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.corner t +
      ((r + 3 : ℕ) : ℤ)) t = Z at *
    push_cast at hs ⊢
    nlinarith [hs.2.1]
  · have hs := hspec t
    beta_reduce at hs
    simp only [blockCorner]
    generalize triadicGridCorner k (fun t => (⟨m, 0⟩ : TriadicCube 2).toIntegerCube.corner t +
      ((r + 3 : ℕ) : ℤ)) t = Z at *
    rw [hM, hMK, hsize]
    have h2' : ((A : ℕ) : ℤ) < ((q * K : ℕ) : ℤ) + (K : ℤ) := by exact_mod_cast h2
    have hqK : ((q * K - 2 * K : ℕ) : ℤ) = (q * K : ℕ) - 2 * (K : ℤ) := by
      rw [Nat.cast_sub (by nlinarith)]
      push_cast
      ring
    rw [hqK]
    have hA' : (A : ℤ) = ((3 ^ m : ℕ) : ℤ) - 2 * ((r + 3 : ℕ) : ℤ) := by
      rw [hA, Nat.cast_sub (by omega)]
      push_cast
      ring
    push_cast at hs h2' hA' ⊢
    nlinarith [hs.1]

end Rigidity.Dirichlet
