import Rigidity.Proofs.Section5.Separation.Lattice

/-!
# Lemma 5.19: simple chains of a graph

Paths of a graph indexed by `ℤ` on an interval `[0, ℓ]`, as used for the arcs `A_p`, `A_n`, `A_z`
of the proof of `SeparationStep` (corrected draft L2051-2089): simple chains extracted from
walks, reversal, concatenation, the arc `P, f 0, …, f ℓ, Q` (`chainBracket`), and the traces in
the plane of concatenations and reversals of lattice chains.
-/

open Set LatticeProb.Percolation

namespace Rigidity.Proofs.Section5

variable {V : Type*} {G : SimpleGraph V}

/-- `f` is a chain of `G` of length `ℓ` without repeated vertices. -/
structure IsSimpleChain (G : SimpleGraph V) (f : ℤ → V) (ℓ : ℕ) : Prop where
  adj : ∀ k : ℤ, 0 ≤ k → k < ℓ → G.Adj (f k) (f (k + 1))
  inj : ∀ k k' : ℤ, 0 ≤ k → k ≤ ℓ → 0 ≤ k' → k' ≤ ℓ → f k = f k' → k = k'

/-- A walk contains a simple chain between its endpoints. -/
theorem exists_isSimpleChain {x y : V} (w : G.Walk x y) :
    ∃ (f : ℤ → V) (ℓ : ℕ), f 0 = x ∧ f ℓ = y ∧ IsSimpleChain G f ℓ ∧ ∀ k, f k ∈ w.support := by
  classical
  refine ⟨fun k => w.bypass.getVert k.toNat, w.bypass.length, by simp, by simp, ⟨?_, ?_⟩,
    fun k => w.support_bypass_subset_support (w.bypass.getVert_mem_support _)⟩
  · intro k h0 h1
    have := w.bypass.adj_getVert_succ (i := k.toNat) (by omega)
    rwa [show (k + 1).toNat = k.toNat + 1 by omega]
  · intro k k' h0 h1 h0' h1' h
    have := (SimpleGraph.Walk.bypass_isPath w).getVert_injOn (by simp; omega) (by simp; omega) h
    omega

/-- The reversal of `f` on `[0, ℓ]`. -/
def chainRev (f : ℤ → V) (ℓ : ℕ) : ℤ → V := fun k => f (ℓ - k)

theorem IsSimpleChain.rev {f : ℤ → V} {ℓ : ℕ} (h : IsSimpleChain G f ℓ) :
    IsSimpleChain G (chainRev f ℓ) ℓ := by
  refine ⟨fun k h0 h1 => ?_, fun k k' h0 h1 h0' h1' e => ?_⟩
  · have := (h.adj (ℓ - k - 1) (by omega) (by omega)).symm
    rw [sub_add_cancel] at this
    show G.Adj (f (ℓ - k)) (f (ℓ - (k + 1)))
    rwa [show (ℓ : ℤ) - (k + 1) = ℓ - k - 1 by ring]
  · have := h.inj _ _ (by omega) (by omega) (by omega) (by omega) e
    omega

/-- The concatenation of `f` on `[0, ℓ]` with `g`, shifted by `ℓ`. -/
def chainAppend (f : ℤ → V) (ℓ : ℕ) (g : ℤ → V) : ℤ → V := fun k =>
  if k ≤ ℓ then f k else g (k - ℓ)

theorem chainAppend_of_le {f g : ℤ → V} {ℓ : ℕ} {k : ℤ} (h : k ≤ ℓ) :
    chainAppend f ℓ g k = f k := if_pos h

theorem chainAppend_of_ge {f g : ℤ → V} {ℓ : ℕ} {k : ℤ} (hfg : f ℓ = g 0) (h : (ℓ : ℤ) ≤ k) :
    chainAppend f ℓ g k = g (k - ℓ) := by
  rcases h.lt_or_eq with h | rfl
  · exact if_neg (not_le.2 h)
  · rw [chainAppend_of_le le_rfl, hfg, sub_self]

theorem IsSimpleChain.append {f g : ℤ → V} {ℓ m : ℕ} (hf : IsSimpleChain G f ℓ)
    (hg : IsSimpleChain G g m) (hfg : f ℓ = g 0)
    (hd : ∀ k k' : ℤ, 0 ≤ k → k ≤ ℓ → 0 ≤ k' → k' ≤ m → f k = g k' → k = ℓ ∧ k' = 0) :
    IsSimpleChain G (chainAppend f ℓ g) (ℓ + m) := by
  refine ⟨fun k h0 h1 => ?_, fun k k' h0 h1 h0' h1' e => ?_⟩
  · by_cases hk : k < ℓ
    · rw [chainAppend_of_le hk.le, chainAppend_of_le (by omega)]
      exact hf.adj k h0 hk
    · rw [chainAppend_of_ge hfg (by omega), chainAppend_of_ge hfg (by omega),
        show k + 1 - ℓ = k - ℓ + 1 by ring]
      exact hg.adj _ (by omega) (by push_cast at h1; omega)
  · push_cast at h1 h1'
    by_cases hk : k ≤ ℓ <;> by_cases hk' : k' ≤ ℓ
    · rw [chainAppend_of_le hk, chainAppend_of_le hk'] at e
      exact hf.inj _ _ h0 hk h0' hk' e
    · rw [chainAppend_of_le hk, chainAppend_of_ge hfg (by omega)] at e
      have := hd _ _ h0 hk (by omega) (by omega) e
      omega
    · rw [chainAppend_of_ge hfg (by omega), chainAppend_of_le hk'] at e
      have := hd _ _ h0' hk' (by omega) (by omega) e.symm
      omega
    · rw [chainAppend_of_ge hfg (by omega), chainAppend_of_ge hfg (by omega)] at e
      have := hg.inj _ _ (by omega) (by omega) (by omega) (by omega) e
      omega

/-- The values of a concatenation are values of its pieces. -/
theorem chainAppend_mem {f g : ℤ → V} {ℓ m : ℕ} (hfg : f ℓ = g 0) {k : ℤ} (h0 : 0 ≤ k)
    (h1 : k ≤ ℓ + m) :
    (∃ j : ℤ, 0 ≤ j ∧ j ≤ ℓ ∧ chainAppend f ℓ g k = f j) ∨
      ∃ j : ℤ, 0 ≤ j ∧ j ≤ m ∧ chainAppend f ℓ g k = g j := by
  by_cases hk : k ≤ ℓ
  · exact Or.inl ⟨k, h0, hk, chainAppend_of_le hk⟩
  · exact Or.inr ⟨k - ℓ, by omega, by omega, chainAppend_of_ge hfg (by omega)⟩

/-- The arc `x, f 0, …, f ℓ, y` of length `ℓ + 2`. -/
def chainBracket (x : V) (f : ℤ → V) (ℓ : ℕ) (y : V) : ℤ → V := fun k =>
  if k ≤ 0 then x else if k ≤ ℓ + 1 then f (k - 1) else y

theorem chainBracket_zero (x : V) (f : ℤ → V) (ℓ : ℕ) (y : V) : chainBracket x f ℓ y 0 = x :=
  if_pos le_rfl

theorem chainBracket_last (x : V) (f : ℤ → V) (ℓ : ℕ) (y : V) :
    chainBracket x f ℓ y ((ℓ + 2 : ℕ) : ℤ) = y := by
  simp only [chainBracket]
  rw [if_neg (by omega), if_neg (by omega)]

theorem chainBracket_mid (x : V) (f : ℤ → V) (ℓ : ℕ) (y : V) {k : ℤ} (h0 : 0 < k)
    (h1 : k ≤ ℓ + 1) : chainBracket x f ℓ y k = f (k - 1) := by
  simp only [chainBracket]
  rw [if_neg (by omega), if_pos h1]

theorem IsSimpleChain.bracket {x y : V} {f : ℤ → V} {ℓ : ℕ} (hf : IsSimpleChain G f ℓ)
    (hx : G.Adj x (f 0)) (hy : G.Adj (f ℓ) y) (hxy : x ≠ y)
    (hfx : ∀ j : ℤ, 0 ≤ j → j ≤ ℓ → f j ≠ x) (hfy : ∀ j : ℤ, 0 ≤ j → j ≤ ℓ → f j ≠ y) :
    IsSimpleChain G (chainBracket x f ℓ y) (ℓ + 2) := by
  have hval : ∀ k : ℤ, 0 ≤ k → k ≤ ℓ + 2 → (k = 0 ∧ chainBracket x f ℓ y k = x) ∨
      (0 < k ∧ k ≤ ℓ + 1 ∧ chainBracket x f ℓ y k = f (k - 1)) ∨
      (k = ℓ + 2 ∧ chainBracket x f ℓ y k = y) := by
    intro k h0 h1
    rcases h0.lt_or_eq with h0 | rfl
    · by_cases hk : k ≤ ℓ + 1
      · exact Or.inr (Or.inl ⟨h0, hk, chainBracket_mid x f ℓ y h0 hk⟩)
      · refine Or.inr (Or.inr ⟨by omega, ?_⟩)
        have : k = ((ℓ + 2 : ℕ) : ℤ) := by push_cast; omega
        rw [this, chainBracket_last]
    · exact Or.inl ⟨rfl, chainBracket_zero x f ℓ y⟩
  refine ⟨fun k h0 h1 => ?_, fun k k' h0 h1 h0' h1' e => ?_⟩
  · push_cast at h1
    rcases hval k h0 (by omega) with ⟨rfl, hk⟩ | ⟨hk0, hk1, hk⟩ | ⟨hk, -⟩
    · rw [hk, zero_add, chainBracket_mid x f ℓ y one_pos (by omega)]
      simpa using hx
    · rw [hk]
      by_cases hk2 : k ≤ ℓ
      · rw [chainBracket_mid x f ℓ y (by omega) (by omega)]
        have := hf.adj (k - 1) (by omega) (by omega)
        rwa [sub_add_cancel, show k + 1 - 1 = k by ring] at *
      · have : k + 1 = ((ℓ + 2 : ℕ) : ℤ) := by push_cast; omega
        rw [this, chainBracket_last, show k - 1 = ℓ by omega]
        exact hy
    · omega
  · push_cast at h1 h1'
    rcases hval k h0 h1 with ⟨hk, ek⟩ | ⟨hk0, hk1, ek⟩ | ⟨hk, ek⟩ <;>
      rcases hval k' h0' h1' with ⟨hk', ek'⟩ | ⟨hk0', hk1', ek'⟩ | ⟨hk', ek'⟩ <;>
      rw [ek, ek'] at e
    · omega
    · exact absurd e.symm (hfx _ (by omega) (by omega))
    · exact absurd e hxy
    · exact absurd e (hfx _ (by omega) (by omega))
    · have := hf.inj _ _ (by omega) (by omega) (by omega) (by omega) e
      omega
    · exact absurd e (hfy _ (by omega) (by omega))
    · exact absurd e.symm hxy
    · exact absurd e.symm (hfy _ (by omega) (by omega))
    · omega

/-! ### Traces of concatenations and reversals -/

theorem chainTrace_chainRev (h : V → Vertex 2) (f : ℤ → V) (ℓ : ℕ) :
    chainTrace (h ∘ chainRev f ℓ) (Ico 0 ℓ) = chainTrace (h ∘ f) (Ico 0 ℓ) := by
  ext v
  simp only [chainTrace, mem_iUnion, mem_Ico, Function.comp, chainRev]
  constructor
  · rintro ⟨k, ⟨h0, h1⟩, hv⟩
    refine ⟨ℓ - k - 1, ⟨by omega, by omega⟩, ?_⟩
    rw [edgeSegment_comm, show (ℓ : ℤ) - k - 1 + 1 = ℓ - k by ring]
    rwa [show (ℓ : ℤ) - (k + 1) = ℓ - k - 1 by ring] at hv
  · rintro ⟨k, ⟨h0, h1⟩, hv⟩
    refine ⟨ℓ - k - 1, ⟨by omega, by omega⟩, ?_⟩
    rw [edgeSegment_comm, show (ℓ : ℤ) - (ℓ - k - 1 + 1) = k by ring,
      show (ℓ : ℤ) - (ℓ - k - 1) = k + 1 by ring]
    exact hv

theorem chainTrace_chainAppend (h : V → Vertex 2) {f g : ℤ → V} {ℓ m : ℕ} (hfg : f ℓ = g 0) :
    chainTrace (h ∘ chainAppend f ℓ g) (Ico 0 (ℓ + m : ℕ)) =
      chainTrace (h ∘ f) (Ico 0 ℓ) ∪ chainTrace (h ∘ g) (Ico 0 m) := by
  ext v
  simp only [chainTrace, mem_union, mem_iUnion, mem_Ico, Function.comp]
  constructor
  · rintro ⟨k, ⟨h0, h1⟩, hv⟩
    push_cast at h1
    by_cases hk : k < ℓ
    · rw [chainAppend_of_le hk.le, chainAppend_of_le (by omega)] at hv
      exact Or.inl ⟨k, ⟨h0, hk⟩, hv⟩
    · rw [chainAppend_of_ge hfg (by omega), chainAppend_of_ge hfg (by omega),
        show k + 1 - ℓ = k - ℓ + 1 by ring] at hv
      exact Or.inr ⟨k - ℓ, ⟨by omega, by omega⟩, hv⟩
  · rintro (⟨k, ⟨h0, h1⟩, hv⟩ | ⟨k, ⟨h0, h1⟩, hv⟩)
    · refine ⟨k, ⟨h0, by push_cast; omega⟩, ?_⟩
      rwa [chainAppend_of_le h1.le, chainAppend_of_le (by omega)]
    · refine ⟨k + ℓ, ⟨by omega, by push_cast; omega⟩, ?_⟩
      rwa [chainAppend_of_ge hfg (by omega), chainAppend_of_ge hfg (by omega),
        add_sub_cancel_right, show k + ℓ + 1 - ℓ = k + 1 by ring]

end Rigidity.Proofs.Section5
