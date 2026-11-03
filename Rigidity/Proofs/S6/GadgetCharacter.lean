import Rigidity.Steps.S6.SlowMixing
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-! # Section 6: the characters of the gadgets

step:6.5-gadget-characters (paper L2953-2961, Fig. slow-mixing-gadget, correction C25). For a
gadget pair `a, b` in `V` (two sites with exactly two open edges, to the same two sites), the
parity `f ↦ f(a) + f(b) mod 2` vanishes on `Δ_V ℤ^V`: the two neighbour sums of `Δ_V h` at `a` and
`b` coincide, so `Δ_V h (a) + Δ_V h (b) = 2 (h(a) + h(b) - Σ)`. Composed with the sign character
of `ZMod 2` it gives a character `[f] ↦ (-1)^{f(a) + f(b)}` of the sandpile group, equal to `-1`
exactly on the chips `[1_a]`, `[1_b]`: it is nontrivial with eigenvalue `1 - 4/|V|`, and it
determines `{a, b}`, so the map from gadget sites to characters has fibres of size at most two. -/

open LatticeProb.Percolation Classical Rigidity.Section6 Rigidity.Steps.S6

namespace Rigidity.Proofs.S6

variable {d : ℕ} {ω : Configuration d} {V : Finset (Vertex d)}

/-- The parity `f ↦ f(a) + f(b) mod 2` on `ℤ^V`. -/
noncomputable def gadgetParity (V : Finset (Vertex d)) (a b : V) : (V → ℤ) →+ ZMod 2 :=
  AddMonoidHom.mk' (fun f => ((f a + f b : ℤ) : ZMod 2)) fun f g => by
    simp only [Pi.add_apply]; push_cast; ring

theorem gadgetParity_apply (a b : V) (f : V → ℤ) :
    gadgetParity V a b f = ((f a + f b : ℤ) : ZMod 2) :=
  rfl

/-- For a gadget pair, the parity vanishes on `Δ_V ℤ^V`. -/
theorem gadgetParity_toppling {a b : V} (hab : IsGadgetPair ω a.val b.val) (h : V → ℤ) :
    gadgetParity V a b (toppling ω V h) = 0 := by
  obtain ⟨-, hda, hdb, hadj⟩ := hab
  have hS : (∑ y : V, if (openGraph ω).Adj b.val y.val then h y else 0) =
      ∑ y : V, if (openGraph ω).Adj a.val y.val then h y else 0 :=
    Finset.sum_congr rfl fun y _ => by simp only [hadj y.val]
  have hsum : toppling ω V h a + toppling ω V h b =
      2 * (h a + h b - ∑ y : V, if (openGraph ω).Adj a.val y.val then h y else 0) := by
    change ((openGraph ω).degree a.val : ℤ) * h a - _ +
      (((openGraph ω).degree b.val : ℤ) * h b - _) = _
    rw [hda, hdb, hS]
    push_cast
    ring
  rw [gadgetParity_apply, hsum, Int.cast_mul, Int.cast_ofNat,
    show (2 : ZMod 2) = 0 by decide, zero_mul]

/-- The parity of a gadget pair, on the sandpile group. -/
noncomputable def gadgetHom {a b : V} (hab : IsGadgetPair ω a.val b.val) :
    SandpileGroup ω V →+ ZMod 2 :=
  QuotientAddGroup.lift _ (gadgetParity V a b) (by
    rintro _ ⟨h, rfl⟩
    exact (AddMonoidHom.mem_ker).2 (gadgetParity_toppling hab h))

/-- The sign character `k ↦ (-1)^k` of `ZMod 2`. -/
noncomputable def signChar : AddChar (ZMod 2) ℂ :=
  AddChar.zmodChar 2 (ζ := (-1 : ℂ)) (by norm_num)

/-- The character `[f] ↦ (-1)^{f(a) + f(b)}` of a gadget pair. -/
noncomputable def gadgetCharacter {a b : V} (hab : IsGadgetPair ω a.val b.val) :
    AddChar (SandpileGroup ω V) ℂ :=
  signChar.compAddMonoidHom (gadgetHom hab)

theorem gadgetCharacter_chip {a b : V} (hab : IsGadgetPair ω a.val b.val) (x : V) :
    gadgetCharacter hab (chip ω V x) = if x = a ∨ x = b then -1 else 1 := by
  have hne : a ≠ b := fun h => hab.1 (congrArg Subtype.val h)
  simp only [gadgetCharacter, AddChar.compAddMonoidHom_apply, chip, gadgetHom,
    QuotientAddGroup.lift_mk, gadgetParity_apply, signChar, AddChar.zmodChar_apply,
    Pi.single_apply]
  by_cases hxa : x = a
  · subst hxa
    simp [Ne.symm hne]
    rw [show ZMod.val (1 : ZMod 2) = 1 from rfl, pow_one]
  · by_cases hxb : x = b
    · subst hxb
      simp [hne]
      rw [show ZMod.val (1 : ZMod 2) = 1 from rfl, pow_one]
    · simp [hxa, hxb, Ne.symm hxa, Ne.symm hxb]

theorem gadgetCharacter_chip_eq_neg_one {a b : V} (hab : IsGadgetPair ω a.val b.val) {x : V}
    (hx : gadgetCharacter hab (chip ω V x) = -1) : x = a ∨ x = b := by
  rw [gadgetCharacter_chip] at hx
  split_ifs at hx with h
  · exact h
  · norm_num at hx

theorem gadgetCharacter_ne_one {a b : V} (hab : IsGadgetPair ω a.val b.val) :
    gadgetCharacter hab ≠ 1 := by
  intro h
  have h1 := congrArg (fun χ : AddChar (SandpileGroup ω V) ℂ => χ (chip ω V a)) h
  simp only [gadgetCharacter_chip, true_or, if_true, AddChar.one_apply] at h1
  norm_num at h1

/-- The eigenvalue of the chain at the character of a gadget pair is `1 - 4/|V|`. -/
theorem chainEigenvalue_gadgetCharacter {a b : V} (hab : IsGadgetPair ω a.val b.val) :
    chainEigenvalue ω V (gadgetCharacter hab) = 1 - 4 / (V.card : ℂ) := by
  have hne : a ≠ b := fun h => hab.1 (congrArg Subtype.val h)
  have hx : ∀ x : V, gadgetCharacter hab (chip ω V x) =
      1 - (if x = a then 2 else 0) - (if x = b then 2 else 0) := by
    intro x
    rw [gadgetCharacter_chip]
    by_cases hxa : x = a
    · subst hxa; simp [hne]; norm_num
    · by_cases hxb : x = b
      · subst hxb; simp [hxa]; norm_num
      · simp [hxa, hxb]
  have hsum : ∑ x : V, gadgetCharacter hab (chip ω V x) = (V.card : ℂ) - 4 := by
    simp only [hx, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Fintype.card_coe, nsmul_eq_mul, mul_one]
    ring
  have hV : (V.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem a.property)
  rw [chainEigenvalue, hsum]
  field_simp

/-- step:6.5-gadget-characters: there are at least `|gadgetSites|/2` nontrivial characters with
eigenvalue `1 - 4/|V|`. -/
theorem gadgetCharacterStep {d : ℕ} : GadgetCharacterStep d := by
  intro ω V hfin
  have hmem : ∀ v ∈ gadgetSites ω V, v ∈ V ∧ ∃ b ∈ V, IsGadgetPair ω v b :=
    fun v hv => Finset.mem_filter.1 hv
  -- the character of a gadget site, with a chosen partner
  let F : Vertex d → AddChar (SandpileGroup ω V) ℂ := fun v =>
    if h : v ∈ V ∧ ∃ b ∈ V, IsGadgetPair ω v b then
      gadgetCharacter (a := ⟨v, h.1⟩) (b := ⟨h.2.choose, h.2.choose_spec.1⟩) h.2.choose_spec.2
    else 1
  have hF : ∀ v (h : v ∈ V ∧ ∃ b ∈ V, IsGadgetPair ω v b), F v =
      gadgetCharacter (a := ⟨v, h.1⟩) (b := ⟨h.2.choose, h.2.choose_spec.1⟩)
        h.2.choose_spec.2 :=
    fun v h => dif_pos h
  have himage : (((gadgetSites ω V).image F : Finset _) : Set _) ⊆ gadgetCharacters ω V := by
    intro χ hχ
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hχ)
    rw [hF v (hmem v hv)]
    exact ⟨gadgetCharacter_ne_one _, chainEigenvalue_gadgetCharacter _⟩
  have hfiber : ∀ χ ∈ (gadgetSites ω V).image F,
      ((gadgetSites ω V).filter fun v => F v = χ).card ≤ 2 := by
    intro χ hχ
    obtain ⟨v₀, hv₀, rfl⟩ := Finset.mem_image.1 hχ
    have h₀ := hmem v₀ hv₀
    refine (Finset.card_le_card (t := {v₀, h₀.2.choose}) fun v hv => ?_).trans
      Finset.card_le_two
    obtain ⟨hv, hFv⟩ := Finset.mem_filter.1 hv
    have h1 : F v (chip ω V ⟨v, (hmem v hv).1⟩) = -1 := by
      rw [hF v (hmem v hv), gadgetCharacter_chip, if_pos (Or.inl rfl)]
    rw [hFv, hF v₀ h₀] at h1
    rcases gadgetCharacter_chip_eq_neg_one _ h1 with h | h
    · exact Finset.mem_insert.2 (Or.inl (congrArg Subtype.val h))
    · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2 (congrArg Subtype.val h)))
  calc (gadgetSites ω V).card ≤ 2 * ((gadgetSites ω V).image F).card :=
        Finset.card_le_mul_card_image _ 2 hfiber
    _ ≤ 2 * Nat.card (gadgetCharacters ω V) := by
        rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
        exact Nat.mul_le_mul_left 2 (Set.ncard_le_ncard himage (Set.toFinite _))

end Rigidity.Proofs.S6
