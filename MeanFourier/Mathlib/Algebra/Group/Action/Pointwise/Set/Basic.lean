module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

open scoped Pointwise

public section

namespace Set
variable {G X : Type*} [Group G] [MulAction G X] {s : Set G} {t : Set X} {x : X}

@[to_additive]
lemma mem_smul_iff_inv_smul_mem : x ∈ s • t ↔ ∃ a ∈ s, a⁻¹ • x ∈ t where
  mp := by rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, ha, by rwa [inv_smul_smul]⟩
  mpr := by rintro ⟨a, ha, hb⟩; exact ⟨a, ha, a⁻¹ • x, hb, smul_inv_smul ..⟩

end Set
