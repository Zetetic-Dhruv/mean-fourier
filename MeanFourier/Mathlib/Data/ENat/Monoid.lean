module

public import Mathlib.Data.ENat.Monoid

public section

namespace ENat
variable {a b n : ℕ∞}

lemma mul_eq_top : a * b = ⊤ ↔ a ≠ 0 ∧ b = ⊤ ∨ a = ⊤ ∧ b ≠ 0 := WithTop.mul_eq_top_iff

@[simp] lemma le_toNat_self_iff : n ≤ n.toNat ↔ n ≠ ⊤ where
  mp := by rintro hn rfl; simp at hn
  mpr hn := by rw [natCast_toNat hn]

end ENat
