/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Set.Basic
public import MeanFourier.Mathlib.Data.Set.Basic
public import MeanFourier.Mathlib.Data.Set.Card

import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Simproc.ExistsAndEq
import Mathlib.Order.Lattice.Nat

/-!
# VC dimension

This file defines the VC dimension of set families.
-/

open Real

public section

variable {α : Type*}

section SemilatticeInf
variable [SemilatticeInf α] {𝒜 ℬ : Set α} {A B : α}

/-- A set family `𝒜` shatters a set `A` if all subsets of `A` can be obtained as the intersection
of `A` with some element of the set family. We also say that `A` is *traced* by `𝒜`. -/
@[expose]
def Shatters (𝒜 : Set α) (A : α) : Prop := ∀ ⦃B⦄, B ≤ A → ∃ C ∈ 𝒜, A ⊓ C = B

@[gcongr]
lemma Shatters.mono (h : 𝒜 ⊆ ℬ) (h𝒜 : Shatters 𝒜 A) : Shatters ℬ A :=
  fun _B hBA ↦ let ⟨C, hC, hCB⟩ := h𝒜 hBA; ⟨C, h hC, hCB⟩

@[gcongr]
lemma Shatters.anti (h : A ≤ B) (hB : Shatters 𝒜 B) : Shatters 𝒜 A := fun C hCA ↦ by
  obtain ⟨D, hD, rfl⟩ := hB (hCA.trans h); exact ⟨D, hD, inf_congr_right hCA <| inf_le_of_left_le h⟩

lemma Shatters.exists_ge (h : Shatters 𝒜 A) : ∃ B ∈ 𝒜, A ≤ B := by simpa using h le_rfl

lemma Shatters.of_forall_le (h : ∀ B ≤ A, B ∈ 𝒜) : Shatters 𝒜 A :=
  fun B hBA ↦ ⟨B, h _ hBA, inf_eq_right.2 hBA⟩

protected lemma Shatters.nonempty (h : Shatters 𝒜 A) : 𝒜.Nonempty :=
  let ⟨B, hB, _⟩ := h le_rfl; ⟨B, hB⟩

protected lemma Shatters.le_iff (h : Shatters 𝒜 A) : B ≤ A ↔ ∃ C ∈ 𝒜, A ⊓ C = B :=
  ⟨fun ht ↦ h ht, by rintro ⟨u, _, rfl⟩; exact inf_le_left⟩

lemma shatters_iff_image_inf_eq_Iic : Shatters 𝒜 A ↔ (A ⊓ ·) '' 𝒜 = .Iic A := by
  aesop (add simp [Set.ext_iff, Shatters])

protected lemma Shatters.univ : Shatters .univ A := .of_forall_le <| by simp

@[simp] lemma shatters_bot [OrderBot α] : Shatters 𝒜 ⊥ ↔ 𝒜.Nonempty :=
  ⟨Shatters.nonempty, fun ⟨A, hA⟩ B hB ↦ ⟨A, hA, by simpa [eq_comm] using hB⟩⟩

@[simp] lemma shatters_top [OrderTop α] : Shatters 𝒜 ⊤ ↔ 𝒜 = .univ := by
  simp [shatters_iff_image_inf_eq_Iic]

end SemilatticeInf

section BooleanAlgebra
variable [BooleanAlgebra α] {𝒜 : Set α} {A : α}

lemma Shatters.preimage_compl (hA : Shatters 𝒜 A) : Shatters ((·ᶜ) ⁻¹' 𝒜) A := by
  rintro B hBA
  obtain ⟨C, hC, hABC⟩ : ∃ C ∈ 𝒜, A ⊓ C = A \ B := hA sdiff_le
  exact ⟨Cᶜ, by simpa, by simpa [← sdiff_eq, hBA] using congr(A \ $hABC)⟩

@[simp] lemma shatters_preimage_compl : Shatters ((·ᶜ) ⁻¹' 𝒜) A ↔ Shatters 𝒜 A where
  mp hA := by simpa [Set.preimage_preimage] using hA.preimage_compl
  mpr := .preimage_compl

@[simp] lemma shatters_image_compl : Shatters ((·ᶜ) '' 𝒜) A ↔ Shatters 𝒜 A := by
  simp [← Set.preimage_compl_eq_image_compl]

alias ⟨_, Shatters.image_compl⟩ := shatters_image_compl

end BooleanAlgebra

section Finset
variable [DecidableEq α] {𝒜 ℬ : Finset (Finset α)}

instance : DecidablePred (Shatters (𝒜 : Set (Finset α))) :=
  fun _s ↦ Finset.decidableForallOfDecidableSubsets

end Finset

section Set
variable {m n d d₁ d₂ : ℕ} {𝒜 ℬ : Set (Set α)} {A B : Set α} {x : α}

@[gcongr]
lemma Shatters.subset (h : A ⊆ B) (hB : Shatters 𝒜 B) : Shatters 𝒜 A := hB.anti h

/-- `Shatters` read at `Set α`, where `⊓` is `∩` and `≤` is `⊆`: every subset of `A` is the
intersection of `A` with a member of `𝒜`. Definitionally the same statement, stated in the
shape every use site wants, so that consumers obtain an `∩`-typed equation directly. -/
lemma Shatters.exists_inter_eq (h : Shatters 𝒜 A) (hB : B ⊆ A) : ∃ C ∈ 𝒜, A ∩ C = B := h hB

/-- `Shatters` read at `Set α`, as an introduction rule; the `∩`-shaped companion of
`Shatters.of_forall_le`. -/
lemma Shatters.of_forall_subset (h : ∀ ⦃B⦄, B ⊆ A → ∃ C ∈ 𝒜, A ∩ C = B) : Shatters 𝒜 A := h

/-- `𝒜` shatters the singleton `{x}` exactly when some member of `𝒜` contains `x` and some
member of `𝒜` misses it. -/
@[simp] lemma shatters_singleton : Shatters 𝒜 {x} ↔ (∃ C ∈ 𝒜, x ∉ C) ∧ ∃ C ∈ 𝒜, x ∈ C := by
  simp [Shatters, -Set.subset_singleton_iff, Set.subset_singleton_iff_eq]

open scoped Finset

lemma shatters_iff_le_ncard_image_inter (hA : A.Finite) :
    Shatters 𝒜 A ↔ 2 ^ A.ncard ≤ ((A ∩ ·) '' 𝒜).ncard := by
  sorry

variable (n 𝒜) in
/-- The growth of a set family is the maximum number of sets it cuts out from any set of size at
most `n`. -/
noncomputable def vcGrowth : ℕ :=
  ⨆ A : {A : Set α // A.Finite ∧ A.ncard ≤ n}, ((↑A ∩ ·) '' 𝒜).ncard

private lemma bddAbove_range :
    BddAbove (.range fun A : {A : Set α // A.Finite ∧ A.ncard ≤ n} ↦ ((↑A ∩ ·) '' 𝒜).ncard) := by
  use 2 ^ n
  simp only [mem_upperBounds, Set.mem_range, Subtype.exists, exists_prop, forall_exists_index,
    and_imp, forall_comm (α := ℕ), forall_apply_eq_imp_iff₂]
  rintro A hA hAn
  grw [← hAn, ← Set.ncard_powerset _ hA]
  · gcongr
    · exact hA.powerset
    · grind
  · norm_num

private lemma finite_image_inter (hA : A.Finite) : ((A ∩ ·) '' 𝒜).Finite :=
  hA.powerset.subset (by grind)

lemma vcGrowth_le_iff {d : ℕ} :
    vcGrowth n 𝒜 ≤ d ↔ ∀ ⦃A : Set α⦄, A.Finite → A.ncard ≤ n → ((A ∩ ·) '' 𝒜).ncard ≤ d := by
  simp [vcGrowth, ciSup_le_iff' bddAbove_range]

lemma vcGrowth_lt_iff {d : ℕ} :
    vcGrowth n 𝒜 < d ↔ ∀ ⦃A : Set α⦄, A.Finite → A.ncard ≤ n → ((A ∩ ·) '' 𝒜).ncard < d := by
  obtain _ | d := d
  · simp only [not_lt_zero, imp_false, not_le, false_iff, not_forall, not_lt]
    exact ⟨∅, by simp⟩
  · simp [vcGrowth_le_iff]

lemma ncard_image_inter_le_vcGrowth (hA : A.Finite) (hAn : A.ncard ≤ n) :
    ((A ∩ ·) '' 𝒜).ncard ≤ vcGrowth n 𝒜 := vcGrowth_le_iff.1 le_rfl hA hAn

@[gcongr]
lemma vcGrowth_mono (h𝒜ℬ : 𝒜 ⊆ ℬ) (hmn : m ≤ n) : vcGrowth m 𝒜 ≤ vcGrowth n ℬ := by
  grw [vcGrowth_le_iff, h𝒜ℬ, hmn, ← vcGrowth_le_iff]; exact finite_image_inter ‹_›

lemma vcGrowth_union_le : vcGrowth n (𝒜 ∪ ℬ) ≤ vcGrowth n 𝒜 + vcGrowth n ℬ := by
  rw [vcGrowth_le_iff]
  rintro A hA hAn
  grw [Set.image_union, Set.ncard_union_le, ncard_image_inter_le_vcGrowth hA hAn,
    ncard_image_inter_le_vcGrowth hA hAn]

lemma vcGrowth_image2_inter_le :
    vcGrowth n (.image2 (· ∩ ·) 𝒜 ℬ) ≤ vcGrowth n 𝒜 * vcGrowth n ℬ := by
  rw [vcGrowth_le_iff]
  rintro A hA hAn
  grw [Set.image_image2_distrib (Set.inter_inter_distrib_left _), Set.ncard_image2_le,
    ncard_image_inter_le_vcGrowth hA hAn, ncard_image_inter_le_vcGrowth hA hAn] <;>
      exact finite_image_inter hA

/-- A set family `𝒜` has VC dimension at most `d` if all the sets it shatters have size at most
`d`. -/
@[expose]
def HasVCDimLE (d : ℕ) (𝒜 : Set (Set α)) : Prop :=
  ∀ ⦃A : Set α⦄, A.Finite → Shatters 𝒜 A → A.ncard ≤ d

@[gcongr]
lemma HasVCDimLE.anti (hℬ𝒜 : ℬ ⊆ 𝒜) (hd : HasVCDimLE d 𝒜) : HasVCDimLE d ℬ :=
  fun _A hA h𝒜A ↦ hd hA <| h𝒜A.mono hℬ𝒜

@[gcongr]
lemma HasVCDimLE.mono (hd : d₁ ≤ d₂) : HasVCDimLE d₁ 𝒜 → HasVCDimLE d₂ 𝒜 := by
  grw [HasVCDimLE, HasVCDimLE, hd]; exact id

private lemma trace_sep_union {x : α} :
    (A ∩ ·) '' {C ∈ 𝒜 | x ∉ C} ∪ (A ∩ ·) '' {C ∈ 𝒜 | x ∈ C} = (A ∩ ·) '' 𝒜 := by
  rw [← Set.image_union]; congr 1; ext C; grind

private lemma trace_sep_disjoint {x : α} (hxA : x ∈ A) :
    Disjoint ((A ∩ ·) '' {C ∈ 𝒜 | x ∉ C}) ((A ∩ ·) '' {C ∈ 𝒜 | x ∈ C}) := by
  rw [Set.disjoint_left]
  rintro t ⟨C, hC, rfl⟩ ⟨C', hC', htC⟩
  exact hC.2 ((Set.ext_iff.1 htC x).1 ⟨hxA, hC'.2⟩).2

/-- A family whose members all avoid `x` shatters only sets avoiding `x`. -/
private lemma notMem_of_forall_notMem {x : α} (h𝒜 : ∀ C ∈ 𝒜, x ∉ C) (hB : Shatters 𝒜 B) :
    x ∉ B :=
  let ⟨C, hC, hBC⟩ := hB.exists_ge; fun hxB ↦ h𝒜 C hC (hBC hxB)

private lemma notMem_of_shatters_sep_left {x : α} (h : Shatters {C ∈ 𝒜 | x ∉ C} B) : x ∉ B :=
  notMem_of_forall_notMem (fun _C hC ↦ hC.2) h

private lemma notMem_of_shatters_sep_right {x : α} (h : Shatters {C ∈ 𝒜 | x ∈ C} B) : x ∉ B :=
  notMem_of_forall_notMem (𝒜 := (·ᶜ) ⁻¹' {C ∈ 𝒜 | x ∈ C}) (fun _C hC ↦ fun hx ↦ hC.2 hx)
    h.preimage_compl

/-- If `B` is shattered both by the members of `𝒜` avoiding `x` and by the members of `𝒜`
containing `x`, then `𝒜` shatters `insert x B`. This is the exchange step in the proof of
Pajor's inequality. -/
lemma Shatters.insert {x : α} (h₀ : Shatters {C ∈ 𝒜 | x ∉ C} B)
    (h₁ : Shatters {C ∈ 𝒜 | x ∈ C} B) : Shatters 𝒜 (insert x B) :=
  Shatters.of_forall_subset fun B' hB' ↦ by
    by_cases hxB' : x ∈ B'
    · obtain ⟨C, hC, hBC⟩ := h₁.exists_inter_eq
        (show B' \ {x} ⊆ B from fun y hy ↦ (hB' hy.1).resolve_left hy.2)
      exact ⟨C, hC.1, by rw [Set.insert_inter_of_mem hC.2, hBC, Set.insert_sdiff_singleton,
        Set.insert_eq_of_mem hxB']⟩
    · obtain ⟨C, hC, hBC⟩ := h₀.exists_inter_eq
        (show B' ⊆ B from fun y hy ↦ (hB' hy).resolve_left fun (e : y = x) ↦ hxB' (e ▸ hy))
      exact ⟨C, hC.1, by rw [Set.insert_inter_of_notMem hC.2, hBC]⟩

/-- A point of `A` witnessing that one trace fails to contain another is a point at which `𝒜`
splits. -/
private lemma exists_splitter_of_not_subset {C C' : Set α} (hC : C ∈ 𝒜) (hC' : C' ∈ 𝒜)
    (h : ¬A ∩ C ⊆ A ∩ C') : ∃ x ∈ A, (∃ D ∈ 𝒜, x ∈ D) ∧ ∃ D ∈ 𝒜, x ∉ D := by
  obtain ⟨y, ⟨hyA, hyC⟩, hy'⟩ := Set.not_subset.1 h
  exact ⟨y, hyA, ⟨C, hC, hyC⟩, C', hC', fun hc ↦ hy' ⟨hyA, hc⟩⟩

private lemma exists_splitter (h : ((A ∩ ·) '' 𝒜).Nontrivial) :
    ∃ x ∈ A, (∃ C ∈ 𝒜, x ∈ C) ∧ ∃ C ∈ 𝒜, x ∉ C := by
  obtain ⟨t₁, ⟨C₁, hC₁, rfl⟩, t₂, ⟨C₂, hC₂, rfl⟩, hne⟩ := h
  obtain h' | h' : ¬A ∩ C₁ ⊆ A ∩ C₂ ∨ ¬A ∩ C₂ ⊆ A ∩ C₁ := by grind [Set.Subset.antisymm]
  exacts [exists_splitter_of_not_subset hC₁ hC₂ h', exists_splitter_of_not_subset hC₂ hC₁ h']

/-- Inserting a fixed element is injective on the sets avoiding it: the element can be removed
again, recovering the argument. -/
private lemma insert_injOn_notMem (x : α) : Set.InjOn (insert x) {B : Set α | x ∉ B} :=
  fun _B hB _B' hB' h ↦ by
    rw [← Set.insert_sdiff_self_of_notMem hB, h, Set.insert_sdiff_self_of_notMem hB']

/-- A family whose members all avoid `x` is disjoint from any family of sets containing `x`. -/
private lemma disjoint_image_insert {x : α} {𝒮 𝒯 : Set (Set α)} (h𝒮 : ∀ B ∈ 𝒮, x ∉ B) :
    Disjoint 𝒮 (insert x '' 𝒯) := by
  rw [Set.disjoint_left]
  rintro B hB ⟨B', -, rfl⟩
  exact h𝒮 _ hB (Set.mem_insert x B')

private lemma pajor_encard_aux :
    ∀ N (𝒜 : Set (Set α)), ((A ∩ ·) '' 𝒜).Finite → ((A ∩ ·) '' 𝒜).ncard ≤ N →
      ((A ∩ ·) '' 𝒜).encard ≤ {B | B ⊆ A ∧ Shatters 𝒜 B}.encard := by
  intro N
  induction N with
  | zero =>
    intro 𝒜 hfin hN
    rw [(Set.ncard_eq_zero hfin).1 (Nat.le_zero.1 hN), Set.encard_empty]
    exact zero_le
  | succ N ih =>
    intro 𝒜 hfin hN
    obtain hsub | hnt := Set.subsingleton_or_nontrivial ((A ∩ ·) '' 𝒜)
    · obtain hemp | ⟨t, ht⟩ := ((A ∩ ·) '' 𝒜).eq_empty_or_nonempty
      · rw [hemp, Set.encard_empty]
        exact zero_le
      · obtain ⟨C, hC, -⟩ := id ht
        rw [Set.eq_singleton_iff_unique_mem.2 ⟨ht, fun _ ht' ↦ hsub ht' ht⟩, Set.encard_singleton]
        exact Set.one_le_encard_iff_nonempty.2 ⟨∅, Set.empty_subset A, shatters_bot.2 ⟨C, hC⟩⟩
    · obtain ⟨x, hxA, ⟨C₁, hC₁, hxC₁⟩, C₂, hC₂, hxC₂⟩ := exists_splitter hnt
      have hfin₀ : ((A ∩ ·) '' {C ∈ 𝒜 | x ∉ C}).Finite :=
        hfin.subset (Set.image_mono (Set.sep_subset _ _))
      have hfin₁ : ((A ∩ ·) '' {C ∈ 𝒜 | x ∈ C}).Finite :=
        hfin.subset (Set.image_mono (Set.sep_subset _ _))
      have hpos₀ : 0 < ((A ∩ ·) '' {C ∈ 𝒜 | x ∉ C}).ncard :=
        (Set.ncard_pos hfin₀).2 ⟨A ∩ C₂, C₂, ⟨hC₂, hxC₂⟩, rfl⟩
      have hpos₁ : 0 < ((A ∩ ·) '' {C ∈ 𝒜 | x ∈ C}).ncard :=
        (Set.ncard_pos hfin₁).2 ⟨A ∩ C₁, C₁, ⟨hC₁, hxC₁⟩, rfl⟩
      rw [← trace_sep_union (x := x), Set.ncard_union_eq (trace_sep_disjoint hxA) hfin₀ hfin₁]
        at hN
      set 𝒮₀ := {B | B ⊆ A ∧ Shatters {C ∈ 𝒜 | x ∉ C} B}
      set 𝒮₁ := {B | B ⊆ A ∧ Shatters {C ∈ 𝒜 | x ∈ C} B}
      calc ((A ∩ ·) '' 𝒜).encard
          = ((A ∩ ·) '' {C ∈ 𝒜 | x ∉ C}).encard + ((A ∩ ·) '' {C ∈ 𝒜 | x ∈ C}).encard := by
            rw [← trace_sep_union (x := x), Set.encard_union_eq (trace_sep_disjoint hxA)]
        _ ≤ 𝒮₀.encard + 𝒮₁.encard := add_le_add (ih _ hfin₀ (by lia)) (ih _ hfin₁ (by lia))
        _ = (𝒮₀ ∪ 𝒮₁).encard + (𝒮₀ ∩ 𝒮₁).encard :=
            (Set.encard_union_add_encard_inter 𝒮₀ 𝒮₁).symm
        _ = (𝒮₀ ∪ 𝒮₁).encard + (insert x '' (𝒮₀ ∩ 𝒮₁)).encard := by
            rw [((insert_injOn_notMem x).mono
              fun B hB ↦ notMem_of_shatters_sep_left hB.1.2).encard_image]
        _ = ((𝒮₀ ∪ 𝒮₁) ∪ insert x '' (𝒮₀ ∩ 𝒮₁)).encard :=
            (Set.encard_union_eq <| disjoint_image_insert <| by
              rintro B (⟨-, hB⟩ | ⟨-, hB⟩)
              exacts [notMem_of_shatters_sep_left hB, notMem_of_shatters_sep_right hB]).symm
        _ ≤ {B | B ⊆ A ∧ Shatters 𝒜 B}.encard := Set.encard_le_encard <| by
            rintro B ((⟨hBA, hB⟩ | ⟨hBA, hB⟩) | ⟨B', ⟨⟨hB'A, hB'₀⟩, -, hB'₁⟩, rfl⟩)
            · exact ⟨hBA, hB.mono (Set.sep_subset _ _)⟩
            · exact ⟨hBA, hB.mono (Set.sep_subset _ _)⟩
            · exact ⟨Set.insert_subset_iff.2 ⟨hxA, hB'A⟩, hB'₀.insert hB'₁⟩

variable (𝒜 A) in
/-- The elements of `A` at which `𝒜` splits: some member of `𝒜` contains them and some does
not. These are the elements whose singleton `𝒜` shatters. -/
private def splitPoints : Set α := {x ∈ A | (∃ C ∈ 𝒜, x ∉ C) ∧ ∃ C ∈ 𝒜, x ∈ C}

private lemma injOn_inter_splitPoints : Set.InjOn (· ∩ splitPoints 𝒜 A) ((A ∩ ·) '' 𝒜) := by
  rintro t ⟨C, hC, rfl⟩ t' ⟨C', hC', rfl⟩ hIt
  ext y
  by_cases hyD : y ∈ splitPoints 𝒜 A
  · exact ⟨fun hy ↦ ((Set.ext_iff.1 hIt y).1 ⟨hy, hyD⟩).1,
      fun hy ↦ ((Set.ext_iff.1 hIt y).2 ⟨hy, hyD⟩).1⟩
  · exact ⟨fun ⟨hyA, hyC⟩ ↦ ⟨hyA, by_contra fun hyC' ↦ hyD ⟨hyA, ⟨C', hC', hyC'⟩, C, hC, hyC⟩⟩,
      fun ⟨hyA, hyC'⟩ ↦ ⟨hyA, by_contra fun hyC ↦ hyD ⟨hyA, ⟨C, hC, hyC⟩, C', hC', hyC'⟩⟩⟩

private lemma finite_image_inter_of_finite_splitPoints (h : (splitPoints 𝒜 A).Finite) :
    ((A ∩ ·) '' 𝒜).Finite :=
  Set.Finite.of_finite_image
    (h.finite_subsets.subset <| by rintro _ ⟨t, -, rfl⟩; exact Set.inter_subset_right)
    injOn_inter_splitPoints

private lemma singleton_image_splitPoints_subset :
    (fun x ↦ ({x} : Set α)) '' splitPoints 𝒜 A ⊆ {B | B ⊆ A ∧ Shatters 𝒜 B} := by
  rintro _ ⟨x, ⟨hxA, hxout, hxin⟩, rfl⟩
  exact ⟨Set.singleton_subset_iff.2 hxA, shatters_singleton.2 ⟨hxout, hxin⟩⟩

/-- A family with infinitely many traces on `A` shatters infinitely many subsets of `A`, over
any `α` and for any `𝒜`. -/
lemma infinite_setOf_shatters (h : ((A ∩ ·) '' 𝒜).Infinite) :
    {B | B ⊆ A ∧ Shatters 𝒜 B}.Infinite :=
  Set.Infinite.mono singleton_image_splitPoints_subset <|
    Set.Infinite.image Set.singleton_injective.injOn fun hfin ↦
      h (finite_image_inter_of_finite_splitPoints hfin)

/-- The points of `A` at which `𝒜` splits are exactly those whose singleton `𝒜` shatters. -/
private lemma splitPoints_eq_setOf_shatters_singleton :
    splitPoints 𝒜 A = {x ∈ A | Shatters 𝒜 {x}} := by
  ext x; simp only [splitPoints, Set.mem_ofPred_eq, shatters_singleton]

/-- A trace is determined by its restriction to the points whose singleton is shattered, so the
traces on `A` number at most `2 ^ k` with `k` the number of such points. No hypothesis on `𝒜`. -/
lemma ncard_image_inter_le_two_pow_ncard_shatters_singleton
    (h : {x ∈ A | Shatters 𝒜 {x}}.Finite) :
    ((A ∩ ·) '' 𝒜).ncard ≤ 2 ^ {x ∈ A | Shatters 𝒜 {x}}.ncard := by
  rw [← Set.ncard_powerset _ h]
  refine Set.ncard_le_ncard_of_injOn (· ∩ {x ∈ A | Shatters 𝒜 {x}})
    (fun t _ ↦ Set.inter_subset_right) ?_ (h.powerset)
  rw [← splitPoints_eq_setOf_shatters_singleton]
  exact injOn_inter_splitPoints

/-- The subsets of `A` shattered by `𝒜` grow with `𝒜`. -/
lemma setOf_shatters_mono (h : 𝒜 ⊆ ℬ) :
    {B | B ⊆ A ∧ Shatters 𝒜 B} ⊆ {B | B ⊆ A ∧ Shatters ℬ B} :=
  fun _B hB ↦ ⟨hB.1, hB.2.mono h⟩

/-- **Pajor's inequality**: the traces of `𝒜` on `A` are at most
as many as the subsets of `A` shattered by `𝒜`. -/
lemma encard_image_inter_le_encard_shatters :
    ((A ∩ ·) '' 𝒜).encard ≤ {B | B ⊆ A ∧ Shatters 𝒜 B}.encard := by
  by_cases h : ((A ∩ ·) '' 𝒜).Finite
  · exact pajor_encard_aux _ 𝒜 h le_rfl
  · rw [(infinite_setOf_shatters h).encard_eq]
    exact le_top

/-- The traces of `𝒜` on `A` that are determined by finitely many points are at most as many as
the shattered subsets -/
lemma encard_determined_le_encard_shatters :
    {t ∈ (A ∩ ·) '' 𝒜 | ∃ F : Set α, F.Finite ∧
      ∀ t' ∈ (A ∩ ·) '' 𝒜, t' ∩ F = t ∩ F → t' = t}.encard ≤
      {B | B ⊆ A ∧ Shatters 𝒜 B}.encard :=
  (Set.encard_le_encard (Set.sep_subset _ _)).trans encard_image_inter_le_encard_shatters

lemma finite_setOf_subset_and (hA : A.Finite) (p : Set α → Prop) :
    {B | B ⊆ A ∧ p B}.Finite := hA.finite_subsets.subset fun _B hB ↦ hB.1

/-- The finite form of **Pajor's inequality**. -/
lemma ncard_image_inter_le_ncard_shatters (hA : A.Finite) :
    ((A ∩ ·) '' 𝒜).ncard ≤ {B | B ⊆ A ∧ Shatters 𝒜 B}.ncard :=
  (Set.encard_le_coe_iff_finite_ncard_le.1 <| encard_image_inter_le_encard_shatters.trans_eq
    (finite_setOf_subset_and hA _).cast_ncard_eq.symm).2

/-- A family of VC dimension at most `d` shatters no infinite set, over any `α` and for any
`𝒜`. -/
lemma HasVCDimLE.finite_of_shatters (h𝒜 : HasVCDimLE d 𝒜) (hB : Shatters 𝒜 B) : B.Finite := by
  by_contra hinf
  obtain ⟨B', hB'B, hB'fin, hB'card⟩ := Set.Infinite.exists_subset_ncard_eq hinf (d + 1)
  exact absurd (h𝒜 hB'fin (hB.subset hB'B)) (by lia)

/-- A family of VC dimension at most `d` shatters only sets of size at most `d` -/
lemma HasVCDimLE.ncard_le_of_shatters (h𝒜 : HasVCDimLE d 𝒜) (hB : Shatters 𝒜 B) :
    B.ncard ≤ d := h𝒜 (h𝒜.finite_of_shatters hB) hB

-- the `A.Finite` in `HasVCDimLE` looks redundant now: it only constrains sets already known
-- finite, but `finite_of_shatters` says nothing infinite is shattered anyway, so `HasVCDimLE d 𝒜`
-- should be equivalent to `∀ A, Shatters 𝒜 A → A.ncard ≤ d`.

private lemma setOf_subset_and_ncard_le_zero (hA : A.Finite) :
    {B | B ⊆ A ∧ B.ncard ≤ 0} = {∅} := by
  ext B; simp +contextual [and_or_left, and_iff_right_of_imp, hA.subset]

variable (A d) in
private lemma setOf_subset_and_ncard_le_succ :
    {B | B ⊆ A ∧ B.ncard ≤ d + 1} = {B | B ⊆ A ∧ B.ncard ≤ d} ∪ {B ⊆ A | B.ncard = d + 1} := by
  ext B; simp only [Set.mem_ofPred_eq, Set.mem_union]; lia

variable (A d) in
private lemma disjoint_setOf_ncard_le_setOf_ncard_eq :
    Disjoint {B | B ⊆ A ∧ B.ncard ≤ d} {B ⊆ A | B.ncard = d + 1} := by
  rw [Set.disjoint_left]; rintro _B ⟨-, hle⟩ ⟨-, heq⟩; lia

lemma ncard_setOf_ncard_le (hA : A.Finite) (d : ℕ) :
    {B | B ⊆ A ∧ B.ncard ≤ d}.ncard = ∑ k ∈ .Iic d, A.ncard.choose k := by
  induction d with
  | zero =>
    rw [setOf_subset_and_ncard_le_zero hA, Set.ncard_singleton, ← Nat.range_succ_eq_Iic,
      Finset.sum_range_one, Nat.choose_zero_right]
  | succ d ihd =>
    rw [setOf_subset_and_ncard_le_succ,
      Set.ncard_union_eq (disjoint_setOf_ncard_le_setOf_ncard_eq ..)
        (finite_setOf_subset_and hA _) (finite_setOf_subset_and hA _), ihd,
      Set.ncard_powerset_ncard hA, ← Nat.range_succ_eq_Iic, ← Nat.range_succ_eq_Iic]
    exact (Finset.sum_range_succ _ _).symm

/-- The Sauer-Shelah count, from a bound on the shattered subsets of `A` alone. -/
private lemma ncard_image_inter_le_of_forall_ncard_le (hA : A.Finite) (hAn : A.ncard ≤ n)
    (h : ∀ B ⊆ A, Shatters 𝒜 B → B.ncard ≤ d) :
    ((A ∩ ·) '' 𝒜).ncard ≤ ∑ k ∈ .Iic d, n.choose k :=
  calc ((A ∩ ·) '' 𝒜).ncard
      ≤ {B | B ⊆ A ∧ Shatters 𝒜 B}.ncard := ncard_image_inter_le_ncard_shatters hA
    _ ≤ {B | B ⊆ A ∧ B.ncard ≤ d}.ncard :=
        Set.ncard_le_ncard (fun _B hB ↦ ⟨hB.1, h _ hB.1 hB.2⟩) (finite_setOf_subset_and hA _)
    _ = ∑ k ∈ .Iic d, A.ncard.choose k := ncard_setOf_ncard_le hA d
    _ ≤ ∑ k ∈ .Iic d, n.choose k := Finset.sum_le_sum fun k _ ↦ Nat.choose_le_choose k hAn

/-- **The Sauer-Shelah inequality**: a family of VC dimension at most `d` traces at most
`∑ k ≤ d, n.choose k` sets on any finite set of size at most `n`. -/
lemma HasVCDimLE.ncard_image_inter_le (h𝒜 : HasVCDimLE d 𝒜) (hA : A.Finite)
    (hAn : A.ncard ≤ n) :
    ((A ∩ ·) '' 𝒜).ncard ≤ ∑ k ∈ .Iic d, n.choose k :=
  ncard_image_inter_le_of_forall_ncard_le hA hAn fun _B _ hB ↦ h𝒜.ncard_le_of_shatters hB

/-- The extraction form of the Sauer-Shelah inequality: a family tracing more than
`∑ k ≤ d, n.choose k` sets on a finite `A` of size at most `n` shatters a subset of `A` of size
greater than `d`. -/
lemma exists_shatters_of_lt_ncard_image_inter (hA : A.Finite) (hAn : A.ncard ≤ n)
    (h : ∑ k ∈ .Iic d, n.choose k < ((A ∩ ·) '' 𝒜).ncard) :
    ∃ B ⊆ A, d < B.ncard ∧ Shatters 𝒜 B := by
  by_contra hc
  push Not at hc
  exact absurd h (not_lt.2 (ncard_image_inter_le_of_forall_ncard_le hA hAn
    fun _B hBA hB ↦ not_lt.1 fun hlt ↦ hc _ hBA hlt hB))

/-- `HasVCDimLE.ncard_image_inter_le` read off every finite set of size at most `n` at once:
the growth function of a family of VC dimension at most `d` is at most `∑ k ≤ d, n.choose k`. -/
lemma HasVCDimLE.vcGrowth_le (h𝒜 : HasVCDimLE d 𝒜) :
    vcGrowth n 𝒜 ≤ ∑ k ∈ .Iic d, n.choose k :=
  vcGrowth_le_iff.2 fun _A hA hAn ↦ h𝒜.ncard_image_inter_le hA hAn

/-- `HasVCDimLE.vcGrowth_le` with the sum indexed by `Finset.range (d + 1)` in place of
`Finset.Iic d` -/
private lemma HasVCDimLE.vcGrowth_le_sum_range (h𝒜 : HasVCDimLE d 𝒜) :
    vcGrowth n 𝒜 ≤ ∑ k ∈ Finset.range (d + 1), n.choose k := by
  rw [Nat.range_succ_eq_Iic]; exact h𝒜.vcGrowth_le

private lemma sum_choose_mul_pow_le_add_one_pow {t : ℝ} (ht : 0 ≤ t) (hdm : d ≤ m) :
    ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * t ^ i ≤ (1 + t) ^ m := by
  rw [show (1 + t) ^ m = ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * t ^ i by
    rw [add_comm, add_pow t 1 m]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [one_pow, mul_one]; ring]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun i hi ↦ ?_) fun i _ _ ↦
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht _)
  simp only [Finset.mem_range] at hi ⊢
  exact Nat.lt_of_lt_of_le hi (Nat.succ_le_succ hdm)

private lemma one_add_div_pow_le_exp_pow (hm : (0 : ℝ) < m) :
    (1 + (d : ℝ) / m) ^ m ≤ exp 1 ^ d :=
  calc (1 + (d : ℝ) / m) ^ m ≤ (exp ((d : ℝ) / m)) ^ m := by
        gcongr; linarith [Real.add_one_le_exp ((d : ℝ) / m)]
    _ = exp (d : ℝ) := by rw [← Real.exp_nat_mul, mul_comm, div_mul_cancel₀ _ hm.ne']
    _ = exp 1 ^ d := by rw [← Real.exp_nat_mul]; simp

private lemma sum_choose_le_mul_sum_choose_mul_pow (hd : (0 : ℝ) < d) (hm : (0 : ℝ) < m)
    (hdm : (d : ℝ) ≤ m) :
    (∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ)) ≤
      ((m : ℝ) / d) ^ d * ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * ((d : ℝ) / m) ^ i := by
  rw [Finset.sum_congr rfl fun i _ ↦ show (m.choose i : ℝ)
      = (m.choose i : ℝ) * ((d : ℝ) / m) ^ i * ((m : ℝ) / d) ^ i by
    rw [mul_assoc, ← mul_pow, show (d : ℝ) / m * ((m : ℝ) / d) = 1 by field_simp, one_pow, mul_one]]
  calc ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * ((d : ℝ) / m) ^ i * ((m : ℝ) / d) ^ i
      ≤ ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * ((d : ℝ) / m) ^ i * ((m : ℝ) / d) ^ d :=
        Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left
          (pow_right_mono₀ ((le_div_iff₀ hd).mpr (by linarith))
            (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))) (by positivity)
    _ = ((m : ℝ) / d) ^ d * ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * ((d : ℝ) / m) ^ i := by
        rw [← Finset.sum_mul, mul_comm]

lemma sum_choose_le_exp_pow (d m : ℕ) (hd : 0 < d) (hdm : d ≤ m) :
    (∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ)) ≤ (exp 1 / d * m) ^ d :=
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le hd hdm)
  calc (∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ))
      ≤ ((m : ℝ) / d) ^ d * ∑ i ∈ Finset.range (d + 1), (m.choose i : ℝ) * ((d : ℝ) / m) ^ i :=
        sum_choose_le_mul_sum_choose_mul_pow (Nat.cast_pos.mpr hd) hm' (Nat.cast_le.mpr hdm)
    _ ≤ ((m : ℝ) / d) ^ d * (1 + (d : ℝ) / m) ^ m :=
        mul_le_mul_of_nonneg_left
          (sum_choose_mul_pow_le_add_one_pow (by positivity) hdm) (by positivity)
    _ ≤ ((m : ℝ) / d) ^ d * exp 1 ^ d :=
        mul_le_mul_of_nonneg_left (one_add_div_pow_le_exp_pow hm') (by positivity)
    _ = (exp 1 / d * m) ^ d := by rw [← mul_pow]; ring_nf

/-- The Sauer-Shelah bound: the growth function of a family of VC dimension at
most `d` is at most `(exp 1 / d * n) ^ d`, for `d ≤ n`. -/
lemma HasVCDimLE.vcGrowth_le_exp (h𝒜 : HasVCDimLE d 𝒜) (hdn : d ≤ n) :
    (vcGrowth n 𝒜 : ℝ) ≤ (exp 1 / d * n) ^ d := by
  obtain rfl | hd := Nat.eq_zero_or_pos d
  · rw [pow_zero]
    exact_mod_cast (h𝒜.vcGrowth_le_sum_range (n := n)).trans_eq (by simp)
  · calc (vcGrowth n 𝒜 : ℝ)
        ≤ ((∑ k ∈ Finset.range (d + 1), n.choose k : ℕ) : ℝ) :=
          Nat.cast_le.2 h𝒜.vcGrowth_le_sum_range
      _ = ∑ k ∈ Finset.range (d + 1), (n.choose k : ℝ) := by push_cast; rfl
      _ ≤ (exp 1 / d * n) ^ d := sum_choose_le_exp_pow d n hd hdn

variable [Infinite α]

lemma vcGrowth_le_iff' {d : ℕ} :
    vcGrowth n 𝒜 ≤ d ↔ ∀ ⦃A : Set α⦄, A.Finite → A.ncard = n → ((A ∩ ·) '' 𝒜).ncard ≤ d := by
  rw [vcGrowth_le_iff]
  constructor
  · rintro h A hA hAn
    exact h hA hAn.le
  · rintro h A hA hAn
    obtain ⟨B, hB, hAB, -, rfl⟩ := Set.exists_superset_ncard_eq hA hAn
    grw [← h hB rfl]
    simpa [Set.image_image, hAB, ← Set.inter_assoc]
      using Set.ncard_image_le (finite_image_inter hB) (f := (A ∩ ·))

lemma vcGrowth_lt_iff' {d : ℕ} :
    vcGrowth n 𝒜 < d ↔ ∀ ⦃A : Set α⦄, A.Finite → A.ncard = n → ((A ∩ ·) '' 𝒜).ncard < d := by
  obtain _ | d := d
  · simpa [not_lt_zero, imp_false, false_iff, not_forall, Classical.not_imp, Decidable.not_not]
      using Set.exists_ncard_eq α n
  · simp [vcGrowth_le_iff']

lemma hasVCDimLE_iff_vcGrowth : HasVCDimLE d 𝒜 ↔ vcGrowth (d + 1) 𝒜 < 2 ^ (d + 1) := by
  simp only [HasVCDimLE, vcGrowth_lt_iff']
  constructor
  · rintro h A hA hAd
    rw [← hAd]
    contrapose! h
    exact ⟨A, hA, (shatters_iff_le_ncard_image_inter hA).2 h, by lia⟩
  · rintro h A hA hA𝒜
    contrapose! h
    rw [← Nat.add_one_le_iff] at h
    obtain ⟨B, hBA, hB, hBd⟩ := Set.exists_subset_ncard_eq hA h
    refine ⟨B, hB, hBd, ?_⟩
    grw [← hBd, ← shatters_iff_le_ncard_image_inter hB, hBA]
    exact hA𝒜

end Set
