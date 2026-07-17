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

import Mathlib.Combinatorics.SetFamily.Shatter
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
variable {m n d d₁ d₂ : ℕ} {𝒜 ℬ : Set (Set α)} {A B : Set α}

@[gcongr]
lemma Shatters.subset (h : A ⊆ B) (hB : Shatters 𝒜 B) : Shatters 𝒜 A := hB.anti h

open scoped Finset

lemma shatters_iff_le_ncard_image_inter : Shatters 𝒜 A ↔ 2 ^ A.ncard ≤ ((A ∩ ·) '' 𝒜).ncard := by
  sorry
  -- this might need `A.Finite`? For infinite `A` we have `A.ncard = 0`, so the RHS only
  -- says the image is nonempty, but say `𝒜 = {∅}` does not shatter an infinite `A`.

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

/-!
# Sauer Shelah

This adds the vcGrowth bound for set families of finite VC dimension
-/

open scoped Classical in
private noncomputable def traceOf {A : Set α} (hA : A.Finite) (t : Set α) :
    Finset ↥hA.toFinset :=
  Finset.univ.filter fun x ↦ ↑x ∈ t

private lemma mem_traceOf {hA : A.Finite} {t : Set α} {x : ↥hA.toFinset} :
    x ∈ traceOf hA t ↔ ↑x ∈ t := by
  simp [traceOf]

open scoped Classical in
private noncomputable def traceFinset (𝒜 : Set (Set α)) (hA : A.Finite) :
    Finset (Finset ↥hA.toFinset) :=
  (finite_image_inter (𝒜 := 𝒜) hA).toFinset.image (traceOf hA)

private lemma mem_traceFinset {hA : A.Finite} {u : Finset ↥hA.toFinset} :
    u ∈ traceFinset 𝒜 hA ↔ ∃ C ∈ 𝒜, u = traceOf hA (A ∩ C) := by
  simp only [traceFinset, Finset.mem_image, Set.Finite.mem_toFinset, Set.mem_image]
  constructor
  · rintro ⟨t, ⟨C, hC, rfl⟩, rfl⟩
    exact ⟨C, hC, rfl⟩
  · rintro ⟨C, hC, rfl⟩
    exact ⟨A ∩ C, ⟨C, hC, rfl⟩, rfl⟩

private lemma card_traceFinset (𝒜 : Set (Set α)) (hA : A.Finite) :
    (traceFinset 𝒜 hA).card = ((A ∩ ·) '' 𝒜).ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card _ (finite_image_inter (𝒜 := 𝒜) hA), traceFinset]
  refine Finset.card_image_of_injOn fun t ht t' ht' h ↦ ?_
  rw [Finset.mem_coe, Set.Finite.mem_toFinset] at ht ht'
  obtain ⟨C, -, rfl⟩ := ht
  obtain ⟨C', -, rfl⟩ := ht'
  ext x
  constructor
  · intro hx
    have hx' := Finset.ext_iff.1 h ⟨x, hA.mem_toFinset.2 hx.1⟩
    simp only [mem_traceOf] at hx'
    exact hx'.1 hx
  · intro hx
    have hx' := Finset.ext_iff.1 h ⟨x, hA.mem_toFinset.2 hx.1⟩
    simp only [mem_traceOf] at hx'
    exact hx'.2 hx

open scoped Classical in
private lemma shatters_of_traceFinset_shatters {hA : A.Finite} {T : Finset ↥hA.toFinset}
    (hT : (traceFinset 𝒜 hA).Shatters T) :
    Shatters 𝒜 (Subtype.val '' (T : Set ↥hA.toFinset)) := by
  intro B hBV
  obtain ⟨u, hu, hTu⟩ := hT (Finset.filter_subset (fun x ↦ ↑x ∈ B) T)
  obtain ⟨C, hC, rfl⟩ := mem_traceFinset.1 hu
  refine ⟨C, hC, ?_⟩
  ext x
  simp only [Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨⟨y, hyT, rfl⟩, hxC⟩
    have hyu : y ∈ T ∩ traceOf hA (A ∩ C) :=
      Finset.mem_inter.2 ⟨hyT, mem_traceOf.2 ⟨hA.mem_toFinset.1 y.2, hxC⟩⟩
    rw [hTu] at hyu
    exact (Finset.mem_filter.1 hyu).2
  · intro hxB
    obtain ⟨y, hyT, rfl⟩ : ∃ y ∈ T, ↑y = x := by
      obtain ⟨y, hyT, hyx⟩ := hBV hxB
      exact ⟨y, Finset.mem_coe.1 hyT, hyx⟩
    have hyu : y ∈ T.filter fun z ↦ ↑z ∈ B := Finset.mem_filter.2 ⟨hyT, hxB⟩
    rw [← hTu] at hyu
    have hy := mem_traceOf.1 (Finset.mem_inter.1 hyu).2
    exact ⟨⟨y, hyT, rfl⟩, hy.2⟩

open scoped Classical in
private lemma vcDim_traceFinset_le (h𝒜 : HasVCDimLE d 𝒜) (hA : A.Finite) :
    (traceFinset 𝒜 hA).vcDim ≤ d := by
  apply Finset.sup_le
  intro T hT
  rw [Finset.mem_shatterer] at hT
  have h := h𝒜 (T.finite_toSet.image _) (shatters_of_traceFinset_shatters hT)
  rwa [Set.ncard_image_of_injective _ Subtype.val_injective, Set.ncard_coe_finset] at h

lemma HasVCDimLE.ncard_image_inter_le (h𝒜 : HasVCDimLE d 𝒜) (hA : A.Finite)
    (hAn : A.ncard ≤ n) :
    ((A ∩ ·) '' 𝒜).ncard ≤ ∑ k ∈ Finset.Iic d, n.choose k := by
  classical
  calc ((A ∩ ·) '' 𝒜).ncard
      = (traceFinset 𝒜 hA).card := (card_traceFinset 𝒜 hA).symm
    _ ≤ (traceFinset 𝒜 hA).shatterer.card := Finset.card_le_card_shatterer _
    _ ≤ ∑ k ∈ Finset.Iic (traceFinset 𝒜 hA).vcDim, (Fintype.card ↥hA.toFinset).choose k :=
        Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Finset.Iic d, (Fintype.card ↥hA.toFinset).choose k :=
        Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.2 (vcDim_traceFinset_le h𝒜 hA))
    _ ≤ ∑ k ∈ Finset.Iic d, n.choose k :=
        Finset.sum_le_sum fun k _ ↦ Nat.choose_le_choose k
          (by rw [Fintype.card_coe, ← Set.ncard_eq_toFinset_card _ hA]; exact hAn)

lemma HasVCDimLE.vcGrowth_le (h𝒜 : HasVCDimLE d 𝒜) :
    vcGrowth n 𝒜 ≤ ∑ k ∈ Finset.Iic d, n.choose k :=
  vcGrowth_le_iff.2 fun _A hA hAn ↦ h𝒜.ncard_image_inter_le hA hAn

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
    exact ⟨A, hA, shatters_iff_le_ncard_image_inter.2 h, by lia⟩
  · rintro h A hA hA𝒜
    contrapose! h
    rw [← Nat.add_one_le_iff] at h
    obtain ⟨B, hBA, hB, hBd⟩ := Set.exists_subset_ncard_eq hA h
    refine ⟨B, hB, hBd, ?_⟩
    grw [← hBd, ← shatters_iff_le_ncard_image_inter, hBA]
    exact hA𝒜

end Set
