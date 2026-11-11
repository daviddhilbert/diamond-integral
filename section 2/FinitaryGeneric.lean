import «section 2».FinitaryBranches
import «section 2».AlmostContinuity
import Section8.MixedLocalFormula

/-!
# Simultaneous generic continuity of all finite RV branches

The exceptional set is defined over the original base. A proper RV label
adds no elements to its VF parameter field, so every coded inverse branch
is continuous at an independent VF tuple. The zero RV tag is included.
-/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section2.FinitaryRVCode
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {S : Set M} {A : Set (Fin n → VF M)}
variable {F : (Fin n → VF M) → Set (Fin m → VF M)}

theorem branch_definable (C : FinitaryRVCode S A F)
    (hG : S.Definable LRV (vfCorrespondenceGraph A F)) (t : Fin C.arity → M) :
    (S ∪ Set.range t).Definable LRV (vfGraph (C.branch t)) := by
  let B := S ∪ Set.range t
  have hmap : B.DefinableMap LRV (fun z : Fin n ⊕ Fin m → M => Sum.elim t z) := by
    rintro (i | i)
    · exact LRV.definableFun_const _ (Or.inr (Set.mem_range_self i))
    · exact Set.DefinableFun.proj LRV
  have h := ((C.branchGraph_definable hG).mono Set.subset_union_left).preimage_map hmap
  simpa only [Set.preimage, C.branchGraph_slice t] using h

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem mem_branchContinuous (C : FinitaryRVCode S A F)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (t : Fin C.arity → M) (a : Fin n → VF M) :
    Sum.elim t (vfValues a) ∈ continuousInputsFamily C.branchGraph ↔
      ContinuousAt (C.branch t) a := by
  change vfValues a ∈ continuousInputs {z | Sum.elim t z ∈ C.branchGraph} ↔ _
  rw [C.branchGraph_slice]
  exact mem_continuousInputs_iff hv _ a

def branchBadRaw (C : FinitaryRVCode S A F) : Set (Fin n → M) :=
  {a | ∃ t : Fin C.arity → M, (∀ j, iRV (t j)) ∧
    Sum.elim t a ∉ continuousInputsFamily C.branchGraph}

theorem branchBadRaw_definable (C : FinitaryRVCode S A F)
    (hG : S.Definable LRV (vfCorrespondenceGraph A F)) :
    S.Definable LRV C.branchBadRaw := by
  have hsort : S.Definable LRV {z : Fin n ⊕ Fin C.arity → M | ∀ j, iRV (z (.inr j))} := by
    rw [Set.ofPred_forall]
    exact Set.definable_iInter_of_finite (fun j =>
      ((definableAt_sort S .rv).raw_definable).preimage_comp
        (fun _ : Fin 1 => (Sum.inr j : Fin n ⊕ Fin C.arity)))
  have hcont := (continuousInputsFamily_definable (C.branchGraph_definable hG)).preimage_comp
    (Sum.swap : Fin C.arity ⊕ Fin n → Fin n ⊕ Fin C.arity)
  convert (hsort.inter hcont.compl).exists_of_finite using 1
  ext a
  apply exists_congr
  intro t
  rfl

def badRaw (C : FinitaryRVCode S A F) : Set (Fin n → M) :=
  vfRawUniverse n ∩ ((rvConstantRaw C.labelGraph)ᶜ ∪ C.branchBadRaw)

theorem badRaw_definable (C : FinitaryRVCode S A F)
    (hG : S.Definable LRV (vfCorrespondenceGraph A F)) :
    S.Definable LRV C.badRaw :=
  (vfRawUniverse_definable S n).inter
    ((rvConstantRaw_definable (C.labelGraph_definable hG)).compl.union (C.branchBadRaw_definable hG))

theorem mem_badRaw (C : FinitaryRVCode S A F)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (a : Fin n → VF M) :
    vfValues a ∈ C.badRaw ↔
      ¬ rvLocallyConstantAt (rvFibre C.labelGraph) a ∨
        ∃ t : Fin C.arity → M, (∀ j, iRV (t j)) ∧ ¬ ContinuousAt (C.branch t) a := by
  change (_ ∧ (_ ∨ _)) ↔ _
  rw [and_iff_right (show vfValues a ∈ vfRawUniverse n from fun i => (a i).property)]
  apply or_congr
  · exact not_congr (mem_rvConstantRaw_iff hv _ a)
  · apply exists_congr
    intro t
    exact and_congr_right (fun _ => not_congr (C.mem_branchContinuous hv t a))

theorem not_mem_badRaw_of_independent (C : FinitaryRVCode S A F)
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hG : S.Definable LRV (vfCorrespondenceGraph A F))
    (a : Fin n → VF M) (ha : AlgebraicIndependent (vfParameterField S) a) :
    vfValues a ∉ C.badRaw := by
  intro h
  rcases (C.mem_badRaw hv a).mp h with hloc | ⟨t, ht, hcont⟩
  · exact hloc (rvFibre_locallyConstant_of_independent hc hv (C.labelGraph_definable hG) a ha)
  · have hind : AlgebraicIndependent (vfParameterField (S ∪ Set.range t)) a := by
      rw [vfParameterField_union_rv S _ (by rintro z ⟨j, rfl⟩; exact ht j)]
      exact ha
    exact hcont (continuousAt_of_independent hc hκ hs (small_union_range hκ S hsmall t)
      hv (C.branch t) (C.branch_definable hG t) a hind)

theorem badRaw_dimension_lt (C : FinitaryRVCode S A F)
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) (hn : 0 < n)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hG : S.Definable LRV (vfCorrespondenceGraph A F)) :
    vfDimension ({a : Fin n → VF M | vfValues a ∈ C.badRaw} ×ˢ
      (Set.univ : Set (Fin 0 → RVInfinity M))) < (n : WithBot ℕ) := by
  have hdef := C.badRaw_definable hG
  have hd := vfDim_lt_of_no_independent hc hs hsmall _ (rawRVSpace_rvCoded 1) hn hdef
    (fun a ha hind => C.not_mem_badRaw_of_independent hc hκ hs hsmall hv hG a hind ha)
  have he : (vfObjectOfRaw hdef).carrier =
      {a : Fin n → VF M | vfValues a ∈ C.badRaw} ×ˢ
        (Set.univ : Set (Fin 0 → RVInfinity M)) := by
    ext p
    exact (and_iff_left (Set.mem_univ p.2)).symm
  rw [← he]
  exact vfDimension_lt_of_companion_lt hc hs hsmall _ (rawRVSpace_rvCoded 1) hv _ hd

end DiamondIntegral.Section2.FinitaryRVCode
