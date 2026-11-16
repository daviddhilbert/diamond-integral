import «section 6».UnaryCarriedPreparation

/-! Actual original-base source and image domains for an aperture
release. They are defined using the two concrete branch tests, rather
than a formal annulus unrelated to the permitted maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6.CentripetalData

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S}

theorem coreCode_definable (D : CentripetalData (G := G) A) :
    S.Definable LRV {z | D.coreCode z} := by
  have hFocus : S.DefinableFun LRV D.focusCode := scalarCodeExtension_definable D.focusMap
  have hCoeff : S.DefinableFun LRV (fun _ : Fin n ⊕ Fin r → M => D.coefficient.val) :=
    definable_named_constant D.coefficient.val D.coefficient_definable
  have hProduct : S.DefinableFun LRV D.productCode := scalarMulCode_definable hCoeff hFocus
  have hDiff : S.DefinableFun LRV D.differenceCode :=
    scalarSubCode_definable (Set.DefinableFun.proj LRV) hFocus
  exact (rvCode_compare_definable (rv_scalarCode_definable hDiff)
    (rv_scalarCode_definable hProduct)).compl

def releasedDomain (D E : CentripetalData (G := G) A) :
    DefSet (rawMixedSpace (M := M) n r) S := by
  have hD : (rawMixedSpace (M := M) n r).Definable S {p | D.core p = true} := by
    convert mixedValues_preimage_definable _ D.coreCode_definable using 1
    ext p
    exact (D.coreCode_at p).symm
  have hE : (rawMixedSpace (M := M) n r).Definable S {p | E.core p = false} := by
    convert (mixedValues_preimage_definable _ E.coreCode_definable).compl _ using 1
    ext p
    exact ⟨fun h => fun ht => Bool.noConfusion (h.symm.trans ((E.coreCode_at p).mp ht)),
      fun h => Bool.eq_false_iff.mpr (fun ht => h ((E.coreCode_at p).mpr ht))⟩
  exact ⟨{p | p ∈ A.carrier ∧ D.core p = true ∧ E.core p = false},
    A.definable.inter _ (hD.inter _ hE)⟩

theorem releasedDomain_subset (D E : CentripetalData (G := G) A) :
    (D.releasedDomain E).carrier ⊆ A.carrier := fun _ h => h.1

theorem releasedDomain_properInvariant
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (D E : CentripetalData (G := G) A) : ProperInvariant S (D.releasedDomain E).carrier := by
  apply (lemma_6_5 h00 hc hκ hs hv _ (D.releasedDomain E).definable
    (D.sourceProper.vfBounded.mono (D.releasedDomain_subset E))
    (D.sourceProper.rvBounded.mono (D.releasedDomain_subset E))).mpr
  intro u
  have he : vfFibre (D.releasedDomain E).carrier u = D.branch u true ∩ E.branch u false := by
    ext a
    exact ⟨fun h => ⟨⟨h.1,h.2.1⟩,h.1,h.2.2⟩,fun h => ⟨h.1.1,h.1.2,h.2.2⟩⟩
  rw [he]
  exact (D.branch_isClopen hv u true).inter (E.branch_isClopen hv u false)

def releasedRegularizedImage (D E : CentripetalData (G := G) A) :
    DefSet (rawMixedSpace (M := M) n (n+(1+r))) S :=
  (((regularization E.map.image).comp E.bijection).restrict (D.releasedDomain_subset E)).image

theorem mem_releasedRegularizedImage (D E : CentripetalData (G := G) A)
    (q : Mixed M n (n+(1+r))) : q ∈ (D.releasedRegularizedImage E).carrier ↔
      ∃ p, p ∈ A.carrier ∧ D.core p = true ∧ E.core p = false ∧
        DiamondIntegral.Section6.regularize (E.point p) = q := by
  exact ⟨fun ⟨p,hp⟩ => ⟨p.val,p.property.1,p.property.2.1,p.property.2.2,hp⟩,
    fun ⟨p,hp,hD,hE,he⟩ => ⟨⟨p,hp,hD,hE⟩,he⟩⟩

end DiamondIntegral.Section6.CentripetalData
