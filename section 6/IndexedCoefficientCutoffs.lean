import «section 6».SelectedProgramBaseMaps
import «section 6».UnaryCoefficientMaps
import «section 6».VariableFocusCutoffs

/-! Actual old coefficient and aperture maps on joint active domains.
Complete coefficient RV rows give label constancy and the uniform bound;
the aperture is defined by its full Gamma graph over the original base. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s k : ℕ}
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem FocusComponentParameterTemplate.coefficient_nonzero_of_good
    (T : FocusComponentParameterTemplate (M := M) S 1 n s)
    (A : MixedSetParameterTemplate (M := M) S 1 n s)
    (P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s) (a : Fin 1 → M)
    (ha : a ∈ T.good A P) : vfScalarTemplateValue T.coefficient a ha.1.1.2 ≠ 0 := by
  let c := vfScalarTemplateValue T.coefficient a ha.1.1.2
  let t := gammaTemplateRepresentative T.radius a ha.1.2
  have hGeo := focusMetadataParameterLocus_at T.coefficient T.radius (T.geometricLocus A P)
    a ha.1.1.2 ha.1.2 ha.2.2
  exact ((coefficientCodeCondition_at a c t).mp hGeo.1.1).1

def unaryIndexedBaseProjection
    (C : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hBase : ∀ p ∈ C.carrier,unaryFamilyBasePoint p ∈ B.carrier) : Map C B :=
  ((unaryFamilyBaseMap S n r s).comp
    (Map.inclusion (fun _ _ => Set.mem_univ _))).corestrict (fun p => hBase p.val p.property)

theorem unaryIndexedBaseProjection_value
    (C : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hBase : ∀ p ∈ C.carrier,unaryFamilyBasePoint p ∈ B.carrier) (p : C) :
    (unaryIndexedBaseProjection C hBase p).val=unaryFamilyBasePoint p.val := rfl

def indexedCoefficientMap
    (T : ContinuousVFGraphTemplate (M := M) S 1 0 1)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.good)
    (C : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hBase : ∀ p ∈ C.carrier,unaryFamilyBasePoint p ∈ B.carrier) :
    Map C (DefSet.univ (rawVFSpace (M := M) 1) S) :=
  (unaryCoefficientMap T η hGood).comp (unaryIndexedBaseProjection C hBase)

theorem indexedCoefficientMap_value
    (T : ContinuousVFGraphTemplate (M := M) S 1 0 1)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.good)
    (C : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hBase : ∀ p ∈ C.carrier,unaryFamilyBasePoint p ∈ B.carrier) (p : C) :
    (indexedCoefficientMap T η hGood C hBase p).val 0=
      vfScalarTemplateValue T (unaryFamilyParameter η (unaryIndexedBaseProjection C hBase p))
        (hGood (unaryIndexedBaseProjection C hBase p)) :=
  unaryCoefficientMap_value T η hGood (unaryIndexedBaseProjection C hBase p)

theorem indexedCoefficientMap_rv_constant
    (T : ContinuousVFGraphTemplate (M := M) S 1 0 1)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.good)
    (C : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hBase : ∀ p ∈ C.carrier,unaryFamilyBasePoint p ∈ B.carrier)
    (hRows : ∀ b c : B,b.val.2=c.val.2 →
      ((coefficientRVDataTemplate T).fibre (unaryFamilyParameter η b)).carrier=
        ((coefficientRVDataTemplate T).fibre (unaryFamilyParameter η c)).carrier)
    (p z : C) (hTags : p.val.2=z.val.2) :
    rv M ((indexedCoefficientMap T η hGood C hBase p).val 0)=
      rv M ((indexedCoefficientMap T η hGood C hBase z).val 0) := by
  apply unaryCoefficientMap_rv_constant T η hGood hRows
  change p.val.2 ∘ Fin.castAdd s=z.val.2 ∘ Fin.castAdd s
  rw [hTags]

theorem indexedCoefficientMap_bound
    (T : ContinuousVFGraphTemplate (M := M) S 1 0 1)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (hGood : ∀ b : B,unaryFamilyParameter η b ∈ T.good)
    (C : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S)
    (hBase : ∀ p ∈ C.carrier,unaryFamilyBasePoint p ∈ B.carrier) (γ : Gamma M)
    (hBound : ∀ b : B,∀ u ∈ ((coefficientRVDataTemplate T).fibre (unaryFamilyParameter η b)).carrier,
      ∀ i,(γ⁻¹).val ≤ Values.vrv (u i) ∧ Values.vrv (u i) ≤ γ.val) (p : C) :
    (γ⁻¹).val ≤ vfValue ((indexedCoefficientMap T η hGood C hBase p).val 0) ∧
      vfValue ((indexedCoefficientMap T η hGood C hBase p).val 0) ≤ γ.val :=
  unaryCoefficientMap_bound T η hGood γ hBound (unaryIndexedBaseProjection C hBase p)

end DiamondIntegral.Section6
