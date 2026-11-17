import «section 3».GammaFrozenSelectedSchemaRows

/-! Generic full-tuple geometric formula witnesses specialize to the
actual unary selected families on a generic frozen VF tail. All formulas,
including complete Gamma density code classes, remain over that base. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6500000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section5 IntegrationInACVF.Section6 IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {n a b k : ℕ}
variable {U : DefSet (M := M) Set.univ (n+1) a} {V : DefSet (M := M) Set.univ (n+1) b}

theorem gammaFrozenSelected_generic_formula_witnesses
    (hU : GammaSetDefinable B (carrier U)) (hV : GammaSetDefinable B (carrier V))
    (ρ : Fin (k+1) → Fin a) (τ : Fin (k+1) → Fin b)
    (Q : GammaGroundDefSet hc B (rawRVSpace (M := M) a)) (R : GammaGroundDefSet hc B (rawRVSpace (M := M) b))
    (hL : ∀ u : U, u.val.2 ∈ Q.carrier) (hK : ∀ v : V, v.val.2 ∈ R.carrier)
    (ω : GammaGroundVolumeForm hc B Q) (η : GammaGroundVolumeForm hc B R) (N L : ℕ)
    (hWitness : ∀ y : Fin (n+1) → VF (M := M), AlgebraicIndependent (vfParameterField B.real) y →
      ∃ H : GammaMeasuredRelationSchema
        (gammaMeasuredBoundedSelectedSchema U hU ρ (gammaPointRetainedForm U hU Q id (fun u => hL u) ω) N).essential
        (gammaMeasuredBoundedSelectedSchema V hV τ (gammaPointRetainedForm V hV R id (fun v => hK v) η) L).essential,
        H.valid (vfValues y))
    (x : Fin n → VF (M := M)) (hx : AlgebraicIndependent (vfParameterField B.real) x) (NX LX : ℕ)
    (hFX : ∀ z : Fin 1 → VF (M := M), (gammaMeasuredBoundedSelectedSchema
      (extendBase (coordinateFibre U 0 (headFrozenTuple x)) (Set.subset_univ _))
      (gammaFrozenHeadPreparation_source hU x) ρ (gammaFrozenRetainedForm hU Q hL ω x) NX).valid (vfValues z))
    (hGX : ∀ z : Fin 1 → VF (M := M), (gammaMeasuredBoundedSelectedSchema
      (extendBase (coordinateFibre V 0 (headFrozenTuple x)) (Set.subset_univ _))
      (gammaFrozenHeadPreparation_source hV x) τ (gammaFrozenRetainedForm hV R hK η x) LX).valid (vfValues z)) :
    ∀ z : Fin 1 → VF (M := M), AlgebraicIndependent (vfParameterField (B.real ∪ Set.range (vfValues x))) z →
      ∃ H : GammaMeasuredRelationSchema
        (gammaMeasuredBoundedSelectedSchema (extendBase (coordinateFibre U 0 (headFrozenTuple x)) (Set.subset_univ _))
          (gammaFrozenHeadPreparation_source hU x) ρ (gammaFrozenRetainedForm hU Q hL ω x) NX).essential
        (gammaMeasuredBoundedSelectedSchema (extendBase (coordinateFibre V 0 (headFrozenTuple x)) (Set.subset_univ _))
          (gammaFrozenHeadPreparation_source hV x) τ (gammaFrozenRetainedForm hV R hK η x) LX).essential,
        H.valid (vfValues z) := by
  intro z hz
  have hz' : AlgebraicIndependent (tupleField (vfParameterField B.real) x) z :=
    Eq.mp (congrArg (fun E : Subfield (Section2.VF M) => AlgebraicIndependent E z) (vfParameterField_union_tuple B.real x)) hz
  have hy := independent_cons_over_tuple_field (vfParameterField B.real) x z hx hz'
  obtain ⟨H,hH⟩ := hWitness (Fin.cons (z 0) x) hy
  let BC := gammaFrozenFormulaBaseChange B x
  let C := gammaFrozenParameterRecode B x
  let F := gammaMeasuredBoundedSelectedSchema U hU ρ (gammaPointRetainedForm U hU Q id (fun u => hL u) ω) N
  let E := gammaMeasuredBoundedSelectedSchema V hV τ (gammaPointRetainedForm V hV R id (fun v => hK v) η) L
  let FX := gammaMeasuredBoundedSelectedSchema (extendBase (coordinateFibre U 0 (headFrozenTuple x)) (Set.subset_univ _))
    (gammaFrozenHeadPreparation_source hU x) ρ (gammaFrozenRetainedForm hU Q hL ω x) NX
  let GX := gammaMeasuredBoundedSelectedSchema (extendBase (coordinateFibre V 0 (headFrozenTuple x)) (Set.subset_univ _))
    (gammaFrozenHeadPreparation_source hV x) τ (gammaFrozenRetainedForm hV R hK η x) LX
  let FR := gammaMeasuredSchemaChangeBase BC F.essential
  let ER := gammaMeasuredSchemaChangeBase BC E.essential
  let H' := gammaMeasuredGeometryChangeBase BC H
  have hH' : H'.valid (vfValues (Fin.cons (z 0) x)) := (gammaMeasuredGeometryChangeBase_valid BC H _).mpr hH
  let HK := H'.recode C
  have hHK : HK.valid (vfValues z) := H'.recode_valid C _ _ (fun j => (z j).property)
    (gammaFrozenParameterRecode_geometry_rows x H' z) hH'
  have hFR := (HK.valid_endpoints hHK).1
  have hER := (HK.valid_endpoints hHK).2
  have hFRow := gammaMeasured_rowAgreement_essential (gammaFrozenSelectedSchema_rowAgreement hU ρ Q hL ω x N NX z)
  have hERow := gammaMeasured_rowAgreement_essential (gammaFrozenSelectedSchema_rowAgreement hV τ R hK η x L LX z)
  have hFRRec := (GammaVolumeParameterRecode.mk C).volumeObject_rows FR.toRVTemplate _ _
    (gammaFrozenParameterRecode_volume_rows x FR.toRVTemplate z)
  have hERRec := (GammaVolumeParameterRecode.mk C).volumeObject_rows ER.toRVTemplate _ _
    (gammaFrozenParameterRecode_volume_rows x ER.toRVTemplate z)
  have hSameF : FX.essential.toRVTemplate.sameRow (FR.recode C).toRVTemplate (vfValues z) :=
    gammaMeasured_sameRow_of_agreements (E := FR) (F := FX.essential) (G := FR.recode C)
      (z := vfValues (Fin.cons (z 0) x)) (t := vfValues z)
      (fun j => ((Fin.cons (z 0) x : Fin (n+1) → VF (M := M)) j).property) (fun j => (z j).property) hFRow hFRRec
  have hSameG : (ER.recode C).toRVTemplate.sameRow GX.essential.toRVTemplate (vfValues z) :=
    gammaMeasured_sameRow_of_agreements (E := ER) (F := ER.recode C) (G := GX.essential)
      (z := vfValues (Fin.cons (z 0) x)) (t := vfValues z)
      (fun j => ((Fin.cons (z 0) x : Fin (n+1) → VF (M := M)) j).property) (fun j => (z j).property) hERRec hERow
  exact ⟨.trans (FR.recode C) (.agreement FX.essential (FR.recode C))
    (.trans (ER.recode C) HK (.agreement (ER.recode C) GX.essential)),
    ⟨⟨FX.essential_valid _ (hFX z),hFR,hSameF⟩,⟨hHK,hER,GX.essential_valid _ (hGX z),hSameG⟩⟩⟩

end DiamondIntegral.Section3
