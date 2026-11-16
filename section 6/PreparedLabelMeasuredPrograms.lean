import «section 6».MeasuredOrderedProgramData
import «section 6».FixedVFStagePrecomposition
import «section 6».RVGraftingHomeomorphism
import «section 6».SurjectiveMapDescent

/-! The labels of an actual measured preparation can be grafted before
an arbitrary ordered program and absorbed into its first stage. The
source form descends through the actual final contraction map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k q : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S} {hCA : ∀ i,(C i).carrier ⊆ A.carrier}
variable {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}

def measuredOrderedProgramOfPreparedLabels
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hA : ProperInvariant S A.carrier) (D : MeasuredCoordinatePreparation (G := G) A C hCA ω)
    {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    (T : OrderedStandardContractionProgram (G := G) S (graftMap hc (rvProjection D.map)).image U) :
    MeasuredOrderedProgram (G := G) A ω := by
  let τ := rvProjection D.map
  let g := graft hc τ
  have hτ : ProperCovariant τ := ProperCovariant.rvProjection D.map
    (D.special.properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ).covariant
  have hG := graft_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ τ hA hτ
  have hVF (p : A) : (g p).val.1=p.val.1 := rfl
  have hRetain (p : A) (i : Fin r) : (g p).val.2 (Fin.castAdd D.arity i)=p.val.2 i := by
    simp only [g,graft_apply,Fin.append_left]
  have hUnit (p : A) : HasMixedUnitDerivativeAt g p := graft_unit_derivative hc hv τ hτ p
  let P := T.precomposeFixedVF h00 hc linear hκ hs hv hsmall hΓ g hG hVF
    (Fin.castAdd D.arity) (Fin.castAdd_injective r D.arity) hRetain hUnit
  have hMap := T.precomposeFixedVF_toMap h00 hc linear hκ hs hv hsmall hΓ g hG hVF
    (Fin.castAdd D.arity) (Fin.castAdd_injective r D.arity) hRetain hUnit
  have hCompatible : ∀ p z : A,P.toMap p=P.toMap z → ω p=ω z := by
    intro p z he
    have he' : T.toMap (g p)=T.toMap (g z) := by
      change P.toMap p=P.toMap z at he
      rw [hMap] at he
      exact he
    have hTags : (g p).val.2=(g z).val.2 := by
      funext i
      exact (T.retained (g p) i).symm.trans
        ((congrArg (fun a : U => a.val.2 (T.oldLabels i)) he').trans (T.retained (g z) i))
    have hPreparedTags : (D.map p).val.2=(D.map z).val.2 := by
      funext i
      have h := congrFun hTags (Fin.natAdd r i)
      simpa only [g,graft_apply,τ,rvProjection_apply,Fin.append_right] using h
    have hForm := D.constant (D.map p).val (D.map p).property (D.map z).val (D.map z).property hPreparedTags
    rw [gammaFormExtension_at D.form (D.map p),gammaFormExtension_at D.form (D.map z)] at hForm
    exact Subtype.ext ((D.transport p).symm.trans (hForm.trans (D.transport z)))
  exact {
    arity := q
    rvTarget := U
    program := P
    rvForm := descendSurjectiveMap P.toMap P.surjective ω hCompatible
    factor := fun p => congrArg Subtype.val (descendSurjectiveMap_factor P.toMap P.surjective ω hCompatible p) }

end DiamondIntegral.Section6
