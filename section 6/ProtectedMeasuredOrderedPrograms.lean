import «section 6».ProtectedOrderedPrograms
import «section 6».SelectedInverseGammaTransport
import «section 6».MeasuredOrderedProgramData

/-! Membership grafting retains the exact source Gamma form and its
open levels. Measured ordered existence on the grafted source therefore
yields a protected measured program on the original source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def membershipGraftForm (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :=
  ω.comp ((graft hc (properMembershipLabels A C)).inverse (graft_bijective hc _))

theorem membershipGraftForm_transport (hc : CanonicalStructure.IsCanonical (M := M))
    (A : DefSet (rawMixedSpace (M := M) n r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (p : A) :
    (membershipGraftForm hc A C ω (graft hc (properMembershipLabels A C) p)).val=(ω p).val := by
  change (ω ((graft hc (properMembershipLabels A C)).inverse (graft_bijective hc _)
    (graft hc (properMembershipLabels A C) p))).val=_
  rw [Map.inverse_apply]

theorem membershipGraftForm_levels_open
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) n r) S) (hA : ProperInvariant S A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S) (hC : ∀ i,ProperInvariant S (C i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hLevels : ∀ u γ,IsOpen {a : Fin n → VF M | (a,u) ∈ A.carrier ∧ gammaFormExtension ω (a,u)=γ}) :
    ∀ v γ,IsOpen {a : Fin n → VF M | (a,v) ∈ (graftMap hc (properMembershipLabels A C)).image.carrier ∧
      gammaFormExtension (membershipGraftForm hc A C ω) (a,v)=γ} := by
  let τ := properMembershipLabels A C
  have hτ := properMembershipLabels_properCovariant h00 hc hκ hs hv A hA C hC
  have hG := graft_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ τ hA hτ
  apply transported_gamma_levels_open_selected (graft hc τ) (graft_bijective hc τ) (Fin.castAdd k)
    (fun p i => by simp only [graft_apply,Fin.append_left]) hG.inverseContinuous
    (fun v => ((graft_properInvariant h00 hc hκ hs hv τ hA hτ).clopen_fibres hv v).isOpen) ω hLevels

structure ProtectedMeasuredOrderedProgram (A : DefSet (rawMixedSpace (M := M) n r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) where
  contraction : ProtectedOrderedProgram (G := G) A C
  rvForm : Map contraction.target (DefSet.univ (rawGammaPresentation (M := M)) S)
  factor : ∀ p : A,(rvForm (contraction.program.toMap p)).val=(ω p).val

def ProtectedMeasuredOrderedProgram.toMeasuredProgram
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {C : Fin k → DefSet (rawMixedSpace (M := M) n r) S}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (F : ProtectedMeasuredOrderedProgram (G := G) A C ω) : MeasuredOrderedProgram (G := G) A ω where
  arity := F.contraction.arity
  rvTarget := F.contraction.target
  program := F.contraction.program
  rvForm := F.rvForm
  factor := F.factor

def protectedMeasuredOrderedProgram_of_grafted_program
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hA : ProperInvariant S A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S) (hC : ∀ i,ProperInvariant S (C i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (T : MeasuredOrderedProgram (G := G) (graftMap hc (properMembershipLabels A C)).image (membershipGraftForm hc A C ω)) :
    ProtectedMeasuredOrderedProgram (G := G) A C ω := by
  let P := protectedOrderedProgram_of_grafted_program h00 hc linear hκ hs hv hsmall hΓ A hA C hC T.program
  let τ := properMembershipLabels A C
  let g := graft hc τ
  have hτ := properMembershipLabels_properCovariant h00 hc hκ hs hv A hA C hC
  have hG := graft_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ τ hA hτ
  have hVF (p : A) : (g p).val.1=p.val.1 := rfl
  have hRetain (p : A) (i : Fin r) : (g p).val.2 (Fin.castAdd k i)=p.val.2 i := by
    simp only [g,graft_apply,Fin.append_left]
  have hUnit (p : A) : HasMixedUnitDerivativeAt g p := graft_unit_derivative hc hv τ hτ p
  have hMap : P.program.toMap=T.program.toMap.comp g :=
    T.program.precomposeFixedVF_toMap h00 hc linear hκ hs hv hsmall hΓ g hG hVF (Fin.castAdd k)
      (Fin.castAdd_injective r k) hRetain hUnit
  refine ⟨P,T.rvForm,fun p => ?_⟩
  rw [hMap]
  exact (T.factor (g p)).trans (membershipGraftForm_transport hc A C ω p)

end DiamondIntegral.Section6
