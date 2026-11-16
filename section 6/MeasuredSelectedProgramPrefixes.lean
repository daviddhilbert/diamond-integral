import «section 6».SelectedMeasuredRegularizationTerminal
import «section 6».UniformMeasuredPrefixValues
import «section 6».MeasuredPreparationTransport

/-! Identity and regularization prefixes preserve the precise agreement
between the actual ambient form and the remaining local forms. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 14000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.SelectedProgramContext
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q t k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {W : GammaFormParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}

def regularizationGammaForm
    (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    Map (regularizeMap C).image (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  ω.comp ((regularization C).inverse (regularization_bijective C))

theorem regularizationGammaForm_transport
    (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S)) (p : C) :
    (regularizationGammaForm ω (regularization C p)).val=(ω p).val := by
  change (ω ((regularization C).inverse _ (regularization C p))).val=(ω p).val
  rw [Map.inverse_apply]

theorem afterIdentity_source_form
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {H : CentripetalProgramTemplate (M := M) S 1 n s t}
    (U : UniformMeasuredProgramFamily (G := G) η ((CentripetalProgramTemplate.identity s).comp H) A P W)
    (X : SelectedProgramContext η A P C π σ)
    (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSource : ∀ p : C,gammaFormExtension (U.forms (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val) :
    ∀ p : C,gammaFormExtension ((U.afterPrefix h00 hc linear hκ hs hv hsmall hΓ).forms
      ((X.afterIdentity (fun b => (U.geometry b).subset)).baseMap p))
      (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val := by
  intro p
  let b := X.baseMap p
  let x := X.localSourcePoint p
  let y : ((CentripetalProgramTemplate.identity s).target A).fibre (unaryFamilyParameter η b) :=
    ⟨x.val,by
      change x.val ∈ (((CentripetalProgramTemplate.identity s).pieceTarget A A).fibre _).carrier
      rw [identity_pieceTarget_fibre A A _ (Set.Subset.refl _)]
      exact x.property⟩
  have hBase : (X.afterIdentity (fun b => (U.geometry b).subset)).baseMap p=b := by
    apply Subtype.ext
    exact (SelectedProgramContext.baseMap_value _ p).trans (X.baseMap_value p).symm
  have h := U.afterPrefix_value h00 hc linear hκ hs hv hsmall hΓ b (Map.id (A.fibre _))
    Function.bijective_id (identityParameterTransition_at A _) x y rfl
  rw [hBase]
  exact (gammaFormExtension_at _ y).trans (h.trans ((gammaFormExtension_at (U.forms b) x).symm.trans (hSource p)))

theorem afterRegularization_source_form
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {H : CentripetalProgramTemplate (M := M) S 1 n (n+s) t}
    (U : UniformMeasuredProgramFamily (G := G) η ((CentripetalProgramTemplate.regularize s).comp H) A P W)
    (X : SelectedProgramContext η A P C π σ)
    (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hSource : ∀ p : C,gammaFormExtension (U.forms (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val) :
    ∀ z : (regularizeMap C).image,gammaFormExtension ((U.afterPrefix h00 hc linear hκ hs hv hsmall hΓ).forms
      ((X.afterRegularization h00 hc hκ hs hv (fun b => (U.geometry b).subset)).baseMap z))
      (Fin.tail z.val.1,z.val.2 ∘ regularizedTailLabels σ)=(regularizationGammaForm ω z).val := by
  intro z
  obtain ⟨p,hp⟩ := z.property
  have hz : z=regularization C p := Subtype.ext hp.symm
  subst z
  let b := X.baseMap p
  let x := X.localSourcePoint p
  let y : ((CentripetalProgramTemplate.regularize s).target A).fibre (unaryFamilyParameter η b) :=
    ⟨regularize x.val,by
      exact (regularization_pieceTarget_mem_iff A A _ (Set.Subset.refl _) x.val).mpr x.property⟩
  have hBase : (X.afterRegularization h00 hc hκ hs hv (fun b => (U.geometry b).subset)).baseMap
      (regularization C p)=b := by
    apply Subtype.ext
    rw [SelectedProgramContext.baseMap_value,X.baseMap_value,regularization_apply]
    exact selectedUnaryBasePoint_regularize π p.val
  have hLocal : (Fin.tail (regularization C p).val.1,
      (regularization C p).val.2 ∘ regularizedTailLabels σ)=regularize x.val := by
    have h := regularized_selected_tail π σ p.val
    rw [selectedJointPoint_local] at h
    exact h
  have h := U.afterPrefix_value h00 hc linear hκ hs hv hsmall hΓ b (regularization (A.fibre _))
    (regularization_bijective _) (regularizationParameterTransition_at A _) x y rfl
  rw [hBase,hLocal,regularizationGammaForm_transport]
  exact (gammaFormExtension_at _ y).trans (h.trans ((gammaFormExtension_at (U.forms b) x).symm.trans (hSource p)))

end DiamondIntegral.Section6.SelectedProgramContext
