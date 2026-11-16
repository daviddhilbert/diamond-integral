import «section 6».MeasuredVFReindexedPreparation
import «section 6».SemanticGammaBranchDescent
import «section 6».PermutedCoordinateBundles

/-! Semantic form constancy in an arbitrary VF coordinate gives an
actual original-base Gamma descent through that coordinate projection,
with inherited open levels. No radius or individual Gamma name is added. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def CoordinateGammaConstant (j : Fin (n+1))
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) : Prop :=
  ∀ p q : A,(∀ i,i ≠ j → p.val.1 i=q.val.1 i) → p.val.2=q.val.2 → (ω p).val=(ω q).val

theorem CoordinateGammaConstant.reindexed_projection_constant
    {j : Fin (n+1)} {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (h : CoordinateGammaConstant j ω) (e : Fin (n+1) ≃ Fin (n+1)) (he : e (Fin.last n)=j) :
    ∀ p ∈ (reindexedVFSet A e).carrier,∀ q ∈ (reindexedVFSet A e).carrier,
      Fin.init p.1=Fin.init q.1 → p.2=q.2 →
      gammaFormExtension (reindexedGammaForm ω e) p=gammaFormExtension (reindexedGammaForm ω e) q := by
  intro p hp q hq hInit hTags
  rw [gammaFormExtension_at _ ⟨p,hp⟩,gammaFormExtension_at _ ⟨q,hq⟩]
  apply h (reindexVFInverseMap A e ⟨p,hp⟩) (reindexVFInverseMap A e ⟨q,hq⟩) _ hTags
  intro i hi
  have hBefore : e.symm i ≠ Fin.last n := by
    intro hn
    apply hi
    exact (e.apply_symm_apply i).symm.trans ((congrArg e hn).trans he)
  exact Fin.lastCases (motive := fun k => k ≠ Fin.last n → p.1 k=q.1 k)
    (fun hn => False.elim (hn rfl)) (fun k _ => congrFun hInit k) (e.symm i) hBefore

theorem reindexedGammaForm_levels_open
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) (e : Fin (n+1) ≃ Fin (n+1))
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+1) → VF M | (x,u) ∈ A.carrier ∧ gammaFormExtension ω (x,u)=γ}) :
    ∀ u γ,IsOpen {x : Fin (n+1) → VF M | (x,u) ∈ (reindexedVFSet A e).carrier ∧
      gammaFormExtension (reindexedGammaForm ω e) (x,u)=γ} := by
  intro u γ
  have he : {x : Fin (n+1) → VF M | (x,u) ∈ (reindexedVFSet A e).carrier ∧
      gammaFormExtension (reindexedGammaForm ω e) (x,u)=γ}=
      (fun x : Fin (n+1) → VF M => x ∘ e.symm) ⁻¹'
        {x : Fin (n+1) → VF M | (x,u) ∈ A.carrier ∧ gammaFormExtension ω (x,u)=γ} := by
    ext x
    constructor
    · rintro ⟨hx,hγ⟩
      have hOld := (mem_reindexedVFSet A e (x,u)).mp hx
      refine ⟨hOld,?_⟩
      rw [gammaFormExtension_at _ ⟨_,hx⟩] at hγ
      exact (gammaFormExtension_at ω ⟨_,hOld⟩).trans hγ
    · rintro ⟨hx,hγ⟩
      have hNew := (mem_reindexedVFSet A e (x,u)).mpr hx
      refine ⟨hNew,?_⟩
      rw [gammaFormExtension_at _ ⟨_,hNew⟩]
      exact (gammaFormExtension_at ω ⟨_,hx⟩).symm.trans hγ
  rw [he]
  exact (hLevels u γ).preimage (continuous_pi (fun i => continuous_apply (e.symm i)))

theorem CoordinateGammaConstant.exists_coordinate_descent
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hA : ProperInvariant S A.carrier)
    {j : Fin (n+1)} {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (h : CoordinateGammaConstant j ω) (e : Fin (n+1) ≃ Fin (n+1)) (he : e (Fin.last n)=j)
    (hLevels : ∀ u γ,IsOpen {x : Fin (n+1) → VF M | (x,u) ∈ A.carrier ∧ gammaFormExtension ω (x,u)=γ}) :
    ∃ η : Map (coordinateProjection A e) (DefSet.univ (rawGammaPresentation (M := M)) S),
      (∀ q : reindexedVFSet A e,η ((vfDropLast (reindexedVFSet A e)).toImage q)=reindexedGammaForm ω e q) ∧
      ∀ u γ,IsOpen {x : Fin n → VF M | (x,u) ∈ (coordinateProjection A e).carrier ∧ gammaFormExtension η (x,u)=γ} := by
  let hConst := h.reindexed_projection_constant e he
  let η := coordinateGammaDescent (reindexedGammaForm ω e) hConst
  have hη := coordinateGammaDescent_at (reindexedGammaForm ω e) hConst
  exact ⟨η,hη,descended_gamma_levels_open h00 hc linear hκ hs hv hsmall hΓ
    (reindexedVFSet_properInvariant A e hA) (reindexedGammaForm ω e)
    (reindexedGammaForm_levels_open ω e hLevels) η hη⟩

end DiamondIntegral.Section6
