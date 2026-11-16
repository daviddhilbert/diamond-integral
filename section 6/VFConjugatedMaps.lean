import «section 6».VFRelabelingHomeomorphisms
import «section 6».VFConjugatedPreparation
import «section 6».VFReindexedGammaForms
import «section 6».ContractionMapTransports

/-! Conjugating full definable maps by the same VF coordinate relabeling
commutes with identity and composition. Relatively unary maps remain
relatively unary, and the two permutation determinants cancel. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {C : DefSet (rawMixedSpace (M := M) n t) S}

theorem reindexVFInverseMap_value (A : DefSet (rawMixedSpace (M := M) n r) S)
    (e : Equiv.Perm (Fin n)) (p : reindexedVFSet A e) :
    (reindexVFInverseMap A e p).val=(p.val.1 ∘ e.symm,p.val.2) := rfl

theorem reindexVFInverseMap_eq (A : DefSet (rawMixedSpace (M := M) n r) S)
    (e : Equiv.Perm (Fin n)) : reindexVFInverseMap A e=
      changeMapTarget (vfRelabeling (reindexedVFSet A e) e.symm) (reindexedVFSet_inverse A e) := by
  apply Map.ext
  intro p
  apply Subtype.ext
  rw [changeMapTarget_value]
  rfl

theorem reindexVFInverseMap_left (A : DefSet (rawMixedSpace (M := M) n r) S)
    (e : Equiv.Perm (Fin n)) (p : A) : reindexVFInverseMap A e (vfRelabeling A e p)=p := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    change p.val.1 (e (e.symm i))=p.val.1 i
    rw [Equiv.apply_symm_apply]
  · rfl

theorem reindexVFInverseMap_right (A : DefSet (rawMixedSpace (M := M) n r) S)
    (e : Equiv.Perm (Fin n)) (p : reindexedVFSet A e) : vfRelabeling A e (reindexVFInverseMap A e p)=p := by
  apply Subtype.ext
  apply Prod.ext
  · funext i
    change p.val.1 (e.symm (e i))=p.val.1 i
    rw [Equiv.symm_apply_apply]
  · rfl

def reindexVFConjugate (f : Map A B) (e : Equiv.Perm (Fin n)) :
    Map (reindexedVFSet A e) (reindexedVFSet B e) :=
  (vfRelabeling B e).comp (f.comp (reindexVFInverseMap A e))

theorem reindexVFConjugate_value (f : Map A B) (e : Equiv.Perm (Fin n)) (p : reindexedVFSet A e) :
    (reindexVFConjugate f e p).val=
      ((f (reindexVFInverseMap A e p)).val.1 ∘ e,(f (reindexVFInverseMap A e p)).val.2) := rfl

theorem reindexVFConjugate_identity (A : DefSet (rawMixedSpace (M := M) n r) S)
    (e : Equiv.Perm (Fin n)) : reindexVFConjugate (Map.id A) e=Map.id (reindexedVFSet A e) := by
  apply Map.ext
  exact reindexVFInverseMap_right A e

theorem reindexVFConjugate_comp (f : Map A B) (g : Map B C) (e : Equiv.Perm (Fin n)) :
    reindexVFConjugate (g.comp f) e=(reindexVFConjugate g e).comp (reindexVFConjugate f e) := by
  apply Map.ext
  intro p
  change vfRelabeling C e (g (f (reindexVFInverseMap A e p)))=
    vfRelabeling C e (g (reindexVFInverseMap B e (vfRelabeling B e (f (reindexVFInverseMap A e p)))))
  rw [reindexVFInverseMap_left]

theorem reindexVFConjugate_relative (f : Map A B) (e : Equiv.Perm (Fin n)) (j : Fin n)
    (hRelative : ∀ p : A,∀ i,i ≠ j → (f p).val.1 i=p.val.1 i)
    (p : reindexedVFSet A e) (i : Fin n) (hi : i ≠ e.symm j) :
    (reindexVFConjugate f e p).val.1 i=p.val.1 i := by
  have hNe : e i ≠ j := fun he => hi (by
    simpa only [Equiv.symm_apply_apply] using congrArg e.symm he)
  change (f (reindexVFInverseMap A e p)).val.1 (e i)=p.val.1 i
  rw [hRelative _ _ hNe]
  change p.val.1 (e.symm (e i))=p.val.1 i
  rw [Equiv.symm_apply_apply]

theorem reindexVFConjugate_retained (f : Map A B) (e : Equiv.Perm (Fin n)) (π : Fin r → Fin s)
    (hRetained : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i)
    (p : reindexedVFSet A e) (i : Fin r) :
    (reindexVFConjugate f e p).val.2 (π i)=p.val.2 i := hRetained _ i

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem HasMixedVFDerivativeAt.changeMapTarget
    {f : Map A B} {C : DefSet (rawMixedSpace (M := M) n s) S} {p : A}
    {L : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M)}
    (h : HasMixedVFDerivativeAt f p L) (he : B=C) : HasMixedVFDerivativeAt (changeMapTarget f he) p L := by
  cases he
  exact h

theorem reindexVFInverseMap_derivative
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (A : DefSet (rawMixedSpace (M := M) n r) S) (e : Equiv.Perm (Fin n))
    (hA : ProperInvariant S A.carrier) (p : reindexedVFSet A e) :
    HasMixedVFDerivativeAt (reindexVFInverseMap A e) p (vfReindexLinear e.symm) := by
  rw [reindexVFInverseMap_eq]
  exact HasMixedVFDerivativeAt.changeMapTarget
    (vfRelabeling_derivative hv _ e.symm (reindexedVFSet_properInvariant A e hA) p) _

theorem reindexVFConjugate_generic_unit
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (e : Equiv.Perm (Fin n)) (hA : ProperInvariant S A.carrier) (hB : ProperInvariant S B.carrier)
    (hUnit : ∀ p : A,AlgebraicIndependent (vfParameterField S) p.val.1 → HasMixedUnitDerivativeAt f p)
    (p : reindexedVFSet A e) (hInd : AlgebraicIndependent (vfParameterField S) p.val.1) :
    HasMixedUnitDerivativeAt (reindexVFConjugate f e) p := by
  let E := reindexVFInverseMap A e
  let H := vfRelabeling B e
  have hE := reindexVFInverseMap_derivative hv A e hA p
  obtain ⟨L,hL,hDet⟩ := hUnit (E p) (hInd.comp e.symm e.symm.injective)
  have hH := vfRelabeling_derivative hv B e hB (f (E p))
  refine ⟨(vfReindexLinear e).comp (L.comp (vfReindexLinear e.symm)),
    mixedDerivative_comp (f.comp E) H p (mixedDerivative_comp E f p hE hL) hH,?_⟩
  rw [LinearMap.toMatrix'_comp,Matrix.det_mul,LinearMap.toMatrix'_comp,Matrix.det_mul,hDet,one_mul]
  have h := congrArg (fun D => (LinearMap.toMatrix' D).det) (vfReindexLinear_symm_comp (M := M) e.symm)
  simpa only [Equiv.symm_symm,LinearMap.toMatrix'_comp,Matrix.det_mul,LinearMap.toMatrix'_id,Matrix.det_one] using h

theorem reindexVFConjugate_homeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (f : Map A B) (e : Equiv.Perm (Fin n)) (hF : ProperCovariantHomeomorphism f) :
    ProperCovariantHomeomorphism (reindexVFConjugate f e) := by
  have hA := hF.covariant.source_properInvariant h00 hc linear hκ hs hv hsmall hΓ
  have hB := hF.covariant.target_properInvariant h00 hc linear hκ hs hv hsmall hΓ hF.bijective.surjective
  have hE : ProperCovariantHomeomorphism (reindexVFInverseMap A e) := by
    rw [reindexVFInverseMap_eq]
    exact (vfRelabeling_homeomorphism h00 hc linear hκ hs hv hsmall hΓ _ e.symm
      (reindexedVFSet_properInvariant A e hA)).changeMapTarget _
  exact lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ
    (lemma_6_9 h00 hc linear hκ hs hv hsmall hΓ hE hF)
    (vfRelabeling_homeomorphism h00 hc linear hκ hs hv hsmall hΓ B e hB)

end DiamondIntegral.Section6
