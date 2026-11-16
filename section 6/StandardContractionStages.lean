import «section 6».UnaryStandardContraction
import «section 6».CoordinateBundleCriterion
import «section 6».PermutedCoordinateBundles

/-! Actual stages of an ordered standard contraction. Each stage changes
only its last VF coordinate, retains every original label, has the approved
almost-everywhere total unit Jacobian, and recovers its entire target as
the full RV-disc bundle over its contracted source. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure StandardContractionStage (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) where
  arity : ℕ
  target : DefSet (rawMixedSpace (M := M) (n+1) arity) S
  lift : Map A target
  home : ProperCovariantHomeomorphism lift
  proper : ProperInvariant S target.carrier
  doublyBounded : VFDoublyBounded target.carrier
  relative : ∀ p : A,∀ i : Fin n,(lift p).val.1 i.castSucc=p.val.1 i.castSucc
  oldLabels : Fin r → Fin arity
  oldLabels_injective : Function.Injective oldLabels
  retained : ∀ p : A,∀ i,(lift p).val.2 (oldLabels i)=p.val.2 i
  leading : Fin arity
  bundle : target.carrier=(rvCoordinateBundle (vfDropLast target).image leading).carrier
  exceptional : DefSet (rawMixedSpace (M := M) (n+1) r) S
  exceptional_subset : exceptional.carrier ⊆ A.carrier
  exceptional_dim : vfDim (rawRVSpace (M := M) 1) exceptional < n+1
  unitDerivative : ∀ p : A,p.val ∉ exceptional.carrier → HasMixedUnitDerivativeAt lift p

namespace StandardContractionStage
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

def contracted (T : StandardContractionStage (G := G) A) := (vfDropLast T.target).image

def contraction (T : StandardContractionStage (G := G) A) : Map A T.contracted :=
  (vfDropLast T.target).toImage.comp T.lift

theorem contraction_value (T : StandardContractionStage (G := G) A) (p : A) :
    (T.contraction p).val=(Fin.init (T.lift p).val.1,(T.lift p).val.2) := rfl

theorem contraction_surjective (T : StandardContractionStage (G := G) A) : Function.Surjective T.contraction := by
  rintro ⟨z,q,hq⟩
  obtain ⟨p,hp⟩ := T.home.bijective.surjective q
  refine ⟨p,Subtype.ext ?_⟩
  change (vfDropLast T.target (T.lift p)).val=z
  rw [hp]
  exact hq

theorem contracted_proper (T : StandardContractionStage (G := G) A) : ProperInvariant S T.contracted.carrier :=
  vfDropLast_image_properInvariant T.proper

theorem contracted_doublyBounded (T : StandardContractionStage (G := G) A) : VFDoublyBounded T.contracted.carrier := by
  obtain ⟨δ,hδ⟩ := T.doublyBounded
  refine ⟨δ,?_⟩
  rintro q ⟨p,rfl⟩ i
  exact hδ p.val p.property i.castSucc

theorem recover_target (T : StandardContractionStage (G := G) A) (q : Mixed M (n+1) T.arity) :
    q ∈ T.target.carrier ↔ (Fin.init q.1,q.2) ∈ T.contracted.carrier ∧ rv M (q.1 (Fin.last n))=q.2 T.leading := by
  rw [T.bundle]
  rfl

theorem contraction_fixes_complement (T : StandardContractionStage (G := G) A) (p : A) :
    (T.contraction p).val.1=Fin.init p.val.1 := by
  funext i
  exact T.relative p i

theorem contraction_retains_old_labels (T : StandardContractionStage (G := G) A) (p : A) (i : Fin r) :
    (T.contraction p).val.2 (T.oldLabels i)=p.val.2 i := T.retained p i

end StandardContractionStage

theorem rvPullback_last_coordinate_bundle
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hA : IsRVPullback A.carrier) (k : Fin r)
    (hLeading : ∀ p ∈ A.carrier,rv M (p.1 (Fin.last n))=p.2 k) :
    A.carrier=(rvCoordinateBundle (vfDropLast A).image k).carrier := by
  apply coordinate_bundle_of_replacement A k hLeading
  intro p hp d hd
  apply rvPullback_mem_of_sameRV hA hp (q := (Function.update p.1 (Fin.last n) d,p.2)) _ rfl
  funext i
  by_cases hi : i=Fin.last n
  · subst i
    change rv M (p.1 (Fin.last n))=rv M (Function.update p.1 (Fin.last n) d (Fin.last n))
    rw [Function.update_self]
    exact hd.symm
  · change rv M (p.1 i)=rv M (Function.update p.1 (Fin.last n) d i)
    rw [Function.update_of_ne hi]

theorem exists_regularization_contraction_stage
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S)
    (hA : ProperInvariant S A.carrier) (hD : VFDoublyBounded A.carrier) (hRP : IsRVPullback A.carrier) :
    ∃ T : StandardContractionStage (G := G) A,IsRVPullback T.target.carrier := by
  let H : SpecialCovariantChain (G := G) A (regularizeMap A).image (regularization A) := .regularize A hA hD
  obtain ⟨hHome,hOther,hJac⟩ := lemma_6_14 h00 hc linear hκ hs hv hsmall hΓ H
  obtain ⟨E,hEA,hDim,hUnit⟩ := hJac (Nat.zero_lt_succ n)
  have hLeading (p : Mixed M (n+1) ((n+1)+r)) (hp : p ∈ (regularizeMap A).image.carrier) :
      rv M (p.1 (Fin.last n))=p.2 (Fin.castAdd r (Fin.last n)) := by
    obtain ⟨q,rfl⟩ := hp
    simp only [regularizeMap,Map.ofCodes,regularize,Fin.append_left]
    rfl
  exact ⟨{
    arity := (n+1)+r
    target := (regularizeMap A).image
    lift := regularization A
    home := hHome
    proper := regularization_properInvariant h00 hc hκ hs hv A hA hD
    doublyBounded := regularized_vfDoublyBounded hD
    relative := fun _ _ => rfl
    oldLabels := Fin.natAdd (n+1)
    oldLabels_injective := Fin.natAdd_injective r (n+1)
    retained := fun p i => by simp only [regularization_apply,regularize,Fin.append_right]
    leading := Fin.castAdd r (Fin.last n)
    bundle := rvPullback_last_coordinate_bundle _ (regularization_rvPullback A hRP) _ hLeading
    exceptional := E
    exceptional_subset := hEA
    exceptional_dim := hDim
    unitDerivative := hUnit },regularization_rvPullback A hRP⟩

end DiamondIntegral.Section6
