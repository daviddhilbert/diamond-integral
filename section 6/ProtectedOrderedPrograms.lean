import «section 6».FixedVFStagePrecomposition
import «section 6».ProperMembershipGrafting
import «section 6».OrderedContractionLiftProperties

/-! Single-source ordered existence implies simultaneous preparation
of every finite proper family, by retaining its actual membership labels
and absorbing their graft into the first stage. No special-bijection
claim is made about the graft. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 18000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r k q : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure ProtectedOrderedProgram (A : DefSet (rawMixedSpace (M := M) n r) S)
    (C : Fin k → DefSet (rawMixedSpace (M := M) n r) S) where
  arity : ℕ
  target : DefSet (rawMixedSpace (M := M) 0 arity) S
  program : OrderedStandardContractionProgram (G := G) S A target
  pieceIndex : Fin k → Fin arity
  membership : ∀ p : A,∀ i,p.val ∈ (C i).carrier ↔ (program.toMap p).val.2 (pieceIndex i)=branchTag (M := M) true

theorem ProtectedOrderedProgram.protected_images_rvPullback
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {C : Fin k → DefSet (rawMixedSpace (M := M) n r) S}
    (T : ProtectedOrderedProgram (G := G) A C) (V : OrderedStandardContractionLift T.program)
    (hCA : ∀ i,(C i).carrier ⊆ A.carrier) (i : Fin k) :
    IsRVPullback (V.map.restrict (hCA i)).image.carrier := by
  apply restricted_image_rvPullback_of_retained_tag V.map V.home.bijective (hCA i) (T.pieceIndex i) ?_ V.pullback
  intro p
  rw [V.labels]
  exact T.membership p i

def protectedOrderedProgram_of_grafted_program
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) (hA : ProperInvariant S A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) (n+1) r) S) (hC : ∀ i,ProperInvariant S (C i).carrier)
    {U : DefSet (rawMixedSpace (M := M) 0 q) S}
    (T : OrderedStandardContractionProgram (G := G) S (graftMap hc (properMembershipLabels A C)).image U) :
    ProtectedOrderedProgram (G := G) A C := by
  let τ := properMembershipLabels A C
  let g := graft hc τ
  have hτ := properMembershipLabels_properCovariant h00 hc hκ hs hv A hA C hC
  have hG := graft_properHomeomorphism h00 hc linear hκ hs hv hsmall hΓ τ hA hτ
  have hVF (p : A) : (g p).val.1=p.val.1 := rfl
  have hRetain (p : A) (i : Fin r) : (g p).val.2 (Fin.castAdd k i)=p.val.2 i := by
    simp only [g,graft_apply,Fin.append_left]
  have hUnit (p : A) : HasMixedUnitDerivativeAt g p := graft_unit_derivative hc hv τ hτ p
  let P := T.precomposeFixedVF h00 hc linear hκ hs hv hsmall hΓ g hG hVF (Fin.castAdd k)
    (Fin.castAdd_injective r k) hRetain hUnit
  refine {
    arity := q
    target := U
    program := P
    pieceIndex := fun i => T.oldLabels (Fin.natAdd r i)
    membership := ?_ }
  intro p i
  have hMap := T.precomposeFixedVF_toMap h00 hc linear hκ hs hv hsmall hΓ g hG hVF (Fin.castAdd k)
    (Fin.castAdd_injective r k) hRetain hUnit
  change p.val ∈ (C i).carrier ↔ (P.toMap p).val.2 (T.oldLabels (Fin.natAdd r i))=branchTag (M := M) true
  rw [hMap]
  change p.val ∈ (C i).carrier ↔ (T.toMap (g p)).val.2 (T.oldLabels (Fin.natAdd r i))=branchTag (M := M) true
  rw [T.retained]
  exact properMembershipGraft_mem_iff h00 hc A C p i

end DiamondIntegral.Section6
