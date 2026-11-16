import «section 6».CarriedMapProperGeometry
import «section 6».PaddedLiftDerivatives

/-! The full total derivative of an arbitrary carried map has the old
head derivative and an identity block on the fixed VF coordinate. Its
determinant is exactly the original determinant. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

theorem carryLastMap_derivative_and_det
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hA : ProperInvariant S A.carrier) (k : Fin r) (l : Fin s)
    (hLabels : ∀ p : A,(f p).val.2 l=p.val.2 k) (p : rvCoordinateBundle A k)
    {L : (Fin n → VF M) →ₗ[VF M] (Fin n → VF M)}
    (hL : HasMixedVFDerivativeAt f (bundleProjection A k p) L) :
    ∃ D,HasMixedVFDerivativeAt (carryLastMap f k l hLabels) p D ∧
      (LinearMap.toMatrix' D).det=(LinearMap.toMatrix' L).det := by
  obtain ⟨F,⟨ρ,hρ⟩,hF⟩ := hL
  have hF' : HasVFDerivativeAt F (p.val.1 ∘ productLeft n 1) L := hF
  obtain ⟨D,hD⟩ := vfdifferentiableAt_carryIdentityTail F p.val.1 ⟨L,hF'⟩
  have hW := rvCoordinateBundle_properInvariant h00 hc hκ hs hv A k hA
  obtain ⟨σ,hσ⟩ := exists_vfBall_subset_nhds hv p.val.1
    ((hW.clopen_fibres hv p.val.2).isOpen.mem_nhds p.property)
  refine ⟨D,⟨carryIdentityTail F 1,⟨max σ ρ,fun z hz => ?_⟩,hD⟩,
    carryIdentityTail_derivative_det F p.val.1 hD hF'⟩
  have hzW := hσ (vfBall_anti (le_max_left σ ρ) hz)
  let q : rvCoordinateBundle A k := ⟨(z,p.val.2),hzW⟩
  have hzHead : Fin.init z ∈ vfBall (bundleProjection A k p).val.1 ρ :=
    fun i => (vfBall_anti (le_max_right σ ρ) hz) i.castSucc
  obtain ⟨hzA,hValue⟩ := hρ (Fin.init z) hzHead
  have hq : bundleProjection A k q=⟨(Fin.init z,(bundleProjection A k p).val.2),hzA⟩ := Subtype.ext rfl
  refine ⟨hzW,?_⟩
  change (carryLastMap f k l hLabels q).val=_
  rw [carryLastMap_value,hq,hValue,carryLastMap_value]
  have hTail : z ∘ productRight n 1=(fun _ : Fin 1 => z (Fin.last n)) := by
    funext i
    fin_cases i
    rfl
  change (Fin.snoc (F (Fin.init z)) (z (Fin.last n)),(f (bundleProjection A k p)).val.2)=
    (productTuple (F (z ∘ productLeft n 1)) (z ∘ productRight n 1),(f (bundleProjection A k p)).val.2)
  rw [hTail,productTuple_singleton_eq_snoc]
  rfl

theorem carryLastMap_unit_derivative
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hA : ProperInvariant S A.carrier) (k : Fin r) (l : Fin s)
    (hLabels : ∀ p : A,(f p).val.2 l=p.val.2 k) (p : rvCoordinateBundle A k)
    (hUnit : HasMixedUnitDerivativeAt f (bundleProjection A k p)) :
    HasMixedUnitDerivativeAt (carryLastMap f k l hLabels) p := by
  obtain ⟨L,hL,hDet⟩ := hUnit
  obtain ⟨D,hD,hEqual⟩ := carryLastMap_derivative_and_det h00 hc hκ hs hv f hA k l hLabels p hL
  exact ⟨D,hD,hEqual.trans hDet⟩

end DiamondIntegral.Section6
