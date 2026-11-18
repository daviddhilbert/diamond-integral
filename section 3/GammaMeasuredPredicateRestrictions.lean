import «section 3».GammaFullMeasuredRestrictions

/-! A full measured bijection restricts to any two corresponding
original-ground predicates. Generic measure is inherited by the actual
restricted point map. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] [CharZero (Section2.VF M)]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : GammaParameters.Base (M := M)} {k : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]

def gammaMeasuredPredicateRestriction
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {U V : GammaGroundMeasuredVFData hc B k} (F : GammaFullMeasuredBijection U V)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) k U.arity)) (hA : A.carrier ⊆ U.domain.carrier)
    (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) k V.arity)) (hD : D.carrier ⊆ V.domain.carrier)
    (hMem : ∀ p : U.domain, (F.map.map p).val ∈ D.carrier ↔ p.val ∈ A.carrier) :
    GammaFullMeasuredBijection (U.restrict A hA) (V.restrict D hD) := by
  let g : GammaGroundMap A D := (F.map.map.restrict hA).corestrict
    (fun p => (hMem ⟨p.val,hA p.property⟩).mpr p.property)
  have hg : Function.Bijective g := by
    constructor
    · intro p q hpq
      apply Subtype.ext
      have h : F.map.map ⟨p.val,hA p.property⟩ = F.map.map ⟨q.val,hA q.property⟩ :=
        Subtype.ext (congrArg (fun r : D => r.val) hpq)
      exact congrArg (fun r : U.domain => r.val) (F.map.bijective.1 h)
    · intro q
      obtain ⟨p,hp⟩ := F.map.bijective.2 ⟨q.val,hD q.property⟩
      have hmem : p.val ∈ A.carrier := (hMem p).mp (by
        exact (congrArg (fun r : V.domain => r.val) hp).symm ▸ q.property)
      exact ⟨⟨p.val,hmem⟩,Subtype.ext (congrArg (fun r : V.domain => r.val) hp)⟩
  exact gammaFullMeasuredRestriction hκ hs hr hv F A hA D hD ⟨g,hg⟩ (fun _ => rfl)

theorem gammaMeasuredPredicateRestriction_value
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hr : Cardinal.mk B.real < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {U V : GammaGroundMeasuredVFData hc B k} (F : GammaFullMeasuredBijection U V)
    (A : GammaGroundDefSet hc B (rawMixedSpace (M := M) k U.arity)) (hA : A.carrier ⊆ U.domain.carrier)
    (D : GammaGroundDefSet hc B (rawMixedSpace (M := M) k V.arity)) (hD : D.carrier ⊆ V.domain.carrier)
    (hMem : ∀ p : U.domain, (F.map.map p).val ∈ D.carrier ↔ p.val ∈ A.carrier)
    (p : (U.restrict A hA).domain) :
    ((gammaMeasuredPredicateRestriction hκ hs hr hv F A hA D hD hMem).map.map p).val =
      (F.map.map ⟨p.val,hA p.property⟩).val := rfl

end DiamondIntegral.Section3
