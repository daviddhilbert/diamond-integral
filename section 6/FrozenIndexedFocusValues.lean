import «section 6».UnaryIndexedFrozenFamilies
import «section 6».UnaryIndexedContinuousMaps

/-! The actual repaired focus is evaluated by the original focus
formula at the new unary parameter. This identifies the repaired first
component with the same simultaneous reparametrization of the full program. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.FMT.FocusFreezingData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) (r+s)) S}

theorem frozen_indexed_map_value (D : FMT.FocusFreezingData C)
    (hB : ∀ E : D.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (D.centers E) 0)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (F : ContinuousRVGraphTemplate (M := M) S 1 s n 1)
    (hBase : ∀ p ∈ C.carrier,unaryFamilyBasePoint p ∈ B.carrier)
    (hGood : ∀ p ∈ C.carrier,∀ b : B,unaryFamilyBasePoint p=b.val →
      unaryFamilyParameter η b ∈ F.good)
    (p : C) (b : B) (hb : unaryFamilyBasePoint p.val=b.val) :
    ∃ ha : unaryFamilyParameter (D.unaryParameter hB η) b ∈ F.good,
      (D.frozenMap (unaryIndexedFamilyMap η F C hBase hGood) p).val=
        F.value _ ha (p.val.2 ∘ Fin.natAdd r) (Fin.tail p.val.1) := by
  let fp : C := ⟨FMT.mixedFamilyFreeze D.balls D.centers 0 p.val,
    FMT.mixedFamilyFreeze_mapsTo D.balls D.centers 0 C.carrier D.separated D.product_domain p.property⟩
  have hBaseFp : unaryFamilyBasePoint fp.val=(D.unaryBaseFreeze hB b).val := by
    rw [D.unaryFamilyBasePoint_freeze,hb]
    rfl
  have ha := hGood fp.val fp.property (D.unaryBaseFreeze hB b) hBaseFp
  refine ⟨ha,?_⟩
  change (unaryIndexedFamilyMap η F C hBase hGood fp).val=_
  rw [unaryIndexedFamilyMap_value η F C hBase hGood fp (D.unaryBaseFreeze hB b) hBaseFp]
  have hTail : Fin.tail fp.val.1=Fin.tail p.val.1 := by
    funext i
    change Function.update p.val.1 0 (FMT.vfFamilyFreeze D.balls D.centers (p.val.1 0)) i.succ=p.val.1 i.succ
    exact Function.update_of_ne (Fin.succ_ne_zero i) _ _
  rw [hTail]
  rfl

end DiamondIntegral.Section6.FMT.FocusFreezingData
