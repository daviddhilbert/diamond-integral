import «section 6».UnaryBaseFocusFreezing
import «section 6».UnaryIndexedMixedFamilies
import «section 6».RootFreezingGeometry

/-! Freeze the actual unary parameter map on its preserved domain.
Every complete program formula is thereby evaluated at the same new
parameter; all label-constant data and their uniform bounds are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.FMT.FocusFreezingData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q : ℕ}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S}
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

def unaryBaseFreeze (D : FMT.FocusFreezingData C)
    (hB : ∀ E : D.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (D.centers E) 0) :
    Map B B :=
  (FMT.mixedFamilyFreezeMap D.balls D.centers 0 D.separated D.balls_definable D.centers_definable B).corestrict
    (fun b => FMT.mixedFamilyFreeze_mapsTo D.balls D.centers 0 B.carrier D.separated hB b.property)

def unaryParameter (D : FMT.FocusFreezingData C)
    (hB : ∀ E : D.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (D.centers E) 0)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) :
    Map B (DefSet.univ (rawVFSpace (M := M) 1) S) := η.comp (D.unaryBaseFreeze hB)

theorem unaryBaseFreeze_labels (D : FMT.FocusFreezingData C)
    (hB : ∀ E : D.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (D.centers E) 0) (b : B) :
    (D.unaryBaseFreeze hB b).val.2=b.val.2 := rfl

theorem unaryParameter_value (D : FMT.FocusFreezingData C)
    (hB : ∀ E : D.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (D.centers E) 0)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)) (b : B) :
    unaryFamilyParameter (D.unaryParameter hB η) b=unaryFamilyParameter η (D.unaryBaseFreeze hB b) := rfl

theorem unaryParameter_rows_unchanged (D : FMT.FocusFreezingData C)
    (hB : ∀ E : D.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (D.centers E) 0)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (V : RVSetParameterTemplate (M := M) S 1 s)
    (hRows : ∀ b c : B,b.val.2=c.val.2 →
      (V.fibre (unaryFamilyParameter η b)).carrier=(V.fibre (unaryFamilyParameter η c)).carrier)
    (b : B) : (V.fibre (unaryFamilyParameter (D.unaryParameter hB η) b)).carrier=
      (V.fibre (unaryFamilyParameter η b)).carrier := hRows (D.unaryBaseFreeze hB b) b rfl

theorem unaryParameter_rows_constant (D : FMT.FocusFreezingData C)
    (hB : ∀ E : D.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (D.centers E) 0)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (V : RVSetParameterTemplate (M := M) S 1 s)
    (hRows : ∀ b c : B,b.val.2=c.val.2 →
      (V.fibre (unaryFamilyParameter η b)).carrier=(V.fibre (unaryFamilyParameter η c)).carrier)
    (b c : B) (hTags : b.val.2=c.val.2) :
    (V.fibre (unaryFamilyParameter (D.unaryParameter hB η) b)).carrier=
      (V.fibre (unaryFamilyParameter (D.unaryParameter hB η) c)).carrier :=
  hRows (D.unaryBaseFreeze hB b) (D.unaryBaseFreeze hB c) hTags

theorem unaryParameter_bound (D : FMT.FocusFreezingData C)
    (hB : ∀ E : D.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (D.centers E) 0)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (V : RVSetParameterTemplate (M := M) S 1 s) (γ : Gamma M)
    (hBound : ∀ b : B,∀ u ∈ (V.fibre (unaryFamilyParameter η b)).carrier,∀ i,
      (γ⁻¹).val ≤ Values.vrv (u i) ∧ Values.vrv (u i) ≤ γ.val) :
    ∀ b : B,∀ u ∈ (V.fibre (unaryFamilyParameter (D.unaryParameter hB η) b)).carrier,∀ i,
      (γ⁻¹).val ≤ Values.vrv (u i) ∧ Values.vrv (u i) ≤ γ.val :=
  fun b => hBound (D.unaryBaseFreeze hB b)

theorem unaryParameter_good (D : FMT.FocusFreezingData C)
    (hB : ∀ E : D.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (D.centers E) 0)
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (X : Set (Fin 1 → M)) (hGood : ∀ b : B,unaryFamilyParameter η b ∈ X) :
    ∀ b : B,unaryFamilyParameter (D.unaryParameter hB η) b ∈ X :=
  fun b => hGood (D.unaryBaseFreeze hB b)

theorem unaryFamilyBasePoint_freeze (D : FMT.FocusFreezingData C) (p : Mixed M (n+1) (r+s)) :
    unaryFamilyBasePoint (FMT.mixedFamilyFreeze D.balls D.centers 0 p)=
      FMT.mixedFamilyFreeze D.balls D.centers 0 (unaryFamilyBasePoint p) := by
  apply Prod.ext
  · funext i
    fin_cases i
    rfl
  · rfl

end DiamondIntegral.Section6.FMT.FocusFreezingData
