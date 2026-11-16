import «section 6».SelectedGammaFormDescent
import «section 6».UnaryParameterFreezing

/-! Freezing every actual Gamma level retains exact agreement with
all local fibre forms after the entire parameter map is updated. Source
points and their precise unary base points are transported explicitly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.SelectedProgramContext
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q k d : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}
variable (X : SelectedProgramContext η A P C π σ)

theorem baseMap_same_source {η' : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
    (Y : SelectedProgramContext η' A P C π σ) (p : C) : Y.baseMap p=X.baseMap p :=
  Subtype.ext ((Y.baseMap_value p).trans (X.baseMap_value p).symm)

theorem frozen_source_form_agreement
    {W : DefSet (rawMixedSpace (M := M) (n+1) d) S} (D : FMT.FocusFreezingData W)
    (hB : ∀ E : D.balls,FMT.CoordinateProductDomain B.carrier (FMT.vfOpenBall E.val) (D.centers E) 0)
    (Y : SelectedProgramContext (D.unaryParameter hB η) A P C π σ)
    (ζ : ∀ b : B,Map (A.fibre (unaryFamilyParameter η b))
      (DefSet.univ (rawGammaPresentation (M := M)) (S ∪ Set.range (unaryFamilyParameter η b))))
    (ω : Map C (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hForm : ∀ p : C,gammaFormExtension (ζ (X.baseMap p)) (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val)
    (hProducts : ∀ γ,∀ E : D.balls,FMT.CoordinateProductDomain
      {p | p ∈ C.carrier ∧ gammaFormExtension ω p=γ} (FMT.vfOpenBall E.val) (D.centers E) 0) :
    ∀ p : C,gammaFormExtension (ζ (D.unaryBaseFreeze hB (Y.baseMap p)))
      (Fin.tail p.val.1,p.val.2 ∘ σ)=(ω p).val := by
  intro p
  have hMem := FMT.mixedFamilyFreeze_mapsTo D.balls D.centers (0 : Fin (n+1))
    {x | x ∈ C.carrier ∧ gammaFormExtension ω x=(ω p).val} D.separated (hProducts (ω p).val)
    (show p.val ∈ {x | x ∈ C.carrier ∧ gammaFormExtension ω x=(ω p).val} from
      ⟨p.property,gammaFormExtension_at ω p⟩)
  let p' : C := ⟨FMT.mixedFamilyFreeze D.balls D.centers 0 p.val,hMem.1⟩
  have hBase : X.baseMap p'=D.unaryBaseFreeze hB (Y.baseMap p) := by
    apply Subtype.ext
    rw [X.baseMap_value]
    apply Prod.ext
    · funext i
      fin_cases i
      have hOld := congrArg (fun b : B => b.val.1 0) (X.baseMap_same_source Y p)
      change (Y.baseMap p).val.1 0=(X.baseMap p).val.1 0 at hOld
      rw [X.baseMap_value] at hOld
      change FMT.vfFamilyFreeze D.balls D.centers (p.val.1 0)=
        FMT.vfFamilyFreeze D.balls D.centers ((Y.baseMap p).val.1 0)
      rw [hOld]
      rfl
    · have h := congrArg Prod.snd (Y.baseMap_value p)
      exact h.symm
  have hLocal : (Fin.tail p'.val.1,p'.val.2 ∘ σ)=(Fin.tail p.val.1,p.val.2 ∘ σ) := by
    apply Prod.ext
    · funext i
      change Function.update p.val.1 0 (FMT.vfFamilyFreeze D.balls D.centers (p.val.1 0)) i.succ=p.val.1 i.succ
      rw [Function.update_of_ne (Fin.succ_ne_zero i)]
    · rfl
  have h := hForm p'
  rw [hBase,hLocal] at h
  have hValue : (ω p').val=(ω p).val := (gammaFormExtension_at ω p').symm.trans hMem.2
  exact h.trans hValue

end DiamondIntegral.Section6.SelectedProgramContext
