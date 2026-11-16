import «section 6».CarriedMapDerivatives
import «section 6».StandardContractionStages

/-! Literal target changes preserve actual stage homeomorphisms and
total derivatives. Carried maps also retain every prescribed old label
and preserve the relative-coordinate condition on actual VF points. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem ProperCovariantHomeomorphism.changeMapTarget
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B C : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B}
    (h : ProperCovariantHomeomorphism f) (he : B=C) :
    ProperCovariantHomeomorphism (changeMapTarget f he) := by
  cases he
  exact h

theorem HasMixedUnitDerivativeAt.changeMapTarget
    {A : DefSet (rawMixedSpace (M := M) n r) S}
    {B C : DefSet (rawMixedSpace (M := M) n s) S} {f : Map A B} {p : A}
    (h : HasMixedUnitDerivativeAt f p) (he : B=C) :
    HasMixedUnitDerivativeAt (changeMapTarget f he) p := by
  cases he
  exact h

theorem carryLastMap_retains_labels
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (k : Fin r) (l : Fin s) (hLabels : ∀ p : A,(f p).val.2 l=p.val.2 k)
    (π : Fin r → Fin s) (hRetained : ∀ p : A,∀ i,(f p).val.2 (π i)=p.val.2 i)
    (p : rvCoordinateBundle A k) (i : Fin r) :
    (carryLastMap f k l hLabels p).val.2 (π i)=p.val.2 i := by
  rw [carryLastMap_value]
  exact hRetained (bundleProjection A k p) i

theorem carryLastMap_relative
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (k : Fin r) (l : Fin s) (hLabels : ∀ p : A,(f p).val.2 l=p.val.2 k)
    (j : Fin n) (hRelative : ∀ p : A,∀ i,i ≠ j → (f p).val.1 i=p.val.1 i)
    (p : rvCoordinateBundle A k) (i : Fin (n+1)) (hi : i ≠ j.castSucc) :
    (carryLastMap f k l hLabels p).val.1 i=p.val.1 i := by
  refine Fin.lastCases ?_ (fun a => ?_) i hi
  · intro hLast
    exact carryLastMap_fixed f k l hLabels p
  · intro hNe
    have haj : a ≠ j := fun h => hNe (congrArg Fin.castSucc h)
    have h := hRelative (bundleProjection A k p) a haj
    change (f (bundleProjection A k p)).val.1 a=p.val.1 a.castSucc at h
    simpa only [carryLastMap_value,Fin.snoc_castSucc] using h

end DiamondIntegral.Section6
