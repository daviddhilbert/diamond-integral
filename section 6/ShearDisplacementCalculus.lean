import «section 6».RelativeShearCharts
import «section 6».RVCoordinateDisplacements

/-! Fixed-label shear displacements survive composition in one active
coordinate. A chart described by an arbitrary erased-coordinate focus
has this property directly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {C : DefSet (rawMixedSpace (M := M) n t) S}

theorem SameLabelShearDisplacement.of_rv {f : Map A B} {j : Fin n}
    (h : RVCoordinateDisplacement f j) : SameLabelShearDisplacement f j :=
  fun p q _ hOut _ => h p q hOut

theorem SameLabelShearDisplacement.comp {f : Map A B} {g : Map B C} {j : Fin n}
    (hF : SameLabelShearDisplacement f j) (hG : SameLabelShearDisplacement g j)
    (hRelative : ∀ p : A,∀ i,i ≠ j → (f p).val.1 i=p.val.1 i)
    (π : Fin s → Fin t) (hRetain : ∀ p : B,∀ i,(g p).val.2 (π i)=p.val.2 i) :
    SameLabelShearDisplacement (g.comp f) j := by
  intro p q hInput hOutput hInactive
  have hMiddle : (f p).val.2=(f q).val.2 := by
    funext i
    exact (hRetain (f p) i).symm.trans ((congrFun hOutput (π i)).trans (hRetain (f q) i))
  have hOther (i) (hi : i ≠ j) : (f p).val.1 i=(f q).val.1 i := by
    rw [hRelative p i hi,hRelative q i hi,hInactive i hi]
  have h₁ := hF p q hInput hMiddle hInactive
  have h₂ := hG (f p) (f q) hMiddle hOutput hOther
  change (g (f p)).val.1 j-p.val.1 j=(g (f q)).val.1 j-q.val.1 j
  calc
    _=((g (f p)).val.1 j-(f p).val.1 j)+((f p).val.1 j-p.val.1 j) := by abel
    _=((g (f q)).val.1 j-(f q).val.1 j)+((f q).val.1 j-q.val.1 j) := by rw [h₁,h₂]
    _=_ := by abel

theorem sameLabelShearDisplacement_of_shear_value (f : Map A B) (j : Fin n)
    (focus : (Fin r → RVInfinity M) → (Fin s → RVInfinity M) → (Fin n → VF M) → VF M)
    (hValue : ∀ p : A,(f p).val.1=coordinateShear j (focus p.val.2 (f p).val.2) p.val.1) :
    SameLabelShearDisplacement f j := by
  intro p q hInput hOutput hInactive
  have hErase : Function.update p.val.1 j 0=Function.update q.val.1 j 0 := by
    funext i
    by_cases hi : i=j
    · subst i
      simp only [Function.update_self]
    · simpa only [Function.update_of_ne hi] using hInactive i hi
  rw [hValue p,hValue q]
  simp only [coordinateShear,Function.update_self]
  rw [hInput,hOutput,hErase]
  abel

end DiamondIntegral.Section6
