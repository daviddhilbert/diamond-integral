import «section 6».RetainedRVTags
import «section 6».UnaryContextLifts

/-! Track the VF displacement determined by the final retained RV
labels. Unary base preparations have this property; it survives
composition and their actual lifts to higher-dimensional ambients. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 10000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {C : DefSet (rawMixedSpace (M := M) n t) S}

def RVCoordinateDisplacement (f : Map A B) (i : Fin n) : Prop :=
  ∀ p z : A,(f p).val.2=(f z).val.2 →
    (f p).val.1 i-p.val.1 i=(f z).val.1 i-z.val.1 i

theorem RVCoordinateDisplacement.of_fixed {f : Map A B} (i : Fin n)
    (hFixed : ∀ p : A,(f p).val.1 i=p.val.1 i) : RVCoordinateDisplacement f i := by
  intro p z _
  rw [hFixed,hFixed,sub_self,sub_self]

theorem RVCoordinateDisplacement.comp {f : Map A B} {g : Map B C} {i : Fin n}
    (hf : RVCoordinateDisplacement f i) (hg : RVCoordinateDisplacement g i)
    (π : Fin s → Fin t) (hRetain : ∀ p : B,∀ j,(g p).val.2 (π j)=p.val.2 j) :
    RVCoordinateDisplacement (g.comp f) i := by
  intro p z he
  have hTags : (f p).val.2=(f z).val.2 := by
    funext j
    exact (hRetain (f p) j).symm.trans ((congrFun he (π j)).trans (hRetain (f z) j))
  have hF := hf p z hTags
  have hG := hg (f p) (f z) he
  change (g (f p)).val.1 i-p.val.1 i=(g (f z)).val.1 i-z.val.1 i
  calc
    _ = ((g (f p)).val.1 i-(f p).val.1 i)+((f p).val.1 i-p.val.1 i) := by abel
    _ = ((g (f z)).val.1 i-(f z).val.1 i)+((f z).val.1 i-z.val.1 i) := by rw [hF,hG]
    _ = _ := by abel

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem CentripetalData.rv_displacement_of_rv_focus (h00 : M ⊨ Axioms.ACVF00)
    (D : CentripetalData (G := G) A)
    (hFocus : ∀ p z : A,p.val.2=z.val.2 → D.extendedFocus p.val=D.extendedFocus z.val)
    (i : Fin n) : RVCoordinateDisplacement D.bijection i := by
  intro p z he
  change (D.point p.val).2=(D.point z.val).2 at he
  have hOld : p.val.2=z.val.2 := by
    funext j
    simpa only [CentripetalData.point,Fin.append_right] using congrFun he (Fin.natAdd 1 j)
  have hCore : D.core p.val=D.core z.val := by
    apply branchTag_injective h00
    simpa only [CentripetalData.point,Fin.append_left] using congrFun he (Fin.castAdd r (0 : Fin 1))
  have hF := hFocus p z hOld
  change (D.point p.val).1 i-p.val.1 i=(D.point z.val).1 i-z.val.1 i
  by_cases hi : i=D.coordinate
  · subst i
    simp only [CentripetalData.point,Function.update_self]
    rw [hCore,hF]
    abel
  · simp only [CentripetalData.point,Function.update_of_ne hi,sub_self]

theorem ZeroCenteredData.rv_displacement (h00 : M ⊨ Axioms.ACVF00)
    (D : ZeroCenteredData A) (i : Fin n) : RVCoordinateDisplacement D.bijection i := by
  intro p z he
  change (D.point p.val).2=(D.point z.val).2 at he
  have hCore : D.core p.val=D.core z.val := by
    funext j
    apply branchTag_injective h00
    simpa only [ZeroCenteredData.point,ZeroCenteredData.tags,Fin.append_left] using congrFun he (Fin.castAdd r j)
  change (p.val.1 i+D.shift (D.core p.val) i)-p.val.1 i=(z.val.1 i+D.shift (D.core z.val) i)-z.val.1 i
  simp only [Pi.add_apply,hCore]
  abel

theorem SpecialCovariantChain.unary_rv_displacement
    (h00 : M ⊨ Axioms.ACVF00)
    {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
    {f : Map A B} (H : SpecialCovariantChain (G := G) A B f) (i : Fin 1) :
    RVCoordinateDisplacement f i := by
  induction H with
  | identity A hA => exact .of_fixed i (fun _ => rfl)
  | regularize A hA hD => exact .of_fixed i (fun _ => rfl)
  | centripetal A D =>
    apply D.rv_displacement_of_rv_focus h00
    intro p z hTags
    apply D.extendedFocus_same_other p.property z.property hTags
    intro j hj
    exact False.elim (hj (Subsingleton.elim _ _))
  | zeroCentered A D => exact D.rv_displacement h00 i
  | comp hf hg ihf ihg =>
    obtain ⟨hrs,hRetain⟩ := hg.retainsRV
    exact ihf.comp ihg (rvTailIndex hrs) hRetain

end DiamondIntegral.Section6
