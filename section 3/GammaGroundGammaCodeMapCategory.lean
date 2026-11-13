import «section 3».GammaGroundGammaCodeDescent
import «section 3».GammaGroundGammaProducts
import «section 3».GammaGroundFamilyMaps
/-! An auxiliary category retains actual full-code maps and their
quotient compatibility. Its isomorphisms supply the original Gamma
morphisms whenever the two recorded degrees agree. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]

structure GammaGroundGammaCodeObject (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) where
  degree : ℕ
  obj : GammaGroundGammaObject hc ground degree

variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

structure GammaGroundGammaCodeMap (A B : GammaGroundGammaCodeObject hc ground) where
  map : GammaGroundFamilyMap A.obj.codeLift B.obj.codeLift
  respects : ∀ c d, A.obj.decode c = A.obj.decode d → B.obj.decode (map.toFun c) = B.obj.decode (map.toFun d)

@[ext] theorem GammaGroundGammaCodeMap.ext {A B : GammaGroundGammaCodeObject hc ground} {f g : GammaGroundGammaCodeMap A B}
    (h : f.map = g.map) : f = g := by cases f; cases g; cases h; rfl

instance gammaGroundGammaCodeMapCategory : Category (GammaGroundGammaCodeObject hc ground) where
  Hom := GammaGroundGammaCodeMap
  id A := ⟨GammaGroundFamilyMap.id A.obj.codeLift, fun _ _ h => h⟩
  comp f g := ⟨g.map.comp f.map, fun c d h => g.respects _ _ (f.respects c d h)⟩
  id_comp f := by apply GammaGroundGammaCodeMap.ext; apply GammaGroundFamilyMap.ext; rfl
  comp_id f := by apply GammaGroundGammaCodeMap.ext; apply GammaGroundFamilyMap.ext; rfl
  assoc f g h := by apply GammaGroundGammaCodeMap.ext; apply GammaGroundFamilyMap.ext; rfl

def GammaGroundGammaCodeObject.product (A B : GammaGroundGammaCodeObject hc ground) : GammaGroundGammaCodeObject hc ground :=
  ⟨A.degree + B.degree, A.obj.product B.obj⟩

def GammaGroundGammaCodeObject.unit (hc : CanonicalStructure.IsCanonical (M := M)) (ground : GammaParameters.Base (M := M)) : GammaGroundGammaCodeObject hc ground :=
  ⟨0, GammaGroundGammaObject.unit hc ground⟩

def gammaGroundGammaCodeBijectionOfIso {A B : GammaGroundGammaCodeObject hc ground} (e : A ≅ B) : GammaGroundFamilyBijection A.obj.codeLift B.obj.codeLift where
  equiv := Equiv.ofBijective e.hom.map.toFun (by
    have hl : Function.LeftInverse e.inv.map.toFun e.hom.map.toFun := fun c =>
      congrArg (fun f : A ⟶ A => f.map.toFun c) e.hom_inv_id
    have hr : Function.RightInverse e.inv.map.toFun e.hom.map.toFun := fun c =>
      congrArg (fun f : B ⟶ B => f.map.toFun c) e.inv_hom_id
    exact ⟨hl.injective, hr.surjective⟩)
  definable := e.hom.map.definable

theorem gammaGroundGammaCodeIso_kernel {A B : GammaGroundGammaCodeObject hc ground} (e : A ≅ B) (c d : A.obj.codeLift.Carrier) :
    A.obj.decode c = A.obj.decode d ↔
      B.obj.decode ((gammaGroundGammaCodeBijectionOfIso e).equiv c) = B.obj.decode ((gammaGroundGammaCodeBijectionOfIso e).equiv d) := by
  constructor
  · exact e.hom.respects c d
  · intro h
    have ht := e.inv.respects _ _ h
    have hc' := congrArg (fun f : A ⟶ A => f.map.toFun c) e.hom_inv_id
    have hd' := congrArg (fun f : A ⟶ A => f.map.toFun d) e.hom_inv_id
    change e.inv.map.toFun (e.hom.map.toFun c) = c at hc'
    change e.inv.map.toFun (e.hom.map.toFun d) = d at hd'
    change A.obj.decode (e.inv.map.toFun (e.hom.map.toFun c)) = A.obj.decode (e.inv.map.toFun (e.hom.map.toFun d)) at ht
    rw [hc', hd'] at ht
    exact ht

def gammaGroundGammaHomOfCodeIso {A B : GammaGroundGammaCodeObject hc ground} (e : A ≅ B) (h : A.degree = B.degree) :
    GammaGroundGammaHom A.obj (h.symm ▸ B.obj) := by
  obtain ⟨m, A⟩ := A
  obtain ⟨n, B⟩ := B
  dsimp only at h
  subst n
  exact GammaGroundGammaHom.ofCodeBijection (gammaGroundGammaCodeBijectionOfIso e) (gammaGroundGammaCodeIso_kernel e)

end DiamondIntegral.Section3
