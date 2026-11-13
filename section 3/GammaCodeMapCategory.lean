import «section 3».GammaCodeDescent
import «section 3».GammaProducts
import «section 3».FamilyMaps

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

structure GammaCodeObject (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) where
  degree : ℕ
  obj : GammaObject hc S degree

variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M}

structure GammaCodeMap (A B : GammaCodeObject hc S) where
  map : FamilyMap A.obj.codeLift B.obj.codeLift
  respects : ∀ c d, A.obj.decode c = A.obj.decode d → B.obj.decode (map.toFun c) = B.obj.decode (map.toFun d)

@[ext] theorem GammaCodeMap.ext {A B : GammaCodeObject hc S} {f g : GammaCodeMap A B}
    (h : f.map = g.map) : f = g := by cases f; cases g; cases h; rfl

instance gammaCodeMapCategory : Category (GammaCodeObject hc S) where
  Hom := GammaCodeMap
  id A := ⟨FamilyMap.id A.obj.codeLift, fun _ _ h => h⟩
  comp f g := ⟨g.map.comp f.map, fun c d h => g.respects _ _ (f.respects c d h)⟩
  id_comp f := by apply GammaCodeMap.ext; apply FamilyMap.ext; rfl
  comp_id f := by apply GammaCodeMap.ext; apply FamilyMap.ext; rfl
  assoc f g h := by apply GammaCodeMap.ext; apply FamilyMap.ext; rfl

def GammaCodeObject.product (A B : GammaCodeObject hc S) : GammaCodeObject hc S :=
  ⟨A.degree + B.degree, A.obj.product B.obj⟩

def GammaCodeObject.unit (hc : CanonicalStructure.IsCanonical (M := M)) (S : Set M) : GammaCodeObject hc S :=
  ⟨0, GammaObject.unit hc S⟩

def gammaCodeBijectionOfIso {A B : GammaCodeObject hc S} (e : A ≅ B) : FamilyBijection A.obj.codeLift B.obj.codeLift where
  equiv := Equiv.ofBijective e.hom.map.toFun (by
    have hl : Function.LeftInverse e.inv.map.toFun e.hom.map.toFun := fun c =>
      congrArg (fun f : A ⟶ A => f.map.toFun c) e.hom_inv_id
    have hr : Function.RightInverse e.inv.map.toFun e.hom.map.toFun := fun c =>
      congrArg (fun f : B ⟶ B => f.map.toFun c) e.inv_hom_id
    exact ⟨hl.injective, hr.surjective⟩)
  definable := e.hom.map.definable

theorem gammaCodeIso_kernel {A B : GammaCodeObject hc S} (e : A ≅ B) (c d : A.obj.codeLift.Carrier) :
    A.obj.decode c = A.obj.decode d ↔
      B.obj.decode ((gammaCodeBijectionOfIso e).equiv c) = B.obj.decode ((gammaCodeBijectionOfIso e).equiv d) := by
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

def gammaHomOfCodeIso {A B : GammaCodeObject hc S} (e : A ≅ B) (h : A.degree = B.degree) :
    GammaHom A.obj (h.symm ▸ B.obj) := by
  obtain ⟨m, A⟩ := A
  obtain ⟨n, B⟩ := B
  dsimp only at h
  subst n
  exact GammaHom.ofCodeBijection (gammaCodeBijectionOfIso e) (gammaCodeIso_kernel e)

end DiamondIntegral.Section3
