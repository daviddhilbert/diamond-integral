import «section 3».CompletionDirectSum
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Limits

set_option autoImplicit false
noncomputable section
namespace DiamondIntegral.Section3
open Algebra.GrothendieckAddGroup CategoryTheory
universe u
variable {A B D : Type u} [AddCommMonoid A] [AddCommMonoid B] [AddCommMonoid D]

def additiveCompletionMap (f : A →+ B) : Algebra.GrothendieckAddGroup A →+ Algebra.GrothendieckAddGroup B :=
  lift (of.comp f)

@[simp] theorem additiveCompletionMap_of (f : A →+ B) (a : A) :
    additiveCompletionMap f (of a) = of (f a) := lift_apply_of _ _

theorem additiveCompletionMap_id : additiveCompletionMap (AddMonoidHom.id A) = AddMonoidHom.id _ := by
  apply completionAddHom_ext
  intro a
  exact additiveCompletionMap_of _ a

theorem additiveCompletionMap_comp (f : A →+ B) (g : B →+ D) :
    additiveCompletionMap (g.comp f) = (additiveCompletionMap g).comp (additiveCompletionMap f) := by
  apply completionAddHom_ext
  intro a
  simp only [additiveCompletionMap_of, AddMonoidHom.comp_apply]

def additiveCompletionFunctor : AddCommMonCat.{u} ⥤ AddCommGrpCat.{u} where
  obj A := AddCommGrpCat.of (Algebra.GrothendieckAddGroup A)
  map f := AddCommGrpCat.ofHom (additiveCompletionMap f.hom)
  map_id A := by
    apply AddCommGrpCat.hom_ext
    exact additiveCompletionMap_id
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    exact additiveCompletionMap_comp f.hom g.hom

def additiveCompletionHomEquiv (A : AddCommMonCat.{u}) (G : AddCommGrpCat.{u}) :
    (additiveCompletionFunctor.obj A ⟶ G) ≃ (A ⟶ (forget₂ AddCommGrpCat AddCommMonCat).obj G) where
  toFun f := AddCommMonCat.ofHom (f.hom.comp of)
  invFun f := AddCommGrpCat.ofHom (lift (G := G) f.hom)
  left_inv f := by
    apply AddCommGrpCat.hom_ext
    apply completionAddHom_ext
    intro a
    exact lift_apply_of _ a
  right_inv f := by
    apply AddCommMonCat.hom_ext
    exact AddMonoidHom.ext (lift_apply_of (G := G) f.hom)

def additiveCompletionAdjunction : additiveCompletionFunctor.{u} ⊣ forget₂ AddCommGrpCat AddCommMonCat :=
  Adjunction.mkOfHomEquiv {
    homEquiv := additiveCompletionHomEquiv
    homEquiv_naturality_left_symm := by
      intro A' A G f g
      apply AddCommGrpCat.hom_ext
      apply completionAddHom_ext
      intro a
      change lift (G := G) (g.hom.comp f.hom) (of a) = lift (G := G) g.hom (additiveCompletionMap f.hom (of a))
      rw [lift_apply_of, additiveCompletionMap_of, lift_apply_of]
      rfl
    homEquiv_naturality_right := by
      intro A G G' f g
      apply AddCommMonCat.hom_ext
      rfl }

instance additiveCompletionFunctorLeftAdjoint : additiveCompletionFunctor.{u}.IsLeftAdjoint :=
  additiveCompletionAdjunction.isLeftAdjoint

end DiamondIntegral.Section3
