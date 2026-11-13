import «section 3».GammaGroundFiniteFamilies
import «section 3».GammaGroundCarrierBijections
import «section 3».GammaGroundMapRelations
/-! Definable finite-gammaGroundFamily maps with a prescribed tag map, including
actual tag permutations and disjoint unions. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q : Space LRV M}

def GammaGroundFiniteFamily.coprod (A B : GammaGroundFiniteFamily hc ground P) : GammaGroundFiniteFamily hc ground P :=
  ⟨A.tags + B.tags, Fin.addCases A.piece B.piece⟩

def gammaGroundFamilyTaggedMap (A : GammaGroundFiniteFamily hc ground P) (B : GammaGroundFiniteFamily hc ground Q)
    (h : Fin A.tags → Fin B.tags) (f : ∀ i, GammaGroundMap (A.piece i) (B.piece (h i))) : A.Carrier → B.Carrier :=
  fun a => ⟨h a.1, f a.1 a.2⟩

theorem gammaGroundFamilyTaggedMap_definable (A : GammaGroundFiniteFamily hc ground P) (B : GammaGroundFiniteFamily hc ground Q)
    (h : Fin A.tags → Fin B.tags) (f : ∀ i, GammaGroundMap (A.piece i) (B.piece (h i))) :
    GammaGroundFamilyDefinable A B (gammaGroundFamilyTaggedMap A B h f) := by
  classical
  intro i j
  by_cases he : h i = j
  · subst j
    exact (f i).relation_definable.congr (by
      intro x y
      constructor
      · rintro ⟨a, rfl, hy⟩
        exact ⟨a, f i a, rfl, hy, rfl⟩
      · rintro ⟨a, b, rfl, rfl, hab⟩
        have hfb : f i a = b := eq_of_heq (Sigma.mk.inj_iff.mp hab).2
        exact ⟨a, rfl, congrArg Subtype.val hfb⟩)
  · have hd : GammaGroundRelationDefinable hc ground P Q (fun _ _ => False) := by
      exact (GammaGroundDefSet.empty hc ground (P.prod Q)).definable
    exact hd.congr (by
      intro x y
      constructor
      · exact False.elim
      · rintro ⟨a, b, _, _, hab⟩
        exact he (congrArg Sigma.fst hab))

def gammaGroundFamilyBijectionOfTagEquiv (A : GammaGroundFiniteFamily hc ground P) (B : GammaGroundFiniteFamily hc ground Q)
    (e : Fin A.tags ≃ Fin B.tags) (f : ∀ i, GammaGroundBijection (A.piece i) (B.piece (e i))) :
    GammaGroundFamilyBijection A B where
  equiv := (Equiv.sigmaCongrRight (fun i => Equiv.ofBijective (f i).map (f i).bijective)).trans
    (Equiv.sigmaCongrLeft (β := fun j => B.piece j) e)
  definable := gammaGroundFamilyTaggedMap_definable A B e (fun i => (f i).map)

@[simp] theorem gammaGroundFamilyBijectionOfTagEquiv_apply (A : GammaGroundFiniteFamily hc ground P) (B : GammaGroundFiniteFamily hc ground Q)
    (e : Fin A.tags ≃ Fin B.tags) (f : ∀ i, GammaGroundBijection (A.piece i) (B.piece (e i))) (a : A.Carrier) :
    (gammaGroundFamilyBijectionOfTagEquiv A B e f).equiv a = ⟨e a.1, (f a.1).map a.2⟩ := rfl

end DiamondIntegral.Section3
