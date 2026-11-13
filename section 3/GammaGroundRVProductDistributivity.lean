import «section 3».GammaGroundRVProductScissors
import «section 3».GammaGroundEmptyBijections

/-! Cartesian multiplication distributes over actual positive scissors
and hence over arbitrary fixed-degree positive classes. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k l : ℕ}

def gammaGroundRVCoprodLeftRestrictionIso (U V : GammaGroundRVObject hc ground k) :
    U ≅ (U.coprod V).restrict (gammaGroundRVLeftTag U.domain V.arity).image (fun _ h => Or.inl h) :=
  asIso (show _ ⟶ _ from ⟨(gammaGroundRVLeftTag U.domain V.arity).toImage,
    (gammaGroundRVLeftTag U.domain V.arity).toImage_bijective (gammaGroundRVLeftTag_injective U.domain V.arity)⟩)

def gammaGroundRVCoprodRightRestrictionIso (U V : GammaGroundRVObject hc ground k) :
    V ≅ (U.coprod V).restrict (gammaGroundRVRightTag V.domain U.arity).image (fun _ h => Or.inr h) :=
  asIso (show _ ⟶ _ from ⟨(gammaGroundRVRightTag V.domain U.arity).toImage,
    (gammaGroundRVRightTag V.domain U.arity).toImage_bijective (gammaGroundRVRightTag_injective V.domain U.arity)⟩)

theorem gammaGroundRVClass_product_coprod (U : GammaGroundRVObject hc ground k) (V W : GammaGroundRVObject hc ground l) :
    gammaGroundRVClass (U.product (V.coprod W)) = gammaGroundRVClass (U.product V) + gammaGroundRVClass (U.product W) := by
  let T := V.coprod W
  let B := (gammaGroundRVLeftTag V.domain W.arity).image
  let D := (gammaGroundRVRightTag W.domain V.arity).image
  have hB : B.carrier ⊆ T.domain.carrier := fun _ h => Or.inl h
  have hD : D.carrier ⊆ T.domain.carrier := fun _ h => Or.inr h
  have hp := gammaGroundRVClass_partition (U.product T)
    (gammaGroundRVProductDomain U.domain B) (gammaGroundRVProductDomain U.domain D)
    (gammaGroundRVProductRestrictionSubset U T B hB) (gammaGroundRVProductRestrictionSubset U T D hD)
    (gammaGroundRVProductDomain_disjoint _ _ _ (gammaGroundRVTaggedImages_disjoint _ _))
    (by rw [← gammaGroundRVProductDomain_union]; rfl)
  let f := (gammaGroundRVProductIso (Iso.refl U) (gammaGroundRVCoprodLeftRestrictionIso V W)).trans
    (gammaGroundRVProductRestrictionIso U T B hB)
  let g := (gammaGroundRVProductIso (Iso.refl U) (gammaGroundRVCoprodRightRestrictionIso V W)).trans
    (gammaGroundRVProductRestrictionIso U T D hD)
  exact hp.trans (congrArg₂ (· + ·) (gammaGroundRVClass_iso f).symm (gammaGroundRVClass_iso g).symm)

theorem gammaGroundRVClassMul_zero (a : GammaGroundRVKPlus hc ground k) :
    gammaGroundRVClassMul a (0 : GammaGroundRVKPlus hc ground l) = 0 := by
  obtain ⟨U, rfl⟩ := gammaGroundRVClass_surjective a
  rw [← gammaGroundRVClass_empty (M := M) (hc := hc) (ground := ground) (k := l), gammaGroundRVClassMul_class]
  have he : (U.product (GammaGroundRVObject.empty hc ground l)).domain.carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨a, _⟩
    exact a.property.2
  have hi : U.product (GammaGroundRVObject.empty hc ground l) ≅ GammaGroundRVObject.empty hc ground (k + l) :=
    asIso (show _ ⟶ _ from GammaGroundBijection.ofEmpty he rfl)
  exact (gammaGroundRVClass_iso hi).trans gammaGroundRVClass_empty

theorem gammaGroundRVKPlusCast_zero (h : k = l) :
    gammaGroundRVKPlusCast h (0 : GammaGroundRVKPlus hc ground k) = 0 := by cases h; rfl

theorem gammaGroundRVClassMul_zero_left (b : GammaGroundRVKPlus hc ground l) :
    gammaGroundRVClassMul (0 : GammaGroundRVKPlus hc ground k) b = 0 := by
  rw [← gammaGroundRVClassMul_comm_cast, gammaGroundRVClassMul_zero]
  exact gammaGroundRVKPlusCast_zero _

theorem gammaGroundRVClassMul_add (a : GammaGroundRVKPlus hc ground k) (b c : GammaGroundRVKPlus hc ground l) :
    gammaGroundRVClassMul a (b + c) = gammaGroundRVClassMul a b + gammaGroundRVClassMul a c := by
  obtain ⟨U, rfl⟩ := gammaGroundRVClass_surjective a
  obtain ⟨V, rfl⟩ := gammaGroundRVClass_surjective b
  obtain ⟨W, rfl⟩ := gammaGroundRVClass_surjective c
  rw [← gammaGroundRVClass_coprod V W, gammaGroundRVClassMul_class,
    gammaGroundRVClassMul_class, gammaGroundRVClassMul_class]
  exact gammaGroundRVClass_product_coprod U V W

theorem gammaGroundRVClassMul_add_left (a b : GammaGroundRVKPlus hc ground k) (c : GammaGroundRVKPlus hc ground l) :
    gammaGroundRVClassMul (a + b) c = gammaGroundRVClassMul a c + gammaGroundRVClassMul b c := by
  rw [← gammaGroundRVClassMul_comm_cast (a + b) c, gammaGroundRVClassMul_add, gammaGroundRVKPlusCast_add,
    gammaGroundRVClassMul_comm_cast, gammaGroundRVClassMul_comm_cast]

end DiamondIntegral.Section3
