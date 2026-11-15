import «section 5».Completed18RVClassEquivalence
import «section 3».GammaGroundRVProductScissors
import IntegrationSection6.GammaNonzeroGradedSemiring

/-! Addition and cartesian products agree under the actual RV class dictionary. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.Section4.rawRVSpace
  SpecialTransformations.Section4.realSpace SpecialTransformations.DefinableGeometry.Space.ofEmbedding
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV
open DiamondIntegral.Section3 DiamondIntegral.Section4
namespace DiamondIntegral.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)} {a b k l : ℕ}
local notation "N" => (@CanonicalStructure.normalize M sM)
local notation "hN" => (@CanonicalStructure.normalized_model M sM hM)
local instance : Fact (B.real ⊆ (Set.univ : Set M)) := ⟨Set.subset_univ _⟩

theorem rvLeftTag_normalized (t : Fin a → CanonicalRV.RVSort M) :
    @rvLeftTag M N hN a b t = @rvLeftTag M sM hM a b t := by
  unfold rvLeftTag rvAppend rvZeroTuple
  apply congrArg₂ Fin.append
  · funext i
    exact Subtype.ext (CanonicalStructure.sortZero_normalize .rv)
  · apply congrArg₂ Fin.append rfl
    funext i
    exact Subtype.ext (CanonicalStructure.sortZero_normalize .rv)

theorem rvRightTag_normalized (t : Fin b → CanonicalRV.RVSort M) :
    @rvRightTag M N hN b a t = @rvRightTag M sM hM b a t := by
  unfold rvRightTag rvAppend rvZeroTuple
  apply congrArg₂ Fin.append
  · funext i
    apply Subtype.ext
    exact CanonicalStructure.normalize_fun Fn.rvOne (fun i => i.elim0) (fun i => i.elim0)
  · apply congrArg₂ Fin.append
    · funext i
      exact Subtype.ext (CanonicalStructure.sortZero_normalize .rv)
    · rfl

theorem groundRVAt_coprod_domain (U V : GammaGroundRVObject hc B k) :
    (nativeRVGroundDomain (hc := hc) (gammaCoprodAt (groundRVAt U) (groundRVAt V))).carrier =
      (U.coprod V).domain.carrier := by
  rw [nativeRVGroundDomain_carrier]
  ext x
  change ((∃ u : rvObjectDomain (groundRVAt U).object.obj,@rvLeftTag M N hN U.arity V.arity u.val=x) ∨
    (∃ v : rvObjectDomain (groundRVAt V).object.obj,@rvRightTag M N hN V.arity U.arity v.val=x)) ↔
    ((∃ u : U.domain,rvLeftTag V.arity u.val=x) ∨ (∃ v : V.domain,rvRightTag U.arity v.val=x))
  constructor
  · rintro (⟨u,hu⟩|⟨v,hv⟩)
    · exact Or.inl ⟨(groundRVAtDomainEquiv U).symm u,(@rvLeftTag_normalized M sM hM U.arity V.arity u.val).symm.trans hu⟩
    · exact Or.inr ⟨(groundRVAtDomainEquiv V).symm v,(@rvRightTag_normalized M sM hM U.arity V.arity v.val).symm.trans hv⟩
  · rintro (⟨u,hu⟩|⟨v,hv⟩)
    · exact Or.inl ⟨groundRVAtDomainEquiv U u,(@rvLeftTag_normalized M sM hM U.arity V.arity u.val).trans hu⟩
    · exact Or.inr ⟨groundRVAtDomainEquiv V v,(@rvRightTag_normalized M sM hM U.arity V.arity v.val).trans hv⟩

theorem groundRVAt_product_domain (U : GammaGroundRVObject hc B k) (V : GammaGroundRVObject hc B l) :
    (nativeRVGroundDomain (hc := hc) (gammaProductAt (groundRVAt U) (groundRVAt V))).carrier =
      (U.product V).domain.carrier := by
  rw [nativeRVGroundDomain_carrier]
  ext x
  change _ ↔ x ∈ (gammaGroundRVProductDomain U.domain V.domain).carrier
  rw [mem_gammaGroundRVProductDomain]
  constructor
  · rintro ⟨uv,huv⟩
    exact ⟨uv.val.1,(groundRVAt_domain U) ▸ uv.property.1,
      uv.val.2,(groundRVAt_domain V) ▸ uv.property.2,huv⟩
  · rintro ⟨u,hu,v,hv,he⟩
    exact ⟨⟨(u,v),(groundRVAt_domain U).symm ▸ hu,(groundRVAt_domain V).symm ▸ hv⟩,he⟩

theorem groundRVClassNative_zero :
    groundRVClassNative (hc := hc) (B := B) (k := k) 0 = 0 := by
  rw [← gammaGroundRVClass_empty (hc := hc) (ground := B) (k := k),groundRVClassNative_class]
  apply Subtype.ext
  change gammaIsoClassAt _ = 0
  rw [← gammaIsoClassAt_empty (B := B) (n := k) (Set.subset_univ _)]
  apply gammaIsoClassAt_iso
  apply groundRVAtToNativeIso _ _ (gammaFullWeightAt_empty _)
  apply GammaGroundBijection.ofCarrierEq
  rw [nativeRVGroundDomain_carrier]
  rfl

theorem groundRVClassNative_add (x y : GammaGroundRVKPlus hc B k) :
    groundRVClassNative (x+y)=groundRVClassNative x+groundRVClassNative y := by
  obtain ⟨U,rfl⟩ := gammaGroundRVClass_surjective x
  obtain ⟨V,rfl⟩ := gammaGroundRVClass_surjective y
  rw [← gammaGroundRVClass_coprod,groundRVClassNative_class,groundRVClassNative_class,groundRVClassNative_class]
  apply Subtype.ext
  change gammaIsoClassAt _ = gammaIsoClassAt _ + gammaIsoClassAt _
  rw [← gammaIsoClassAt_coprod]
  exact gammaIsoClassAt_iso (groundRVAtToNativeIso _ _ ((groundRVAt_full U).coprod (groundRVAt_full V))
    (GammaGroundBijection.ofCarrierEq (groundRVAt_coprod_domain U V).symm))

def completed18RVClassAddEquiv : GammaGroundRVKPlus hc B k ≃+
    GammaNonzeroClassesAt (B := B) (S := Set.univ) k where
  __ := completed18RVClassEquiv
  map_add' := groundRVClassNative_add

theorem groundRVClassNative_mul (x : GammaGroundRVKPlus hc B k) (y : GammaGroundRVKPlus hc B l) :
    groundRVClassNative (gammaGroundRVClassMul x y)=
      gammaNonzeroMulAt (groundRVClassNative x) (groundRVClassNative y) := by
  obtain ⟨U,rfl⟩ := gammaGroundRVClass_surjective x
  obtain ⟨V,rfl⟩ := gammaGroundRVClass_surjective y
  rw [gammaGroundRVClassMul_class,groundRVClassNative_class,groundRVClassNative_class,groundRVClassNative_class]
  apply Subtype.ext
  change gammaIsoClassAt _ = gammaClassMulAt (gammaIsoClassAt _) (gammaIsoClassAt _)
  rw [gammaClassMulAt_class]
  exact gammaIsoClassAt_iso (groundRVAtToNativeIso _ _ ((groundRVAt_full U).product (groundRVAt_full V))
    (GammaGroundBijection.ofCarrierEq (groundRVAt_product_domain U V).symm))

end DiamondIntegral.Section5
