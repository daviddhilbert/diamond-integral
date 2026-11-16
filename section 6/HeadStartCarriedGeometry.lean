import «section 6».HeadStartCarriedBijections
import «section 6».CarriedExceptionalSets

/-! Head-start lifts preserve proper covariant homeomorphisms and
unit total derivatives. The exceptional set is its literal lifted
domain, with the strict dimension inequality in degree n+k. -/

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
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}

theorem carryHeadStartBijection_properHomeomorphism
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (f : Map A B) (hf : Function.Bijective f) (hF : ProperCovariantHomeomorphism f)
    (k : ℕ) (π : Fin k → Fin r) (θ : Fin k → Fin s)
    (hLabels : ∀ p : A,∀ i,(f p).val.2 (θ i)=p.val.2 (π i)) :
    ProperCovariantHomeomorphism (carryHeadStartBijection f hf k π θ hLabels).map := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    let H := carryHeadStartBijection f hf k (π ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
      (fun p i => hLabels p i.castSucc)
    have hL (p : rvHeadStartBundle A k (π ∘ Fin.castSucc)) :
        (H.map p).val.2 (θ (Fin.last k))=p.val.2 (π (Fin.last k)) := by
      simpa only [headStartBaseProjection_value] using
        (congrFun (H.labels p) (θ (Fin.last k))).trans
          (hLabels (headStartBaseProjection A k (π ∘ Fin.castSucc) p) (Fin.last k))
    change ProperCovariantHomeomorphism (carryLastMap H.map (π (Fin.last k)) (θ (Fin.last k)) hL)
    exact carryLastMap_properHomeomorphism H.map _ _ hL h00 hc linear hκ hs hv hsmall hΓ
      (ih _ _ (fun p i => hLabels p i.castSucc))

theorem carryHeadStartBijection_unit_derivative
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hf : Function.Bijective f) (hA : ProperInvariant S A.carrier)
    (k : ℕ) (π : Fin k → Fin r) (θ : Fin k → Fin s)
    (hLabels : ∀ p : A,∀ i,(f p).val.2 (θ i)=p.val.2 (π i))
    (p : rvHeadStartBundle A k π)
    (hUnit : HasMixedUnitDerivativeAt f (headStartBaseProjection A k π p)) :
    HasMixedUnitDerivativeAt (carryHeadStartBijection f hf k π θ hLabels).map p := by
  induction k with
  | zero => exact hUnit
  | succ k ih =>
    let H := carryHeadStartBijection f hf k (π ∘ Fin.castSucc) (θ ∘ Fin.castSucc)
      (fun p i => hLabels p i.castSucc)
    have hL (p : rvHeadStartBundle A k (π ∘ Fin.castSucc)) :
        (H.map p).val.2 (θ (Fin.last k))=p.val.2 (π (Fin.last k)) := by
      simpa only [headStartBaseProjection_value] using
        (congrFun (H.labels p) (θ (Fin.last k))).trans
          (hLabels (headStartBaseProjection A k (π ∘ Fin.castSucc) p) (Fin.last k))
    change HasMixedUnitDerivativeAt (carryLastMap H.map (π (Fin.last k)) (θ (Fin.last k)) hL) p
    exact carryLastMap_unit_derivative h00 hc hκ hs hv H.map
      (rvHeadStartBundle_properInvariant h00 hc hκ hs hv A k _ hA) _ _ hL p
      (ih _ _ (fun p i => hLabels p i.castSucc) _ hUnit)

theorem rvHeadStartBundle_exception_dim_lt
    (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (E : DefSet (rawMixedSpace (M := M) n r) S) (k : ℕ) (π : Fin k → Fin r)
    (hDim : vfDim (rawRVSpace (M := M) 1) E < n) :
    vfDim (rawRVSpace (M := M) 1) (rvHeadStartBundle E k π) < n+k := by
  induction k with
  | zero => exact hDim
  | succ k ih => exact carried_exception_dim_lt hc hs hsmall _ _ (ih _)

theorem carryHeadStartBijection_unit_derivative_ae
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ)
    (f : Map A B) (hf : Function.Bijective f) (hA : ProperInvariant S A.carrier)
    (k : ℕ) (π : Fin k → Fin r) (θ : Fin k → Fin s)
    (hLabels : ∀ p : A,∀ i,(f p).val.2 (θ i)=p.val.2 (π i))
    (E : DefSet (rawMixedSpace (M := M) n r) S) (hEA : E.carrier ⊆ A.carrier)
    (hDim : vfDim (rawRVSpace (M := M) 1) E < n)
    (hUnit : ∀ p : A,p.val ∉ E.carrier → HasMixedUnitDerivativeAt f p) :
    (rvHeadStartBundle E k π).carrier ⊆ (rvHeadStartBundle A k π).carrier ∧
      vfDim (rawRVSpace (M := M) 1) (rvHeadStartBundle E k π) < n+k ∧
      ∀ p : rvHeadStartBundle A k π,p.val ∉ (rvHeadStartBundle E k π).carrier →
        HasMixedUnitDerivativeAt (carryHeadStartBijection f hf k π θ hLabels).map p := by
  refine ⟨?_,rvHeadStartBundle_exception_dim_lt hc hs hsmall E k π hDim,?_⟩
  · intro p hp
    obtain ⟨hE,hHead⟩ := (mem_rvHeadStartBundle E k π p.1 p.2).mp hp
    exact (mem_rvHeadStartBundle A k π p.1 p.2).mpr ⟨hEA hE,hHead⟩
  · intro p hp
    apply carryHeadStartBijection_unit_derivative h00 hc hκ hs hv f hf hA k π θ hLabels p
    apply hUnit
    intro hMem
    rw [headStartBaseProjection_value] at hMem
    apply hp
    exact (mem_rvHeadStartBundle E k π p.val.1 p.val.2).mpr
      ⟨hMem,((mem_rvHeadStartBundle A k π p.val.1 p.val.2).mp p.property).2⟩

end DiamondIntegral.Section6
