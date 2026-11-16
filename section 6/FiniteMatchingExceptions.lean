import «section 6».PairedUnaryExceptionCenters
import «section 6».OrdinaryFocusExceptions

/-! For the original degree-one objects, finite VF projection and
their actual finite RV fibres make the paired exceptional domain finite
as a full mixed set. Intermediate RV fibres are not assumed finite. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

theorem finite_mixed_set_of_finite_vf_projection (H : Set (Mixed M n r))
    (hVF : (Prod.fst '' H).Finite)
    (hRV : ∀ a : Fin n → VF M,{u : Fin r → RVInfinity M | (a,u) ∈ H}.Finite) : H.Finite := by
  apply Set.Finite.of_finite_fibers Prod.fst hVF
  intro a ha
  apply ((hRV a).image (fun u => (a,u))).subset
  rintro p ⟨hp,he⟩
  exact ⟨p.2,he ▸ hp,by rw [← he]⟩

variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}

theorem pairedUnaryExceptionDomain_finite_vfProjection
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (f : Map A B) (hf : Function.Bijective f)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (F : DefSet (rawMixedSpace (M := M) 1 s) S)
    (hE : (Prod.fst '' E.carrier).Finite) (hF : (Prod.fst '' F.carrier).Finite) :
    (Prod.fst '' (pairedUnaryExceptionDomain f E F).carrier).Finite := by
  have hPre := unaryFieldImage_finite hc hκ hs hsmall (f.inverse hf) F.carrier hF
  apply (hE.union hPre).subset
  rintro x ⟨p,hp,rfl⟩
  rcases hp with hE | ⟨a,rfl,hF⟩
  · exact Or.inl ⟨p,hE,rfl⟩
  · apply Or.inr
    refine ⟨f a,hF,?_⟩
    rw [Map.inverse_apply]

theorem pairedUnaryExceptionDomain_finite
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (f : Map A B) (hf : Function.Bijective f)
    (E : DefSet (rawMixedSpace (M := M) 1 r) S) (F : DefSet (rawMixedSpace (M := M) 1 s) S)
    (hEA : E.carrier ⊆ A.carrier)
    (hE : (Prod.fst '' E.carrier).Finite) (hF : (Prod.fst '' F.carrier).Finite)
    (hFinite : ∀ a : Fin 1 → VF M,{u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite) :
    (pairedUnaryExceptionDomain f E F).carrier.Finite := by
  apply finite_mixed_set_of_finite_vf_projection _
    (pairedUnaryExceptionDomain_finite_vfProjection hc hκ hs hsmall f hf E F hE hF)
  intro a
  exact (hFinite a).subset (fun _ hu => pairedUnaryExceptionDomain_subset f E F hEA hu)

theorem OriginalBaseOrdinaryUnaryMatching.exception_domain_finite
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    {f : Map A B} (hf : Function.Bijective f) (T : OriginalBaseOrdinaryUnaryMatching A B f)
    (hFinite : ∀ a : Fin 1 → VF M,{u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite) :
    (pairedUnaryExceptionDomain f (T.sourceSpecial.exceptions hc) (T.targetSpecial.exceptions hc)).carrier.Finite :=
  pairedUnaryExceptionDomain_finite hc hκ hs hsmall f hf _ _ (T.sourceSpecial.exceptions_subset hc)
    (T.sourceSpecial.exceptions_finite_vfProjection hc hκ hs hsmall)
    (T.targetSpecial.exceptions_finite_vfProjection hc hκ hs hsmall) hFinite

end DiamondIntegral.Section6
