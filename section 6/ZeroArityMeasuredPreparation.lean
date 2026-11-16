import «section 6».PreparedMeasuredLifts
import «section 6».ZeroArityPreparation

/-! Zero-VF-arity measured preparation and degree-zero lifting. The empty
VF tuple is a singleton, all forms already depend only on RV labels,
and the determinant-one measure identity holds everywhere. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {r k : ℕ} {S : Set M}

theorem zero_arity_gamma_tag_constant
    (A : DefSet (rawMixedSpace (M := M) 0 r) S)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (p q : A) (hTags : p.val.2 = q.val.2) : ω p = ω q := by
  have hVF : p.val.1 = q.val.1 := by funext i; exact i.elim0
  exact congrArg ω (Subtype.ext (Prod.ext hVF hTags))

def zero_arity_measured_lift
    (A : DefSet (rawMixedSpace (M := M) 0 r) S) (hA : ProperInvariant S A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hFin : ∀ a : Fin 0 → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite) :
    MeasuredRVLiftData (G := G) A ω :=
  measured_lift_of_prepared A hA ⟨1,fun _ _ i => i.elim0⟩ (zero_arity_rvPullback _)
    (fun _ _ _ _ _ => funext (fun i => i.elim0)) ω (zero_arity_gamma_tag_constant A ω) hFin

theorem zero_arity_measured_lift_map_value
    (A : DefSet (rawMixedSpace (M := M) 0 r) S) (hA : ProperInvariant S A.carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hFin : ∀ a : Fin 0 → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ A.carrier}.Finite) (p : A) :
    ((zero_arity_measured_lift (G := G) A hA ω hFin).map p).val = p.val :=
  measured_lift_of_prepared_map_value A hA _ _ _ ω _ hFin p

theorem MeasuredRVLiftData.measure_identity_zero_arity [CharZero (VF M)]
    {A : DefSet (rawMixedSpace (M := M) 0 r) S}
    {ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)}
    (T : MeasuredRVLiftData (G := G) A ω)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) (p : A) :
    ∃ J, HasMixedVFJacobianAt T.map p J ∧
      vfValue J = (gammaMapValue ω p/gammaMapValue T.rvForm (T.labelMap p)).val := by
  refine ⟨1,(T.special.unit_derivative_zero_arity h00 hc hκ hs hsmall hv p).partialJacobian,?_⟩
  have hValues : gammaMapValue T.rvForm (T.labelMap p) = gammaMapValue ω p := T.form_preserves p
  have hRatio : gammaMapValue ω p/gammaMapValue T.rvForm (T.labelMap p) = (1 : Gamma M) := by
    rw [hValues]
    exact div_self' (gammaMapValue ω p)
  have hOne : vfValue (1 : VF M) = (1 : Gamma M).val :=
    (valueHom_eq_value (1 : VF M)).symm.trans ((map_one Values.vfValueHom).trans Values.gamma_val_one.symm)
  exact hOne.trans (congrArg (fun γ : Gamma M => γ.val) hRatio).symm

theorem lemma_6_21_zero_arity (h00 : M ⊨ Axioms.ACVF00)
    (A : DefSet (rawMixedSpace (M := M) 0 r) S) (hA : ProperInvariant S A.carrier)
    (C : Fin k → DefSet (rawMixedSpace (M := M) 0 r) S)
    (hCA : ∀ i, (C i).carrier ⊆ A.carrier) (hC : ∀ i, ProperInvariant S (C i).carrier)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S)) :
    SpecialCovariantChain (G := G) A A (Map.id A) ∧
      (∀ i, SpecialCovariantChain (G := G) (C i) ((Map.id A).restrict (hCA i)).image
        ((Map.id A).restrict (hCA i)).toImage ∧ IsRVPullback ((Map.id A).restrict (hCA i)).image.carrier) ∧
      (∀ p q : A, p.val.2 = q.val.2 → ω p = ω q) ∧
      ∀ i, (∀ a : Fin 0 → VF M, {u : Fin r → RVInfinity M | (a,u) ∈ (C i).carrier}.Finite) →
        ∃ L : MeasuredRVLiftData (G := G) (C i) (ω.comp (Map.inclusion (hCA i))),
          L.object.arity = r ∧ ∀ p : C i, HEq (L.map p).val p.val := by
  obtain ⟨hId,hD,hRV,hPieces⟩ := lemma_6_19_zero_arity h00 A hA C hCA hC
  refine ⟨hId,hPieces,zero_arity_gamma_tag_constant A ω,fun i hFin => ?_⟩
  exact ⟨zero_arity_measured_lift (C i) (hC i) (ω.comp (Map.inclusion (hCA i))) hFin,
    rfl,fun p => (zero_arity_measured_lift_map_value (C i) (hC i) (ω.comp (Map.inclusion (hCA i))) hFin p).heq⟩

end DiamondIntegral.Section6
