import «section 4».RVResidueCodeIndependence
import «section 4».RESFibreObjects
import Section4.ResidueScaledPredicates

/-! Every nonzero full RV value fibre has the pure-field punctured-line
class. The scale is an arbitrary auxiliary representative, not an
original-base definable lift. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section4.ResiduePurity

namespace DiamondIntegral.Section4.RVResidueFibreCodes
open RVResidueChartCodes RVResidueScaledCovers RVResidueCodeIndependence
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
attribute [local instance] FirstOrder.Ring.compatibleRingOfRing

def puncturedLine (K : Type) [Field K] : FieldDefinableRing.Chart K :=
  ⟨1, {x | x 0 ≠ 0}, ((pure_proj (0 : Fin 1)).eq_const (0 : K)).compl⟩

theorem sameValue_scale_iff (s : CanonicalRV.RVSort M) (hs : s ≠ 0) (x : ModelResidue M) :
    Values.vrv (s * residueRV x) = Values.vrv s ↔ x ≠ 0 := by
  constructor
  · intro hv hx
    rw [hx, residueRV_zero, mul_zero] at hv
    apply hs
    apply (RVOperations.absolute_eq_zero s).mp
    rw [← absolute_eq_of_vrv_eq hv, map_zero]
  · intro hx
    apply (Values.valueEquiv Values.presentationValuation Values.presentation_compatible).injective
    change RVOperations.absoluteHom (s * residueRV x) = RVOperations.absoluteHom s
    rw [map_mul, absolute_residue, if_neg hx, mul_one]

def scalarCode (s : CanonicalRV.RVSort M) (hs : s ≠ 0) (A : Set (Fin 1 → M))
    (hA : ∀ u, u ∈ A ↔ ∃ t : CanonicalRV.RVSort M, t.val = u 0 ∧ Values.vrv t = Values.vrv s) :
    RawCode A where
  chart := puncturedLine (ModelResidue M)
  decode := residueScale (fun _ => s)
  bijective := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      exact (hA _).mpr ⟨s * residueRV (x (0 : Fin 1)), rfl,
        (sameValue_scale_iff s hs (x (0 : Fin 1))).mpr hx⟩
    · intro x _ y _ he
      funext i
      apply residueRV_injective
      apply mul_left_cancel₀ hs
      apply Subtype.ext
      exact congrFun he i
    · intro u hu
      obtain ⟨t, htu, htv⟩ := (hA u).mp hu
      let x := residueNormalize (fun _ : Fin 1 => s) (fun _ => t)
      have hscale : residueScale (fun _ : Fin 1 => s) x = fun _ => t :=
        residueScale_normalize _ _ (fun _ => htv)
      have hx : x 0 ≠ 0 := (sameValue_scale_iff s hs (x 0)).mp (by
        change Values.vrv (residueScale (fun _ : Fin 1 => s) x 0) = Values.vrv s
        rw [hscale]
        exact htv)
      refine ⟨x, hx, ?_⟩
      funext i
      fin_cases i
      exact (congrArg Subtype.val (congrFun hscale 0)).trans htu
  cover := {
    Index := Unit
    finite := inferInstance
    piece := fun _ => {
      guard := Set.univ
      definable := Set.definable_univ
      scale := fun _ => s
      coord := id }
    covers := fun _ _ => ⟨(), Set.mem_univ _⟩
    agrees := fun _ _ _ _ => rfl }

theorem fibre_domain (B : Base (M := M)) (α β : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β)
    (s : CanonicalRV.RVSort M) (hsv : Values.vrv s = α.val) (u : Fin 1 → M) :
    u ∈ (RESFibreObjects.fibre B α β hα hβ).domain ↔
      ∃ t : CanonicalRV.RVSort M, t.val = u 0 ∧ Values.vrv t = Values.vrv s := by
  change (Proper u ∧ codeValue (u 0) = α) ↔ _
  constructor
  · rintro ⟨hp, hv⟩
    let t : Code (M := M) := ⟨⟨u 0, (hp 0).1⟩, (hp 0).2⟩
    have hproj : (codeValue (u 0)).val = Values.vrv t.val := congrArg Subtype.val (codeValue_raw t)
    exact ⟨t.val, rfl, hproj.symm.trans ((congrArg Subtype.val hv).trans hsv.symm)⟩
  · rintro ⟨t, htu, htv⟩
    have ht0 : t.val ≠ iRVZero := by
      intro hz
      exact α.property ((htv.trans hsv).symm.trans ((Values.vrv_eq_infinity_iff t).mpr hz))
    have hp : Proper u := by
      intro i
      fin_cases i
      exact htu ▸ ⟨t.property, ht0⟩
    refine ⟨hp, ?_⟩
    apply Subtype.ext
    have hproj : (codeValue t.val).val = Values.vrv t :=
      congrArg Subtype.val (codeValue_raw (⟨t, ht0⟩ : Code (M := M)))
    exact (congrArg (fun v : M => (codeValue v).val) htu).symm.trans (hproj.trans (htv.trans hsv))

theorem value_fibre (hc : CanonicalStructure.IsCanonical (M := M)) [Infinite (ModelResidue M)]
    (B : Base (M := M)) (α β : Values.Gamma (M := M))
    (hα : GammaDefinableClosureAtBase B α) (hβ : GammaDefinableClosureAtBase B β) :
    RVResidueIsomorphisms.value hc (RESFibreObjects.fibre B α β hα hβ) =
      FieldDefinableRing.objectClass (ModelResidue M) (puncturedLine (ModelResidue M)) := by
  let s := (representative α).val
  have hsv : Values.vrv s = α.val := congrArg Subtype.val (representative_value α)
  have hs : s ≠ 0 := by
    intro he
    exact (raw_ne_zero (representative α)) (by change s.val = iRVZero; rw [he, RVOperations.zero_val])
  exact (code_class_value hc (RESFibreObjects.fibre B α β hα hβ)
    (scalarCode s hs _ (fibre_domain B α β hα hβ s hsv))).symm

end DiamondIntegral.Section4.RVResidueFibreCodes
