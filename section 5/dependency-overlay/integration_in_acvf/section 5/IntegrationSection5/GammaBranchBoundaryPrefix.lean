import IntegrationSection5.EmptyFocus
import IntegrationSection5.GammaUnaryCoordinateLift
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n a b l : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b} {H : DefSet (M := M) S n l}

theorem unary_chain_initial_boundary (T : Chain S 1 A B) (hT : T.Alternating none) :
    T.Alternating (some false) ∨ T.Alternating (some true) := by
  cases T with
  | nil A => exact Or.inl trivial
  | cons p tail =>
    cases p with
    | canonical => exact Or.inr ⟨by decide,hT.2⟩
    | centripetal D => exact Or.inl ⟨by decide,hT.2⟩

theorem gamma_branch_boundary_prefix_of_not_canonical (T : Chain S 1 A B)
    (hT : T.Alternating none) (hH : GammaSetDefinable G (carrier H))
    (i : Fin n) (previous : Option Bool) (hPrev : previous ≠ some false) :
    ∃ K : DefSet (M := M) S n (1+l), ∃ f : Map H K, ∃ start : Option Bool,
      SpecialRelativeBoundary f i previous start ∧ T.Alternating start ∧
      GammaSetDefinable G (carrier K) ∧ GammaGraphDefinable G (pointMapGraph f) ∧
      (∀ p : H, (f p).val = coordinateCanonical i p.val) ∧
      (start ≠ some true → ∃ kH, Tagged (carrier K) i kH) := by
  let C := coordinateCanonicalImage H i
  let can := coordinateCanonicalBijection H i
  have hC := gamma_coordinateCanonicalImage H hH i
  have hCan := gamma_coordinateCanonical_graph H hH i
  rcases unary_chain_initial_boundary T hT with hFalse | hTrue
  · exact ⟨C,can,some false,coordinateCanonical_specialRelativeBoundary H i previous hPrev,
      hFalse,hC,hCan,fun _ => rfl,fun _ => ⟨0,coordinateCanonical_tagged H i⟩⟩
  · let D := Focus.empty i 0 (coordinateCanonical_tagged H i)
    let eta := (SpecialBijection.centripetal D).toMap
    have hD : GammaFocusDefinable G D := Focus.empty_gamma i 0 (coordinateCanonical_tagged H i)
    have hK := GammaPrimitiveDefinable.target (gammaLogicInput G) (.centripetal D) ⟨hC,hD⟩
    have hEta := GammaPrimitiveDefinable.graph (gammaLogicInput G) (.centripetal D) ⟨hC,hD⟩
    refine ⟨D.etaImage,Map.comp eta can,some true,?_,hTrue,hK,?_,?_,fun h => (h rfl).elim⟩
    · exact specialRelativeBoundary_comp can eta i
        (coordinateCanonical_specialRelativeBoundary H i previous hPrev)
        (centripetal_specialRelativeBoundary D (some false) (by decide))
    · exact gamma_composition_graph can eta hCan hEta
    · intro p
      exact Focus.empty_eta i 0 (coordinateCanonical_tagged H i) (can p).val

theorem gamma_branch_boundary_prefix (T : Chain S 1 A B)
    (hT : T.Alternating none) (hH : GammaSetDefinable G (carrier H))
    (i : Fin n) (previous : Option Bool)
    (hTag : previous = some false → ∃ kH, Tagged (carrier H) i kH) :
    ∃ K : DefSet (M := M) S n (1+l), ∃ f : Map H K, ∃ start : Option Bool,
      SpecialRelativeBoundary f i previous start ∧ T.Alternating start ∧
      GammaSetDefinable G (carrier K) ∧ GammaGraphDefinable G (pointMapGraph f) ∧
      (∀ p : H, (f p).val = coordinateCanonical i p.val) ∧
      (start ≠ some true → ∃ kH, Tagged (carrier K) i kH) := by
  by_cases hp : previous = some false
  · subst previous
    obtain ⟨kH,hkH⟩ := hTag rfl
    let D := Focus.empty i kH hkH
    let eta := (SpecialBijection.centripetal D).toMap
    have hD : GammaFocusDefinable G D := Focus.empty_gamma i kH hkH
    have hHD := GammaPrimitiveDefinable.target (gammaLogicInput G) (.centripetal D) ⟨hH,hD⟩
    have hEta := GammaPrimitiveDefinable.graph (gammaLogicInput G) (.centripetal D) ⟨hH,hD⟩
    obtain ⟨K,f,start,hf,hStart,hK,hfG,hForm,hTagEnd⟩ :=
      gamma_branch_boundary_prefix_of_not_canonical T hT hHD i (some true) (by decide)
    refine ⟨K,Map.comp f eta,start,?_,hStart,hK,?_,?_,hTagEnd⟩
    · exact specialRelativeBoundary_comp eta f i
        (centripetal_specialRelativeBoundary D (some false) (by decide)) hf
    · exact gamma_composition_graph eta f hEta hfG
    · intro p
      exact (hForm (eta p)).trans (congrArg (coordinateCanonical i) (Focus.empty_eta i kH hkH p.val))
  · exact gamma_branch_boundary_prefix_of_not_canonical T hT hH i previous hp

theorem canonical_form_target {K : DefSet (M := M) S n (1+l)} (i : Fin n)
    (f : Map H K) (hf : Function.Bijective f)
    (hForm : ∀ p : H, (f p).val = coordinateCanonical i p.val) :
    carrier K = carrier (coordinateCanonicalImage H i) := by
  ext q
  constructor
  · intro hq
    obtain ⟨p,hp⟩ := hf.2 ⟨q,hq⟩
    exact ⟨p,(hForm p).symm.trans (congrArg (fun z : K => z.val) hp)⟩
  · rintro ⟨p,hp⟩
    exact ((hForm p).trans hp) ▸ (f p).property

end IntegrationInACVF.Section5
