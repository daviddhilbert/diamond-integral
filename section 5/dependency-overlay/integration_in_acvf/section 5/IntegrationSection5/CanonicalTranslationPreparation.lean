import IntegrationSection5.CentripetalRelativeBoundary
import IntegrationSection5.CoordinateCanonicalProjection
import IntegrationSection5.HullTranslationFocus
import IntegrationSection5.ScalarCentreMaps

/-! An actual coordinate-canonical step followed by the constructed hull
focus, with legal fibre-special alternation and complete original-Gamma graphs. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m : ℕ}

structure CanonicalTranslationPreparation (A : Set (Point (M := M) n m))
    (i : Fin n) (c : Point (M := M) n m → VF (M := M)) where
  codes : Set M
  real_contains : G.real ⊆ codes
  source : DefSet (M := M) codes n m
  target : DefSet (M := M) codes n (1+m)
  source_eq : carrier source = A
  map : Map source target
  special : SpecialRelativeBoundary map i none (some true)
  graph : GammaGraphDefinable G (pointMapGraph map)
  target_gamma : GammaSetDefinable G (carrier target)
  formula : ∀ a : source, (map a).val =
    replace i (coordinateCanonical i a.val) (vfAt a.val i-c a.val)

theorem canonical_translation_preparation (A : Set (Point (M := M) n m))
    (hA : GammaSetDefinable G A) (i : Fin n) (c : Point (M := M) n m → VF (M := M))
    (hind : ∀ p ∈ A, ∀ q ∈ A, erase i p = erase i q → c p = c q)
    (hRV : ∀ p ∈ A, rv (c p) = rv (vfAt p i))
    (hc : GammaScalarGraphDefinable G (fun p x => p ∈ A ∧ x = c p)) :
    Nonempty (CanonicalTranslationPreparation (G := G) A i c) := by
  obtain ⟨S,hGS,hAr,hcr⟩ := scalar_real_presentation A hA c hc
  let AR : DefSet (M := M) S n m := @PresentedSet.mk M sM (pointSpace n m) S A hAr
  let C := coordinateCanonicalImage AR i
  let can := coordinateCanonicalBijection AR i
  let canBij := coordinateCanonicalBijection_bijective AR i
  let cc : Point (M := M) n (1+m) → VF (M := M) := fun q => c (forgetCoordinateLabel q)
  have hC : GammaSetDefinable G (carrier C) := gamma_coordinateCanonicalImage AR hA i
  have hindC : ∀ p ∈ carrier C, ∀ q ∈ carrier C, erase i p = erase i q → cc p = cc q := by
    intro p hp q hq he
    apply hind (forgetCoordinateLabel p) (forgetCoordinateLabel_mem AR i ⟨p,hp⟩)
      (forgetCoordinateLabel q) (forgetCoordinateLabel_mem AR i ⟨q,hq⟩)
    exact (forgetCoordinateLabel_erase i p).symm.trans
      ((congrArg forgetCoordinateLabel he).trans (forgetCoordinateLabel_erase i q))
  have hRVC : ∀ p ∈ carrier C, rv (cc p) = rv (vfAt p i) := by
    intro p hp
    exact hRV (forgetCoordinateLabel p) (forgetCoordinateLabel_mem AR i ⟨p,hp⟩)
  let sc := Map.comp (scalarCentreMap AR c hcr) (Map.inverse can canBij)
  have hsc (q : C) : (sc q).val 0 = cc q.val := by
    change c (Map.inverse can canBij q).val = cc q.val
    exact congrArg c (coordinateCanonical_inverse_val AR i q)
  have hcc : RelationDefinable (pointSpace n (1+m)) (SpecialTransformations.Section4.vfSpace 1) S
      (fun p z => p ∈ carrier C ∧ z 0 = cc p) := by
    apply RelationDefinable.congr _ _ (Map.graph_definable sc)
    intro p z
    constructor
    · rintro ⟨a,ha,hz⟩
      exact ⟨ha ▸ a.property,(congrFun hz 0).symm.trans ((hsc a).trans (congrArg cc ha))⟩
    · rintro ⟨hp,hz⟩
      refine ⟨⟨p,hp⟩,rfl,?_⟩
      funext j
      fin_cases j
      exact (hsc ⟨p,hp⟩).trans hz.symm
  let F := forgetCoordinateLabelMap (PresentedSet.univ (pointSpace (M := M) n (1+m)) G.real)
  let I := Map.id (PresentedSet.univ (pointSpace (M := M) 1 0) G.real)
  have hccG : GammaScalarGraphDefinable G (fun p x => p ∈ carrier C ∧ x = cc p) := by
    apply GammaGraphDefinable.congr ((gammaLogicInput G).restrict_graph hC (hc.preimage_maps F I))
    intro p z
    change (p ∈ carrier C ∧ forgetCoordinateLabel p ∈ A ∧ vfAt z 0 = cc p) ↔
      (p ∈ carrier C ∧ vfAt z 0 = cc p)
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,forgetCoordinateLabel_mem AR i ⟨p,h.1⟩,h.2⟩⟩
  let D : Focus C i (Fin.castAdd m 0) := hullTranslationFocus (coordinateCanonical_tagged AR i) cc hindC hRVC hcc
  have hD : GammaFocusDefinable G D := hullTranslationFocus_gamma (A := C) hC
    (coordinateCanonical_tagged AR i) cc hindC hRVC hcc hccG
  let f := Map.comp (SpecialBijection.centripetal D).toMap can
  have hspecial : SpecialRelativeBoundary f i none (some true) :=
    specialRelativeBoundary_comp can (SpecialBijection.centripetal D).toMap i
      (coordinateCanonical_specialRelativeBoundary AR i none (by decide))
      (centripetal_specialRelativeBoundary D (some false) (by decide))
  have hGraph := gamma_composition_graph can (SpecialBijection.centripetal D).toMap
    (gamma_coordinateCanonical_graph AR hA i)
    (GammaPrimitiveDefinable.graph (gammaLogicInput G) (.centripetal D) ⟨hC,hD⟩)
  have hTarget := GammaPrimitiveDefinable.target (gammaLogicInput G) (.centripetal D) ⟨hC,hD⟩
  refine ⟨⟨S,hGS,AR,D.etaImage,rfl,f,hspecial,hGraph,hTarget,?_⟩⟩
  intro a
  have h := hullTranslationFocus_apply (A := C) (coordinateCanonical_tagged AR i) cc hindC hRVC hcc (can a)
  change (f a).val = replace i (coordinateCanonical i a.val)
    (vfAt (coordinateCanonical i a.val) i-cc (coordinateCanonical i a.val)) at h
  change (f a).val = replace i (coordinateCanonical i a.val)
    (vfAt (coordinateCanonical i a.val) i-c (forgetCoordinateLabel (coordinateCanonical i a.val))) at h
  rw [forgetCoordinateLabel_canonical] at h
  exact h

end IntegrationInACVF.Section5
