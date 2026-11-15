import IntegrationSection5.BranchCanonicalFocus
import IntegrationSection5.GammaCoordinateCanonical
import IntegrationSection5.CentripetalRelativeBoundary
import IntegrationSection5.CanonicalTranslationPreparation
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)} {n m : ℕ}

def rvSliceSet (A : Set (Point (M := M) n m)) (E : Set (Fin m → RV (M := M))) :
    Set (Point (M := M) n m) := {p | p ∈ A ∧ p.2 ∈ E}

structure RVSliceTranslationPreparation (A : Set (Point (M := M) n m))
    (E : Set (Fin m → RV (M := M))) (i : Fin n) (c : Point (M := M) n m → VF (M := M)) where
  branch : CanonicalTranslationPreparation (G := G) (rvSliceSet A E) i c
  source : DefSet (M := M) branch.codes n m
  source_eq : carrier source = A
  target : DefSet (M := M) branch.codes n (1+m)
  map : Map source target
  special : SpecialRelativeBoundary map i none (some true)
  graph : GammaGraphDefinable G (pointMapGraph map)
  target_gamma : GammaSetDefinable G (carrier target)
  formula : ∀ p : source, (map p).val = if p.val.2 ∈ E then
    replace i (coordinateCanonical i p.val) (vfAt p.val i-c p.val) else coordinateCanonical i p.val
  active_image : carrier branch.target = {q | q ∈ carrier target ∧ q.2 ∘ Fin.natAdd 1 ∈ E}

theorem rvSlice_translation_preparation (A : Set (Point (M := M) n m))
    (hA : GammaSetDefinable G A) (E : Set (Fin m → RV (M := M)))
    (hN : GammaSetDefinable G (rvSliceSet A E)) (i : Fin n)
    (c : Point (M := M) n m → VF (M := M))
    (hind : ∀ p ∈ rvSliceSet A E, ∀ q ∈ rvSliceSet A E, erase i p = erase i q → c p = c q)
    (hRV : ∀ p ∈ rvSliceSet A E, rv (c p) = rv (vfAt p i))
    (hc : GammaScalarGraphDefinable G (fun p x => p ∈ rvSliceSet A E ∧ x = c p)) :
    Nonempty (RVSliceTranslationPreparation (G := G) A E i c) := by
  obtain ⟨S1,hGS1,hNr,hcr1⟩ := scalar_real_presentation (rvSliceSet A E) hN c hc
  obtain ⟨_,γ,_,H0,hH0⟩ := gammaPresentationInput G A hA
  let S0 := G.real ∪ Set.range (SpecialTransformations.Section3.GammaParameters.rawTuple γ)
  let S := S1 ∪ S0
  have hGS : G.real ⊆ S := fun x hx => Or.inl (hGS1 hx)
  have hNrS := SetDefinable.mono (pointSpace n m) hNr (Set.subset_union_left : S1 ⊆ S)
  have hArS : SetDefinable (pointSpace n m) S A := by
    rw [← hH0]
    exact SetDefinable.mono _ (setDefinable H0) (Set.subset_union_right : S0 ⊆ S)
  have hcr := RelationDefinable.mono (pointSpace n m) (SpecialTransformations.Section4.vfSpace 1)
    hcr1 (Set.subset_union_left : S1 ⊆ S)
  let AR : DefSet (M := M) S n m := @PresentedSet.mk M sM (pointSpace n m) S (rvSliceSet A E) hNrS
  let HR : DefSet (M := M) S n m := @PresentedSet.mk M sM (pointSpace n m) S A hArS
  let C := coordinateCanonicalImage AR i
  let can := coordinateCanonicalBijection AR i
  let canBij := coordinateCanonicalBijection_bijective AR i
  let cc : Point (M := M) n (1+m) → VF (M := M) := fun q => c (forgetCoordinateLabel q)
  have hC : GammaSetDefinable G (carrier C) := gamma_coordinateCanonicalImage AR hN i
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
    change (p ∈ carrier C ∧ forgetCoordinateLabel p ∈ rvSliceSet A E ∧ vfAt z 0 = cc p) ↔
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
    (gamma_coordinateCanonical_graph AR hN i)
    (GammaPrimitiveDefinable.graph (gammaLogicInput G) (.centripetal D) ⟨hC,hD⟩)
  have hTarget := GammaPrimitiveDefinable.target (gammaLogicInput G) (.centripetal D) ⟨hC,hD⟩
  have hFormula : ∀ a : AR, (f a).val = replace i (coordinateCanonical i a.val) (vfAt a.val i-c a.val) := by
    intro a
    have h := hullTranslationFocus_apply (A := C) (coordinateCanonical_tagged AR i) cc hindC hRVC hcc (can a)
    change (f a).val = replace i (coordinateCanonical i a.val)
      (vfAt (coordinateCanonical i a.val) i-cc (coordinateCanonical i a.val)) at h
    change (f a).val = replace i (coordinateCanonical i a.val)
      (vfAt (coordinateCanonical i a.val) i-c (forgetCoordinateLabel (coordinateCanonical i a.val))) at h
    rw [forgetCoordinateLabel_canonical] at h
    exact h
  let T : CanonicalTranslationPreparation (G := G) (rvSliceSet A E) i c :=
    ⟨S,hGS,AR,D.etaImage,rfl,f,hspecial,hGraph,hTarget,hFormula⟩
  have hSlice : carrier AR = {p | p ∈ carrier HR ∧ p.2 ∈ E} := rfl
  obtain ⟨K,g,hg,hK,hgG,hgForm,hgOff⟩ := rvSlice_canonical_focus_preparation i E hSlice D hA hD
  have hImage := canonical_focus_active_image i E hSlice D g
    (specialRelative_bijective (specialRelativeBoundary_forget hg)) hgForm
  refine ⟨⟨T,HR,rfl,K,g,hg,hgG,hK,?_,hImage⟩⟩
  intro p
  by_cases hp : p.val.2 ∈ E
  · rw [if_pos hp,hgForm]
    let pN : AR := ⟨p.val,⟨p.property,hp⟩⟩
    exact hFormula pN
  · rw [if_neg hp]
    exact hgOff p hp

end IntegrationInACVF.Section5
