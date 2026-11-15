import IntegrationSection5.RVSliceFocusExtension
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
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m : ℕ} {A H : DefSet (M := M) S n m}

theorem coordinateCanonical_rvSlice (i : Fin n) (E : Set (Fin m → RV (M := M)))
    (hA : carrier A = {p | p ∈ carrier H ∧ p.2 ∈ E}) :
    carrier (coordinateCanonicalImage A i) =
      {q | q ∈ carrier (coordinateCanonicalImage H i) ∧ q.2 ∘ Fin.natAdd 1 ∈ E} := by
  ext q
  constructor
  · rintro ⟨a,rfl⟩
    have ha := (Set.ext_iff.mp hA a.val).mp a.property
    refine ⟨⟨⟨a.val,ha.1⟩,rfl⟩,?_⟩
    have he : (coordinateCanonical i a.val).2 ∘ Fin.natAdd 1 = a.val.2 := by
      funext j; simp only [Function.comp_apply,coordinateCanonical,Fin.append_right]
    change (coordinateCanonical i a.val).2 ∘ Fin.natAdd 1 ∈ E
    rw [he]
    exact ha.2
  · rintro ⟨⟨a,rfl⟩,ha⟩
    have he : (coordinateCanonical i a.val).2 ∘ Fin.natAdd 1 = a.val.2 := by
      funext j; simp only [Function.comp_apply,coordinateCanonical,Fin.append_right]
    change (coordinateCanonical i a.val).2 ∘ Fin.natAdd 1 ∈ E at ha
    rw [he] at ha
    exact ⟨⟨a.val,(Set.ext_iff.mp hA a.val).mpr ⟨a.property,ha⟩⟩,rfl⟩

theorem rvSlice_canonical_focus_preparation (i : Fin n) (E : Set (Fin m → RV (M := M)))
    (hA : carrier A = {p | p ∈ carrier H ∧ p.2 ∈ E})
    (D : SpecialTransformations.Section5.Focus (coordinateCanonicalImage A i) i (0 : Fin (1+m)))
    (hH : GammaSetDefinable G (carrier H)) (hD : GammaFocusDefinable G D) :
    ∃ K : DefSet (M := M) S n (1+m), ∃ f : Map H K,
      SpecialRelativeBoundary f i none (some true) ∧
      GammaSetDefinable G (carrier K) ∧ GammaGraphDefinable G (pointMapGraph f) ∧
      (∀ p : H, (f p).val = D.toFocusGeometry.eta (coordinateCanonical i p.val)) ∧
      (∀ p : H, p.val.2 ∉ E → (f p).val = coordinateCanonical i p.val) := by
  let C := coordinateCanonicalImage H i
  let E' : Set (Fin (1+m) → RV (M := M)) := {s | s ∘ Fin.natAdd 1 ∈ E}
  have hAC : carrier (coordinateCanonicalImage A i) = {p | p ∈ carrier C ∧ p.2 ∈ E'} :=
    coordinateCanonical_rvSlice i E hA
  let F := Focus.rvSliceExtend D E' hAC 0 (coordinateCanonical_tagged H i)
  let can := coordinateCanonicalBijection H i
  let eta := (SpecialBijection.centripetal F).toMap
  have hC := gamma_coordinateCanonicalImage H hH i
  have hFG : GammaFocusDefinable G F := Focus.rvSliceExtend_gamma D E' hAC 0
    (coordinateCanonical_tagged H i) hC hD
  have hK := GammaPrimitiveDefinable.target (gammaLogicInput G) (.centripetal F) ⟨hC,hFG⟩
  have hGraph := gamma_composition_graph can eta (gamma_coordinateCanonical_graph H hH i)
    (GammaPrimitiveDefinable.graph (gammaLogicInput G) (.centripetal F) ⟨hC,hFG⟩)
  refine ⟨F.etaImage,Map.comp eta can,?_,hK,hGraph,?_,?_⟩
  · exact specialRelativeBoundary_comp can eta i
      (coordinateCanonical_specialRelativeBoundary H i none (by decide))
      (centripetal_specialRelativeBoundary F (some false) (by decide))
  · intro p
    exact Focus.rvSliceExtend_eta D E' hAC 0 (coordinateCanonical_tagged H i) (can p).val (can p).property
  · intro p hp
    apply Focus.rvSliceExtend_inactive D E' hAC 0 (coordinateCanonical_tagged H i) (can p).val (can p).property
    change (coordinateCanonical i p.val).2 ∘ Fin.natAdd 1 ∉ E
    have he : (coordinateCanonical i p.val).2 ∘ Fin.natAdd 1 = p.val.2 := by
      funext j; simp only [Function.comp_apply,coordinateCanonical,Fin.append_right]
    rwa [he]


theorem canonical_focus_active_image {K : DefSet (M := M) S n (1+m)}
    (i : Fin n) (E : Set (Fin m → RV (M := M)))
    (hA : carrier A = {p | p ∈ carrier H ∧ p.2 ∈ E})
    (D : SpecialTransformations.Section5.Focus (coordinateCanonicalImage A i) i (0 : Fin (1+m)))
    (f : Map H K) (hf : Function.Bijective f)
    (hForm : ∀ p : H, (f p).val = D.toFocusGeometry.eta (coordinateCanonical i p.val)) :
    carrier D.etaImage = {q | q ∈ carrier K ∧ q.2 ∘ Fin.natAdd 1 ∈ E} := by
  have hLabels (p : H) : (f p).val.2 ∘ Fin.natAdd 1 = p.val.2 := by
    rw [hForm,D.toFocusGeometry.eta_labels]
    funext j
    simp only [Function.comp_apply,coordinateCanonical,Fin.append_right]
  ext q
  constructor
  · rintro ⟨c,rfl⟩
    change D.toFocusGeometry.eta c.val ∈ carrier K ∧
      (D.toFocusGeometry.eta c.val).2 ∘ Fin.natAdd 1 ∈ E
    obtain ⟨b,hb⟩ := c.property
    have hbA := (Set.ext_iff.mp hA b.val).mp b.property
    let bH : H := ⟨b.val,hbA.1⟩
    have hVal : (f bH).val = D.toFocusGeometry.eta c.val := by
      rw [hForm]
      exact congrArg D.toFocusGeometry.eta hb
    refine ⟨hVal ▸ (f bH).property,?_⟩
    rw [← hVal,hLabels]
    exact hbA.2
  · rintro ⟨hq,hE⟩
    obtain ⟨p,hp⟩ := hf.2 ⟨q,hq⟩
    have hpv : (f p).val = q := congrArg (fun z : K => z.val) hp
    have hpE : p.val.2 ∈ E := by rw [← hLabels p,hpv]; exact hE
    let a : A := ⟨p.val,(Set.ext_iff.mp hA p.val).mpr ⟨p.property,hpE⟩⟩
    exact ⟨coordinateCanonicalBijection A i a,(hForm p).symm.trans hpv⟩

theorem canonical_focus_inactive_image {K : DefSet (M := M) S n (1+m)}
    (i : Fin n) (E : Set (Fin m → RV (M := M)))
    (D : SpecialTransformations.Section5.Focus (coordinateCanonicalImage A i) i (0 : Fin (1+m)))
    (f : Map H K) (hf : Function.Bijective f)
    (hForm : ∀ p : H, (f p).val = D.toFocusGeometry.eta (coordinateCanonical i p.val))
    (hOff : ∀ p : H, p.val.2 ∉ E → (f p).val = coordinateCanonical i p.val) :
    {q | q ∈ carrier K ∧ q.2 ∘ Fin.natAdd 1 ∉ E} =
      {q | ∃ p : H, p.val.2 ∉ E ∧ coordinateCanonical i p.val = q} := by
  have hLabels (p : H) : (f p).val.2 ∘ Fin.natAdd 1 = p.val.2 := by
    rw [hForm,D.toFocusGeometry.eta_labels]
    funext j
    simp only [Function.comp_apply,coordinateCanonical,Fin.append_right]
  ext q
  constructor
  · rintro ⟨hq,hE⟩
    obtain ⟨p,hp⟩ := hf.2 ⟨q,hq⟩
    have hpv : (f p).val = q := congrArg (fun z : K => z.val) hp
    have hpE : p.val.2 ∉ E := by rw [← hLabels p,hpv]; exact hE
    exact ⟨p,hpE,(hOff p hpE).symm.trans hpv⟩
  · rintro ⟨p,hp,hpq⟩
    have hpv : (f p).val = q := (hOff p hp).trans hpq
    refine ⟨hpv ▸ (f p).property,?_⟩
    rw [← hpv,hLabels]
    exact hp

end IntegrationInACVF.Section5
