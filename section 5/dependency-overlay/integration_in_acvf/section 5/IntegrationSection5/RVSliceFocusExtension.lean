import IntegrationSection5.FocusExtension
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
variable {S : Set M} {n m : ℕ}

theorem rv_labels_predicate_hull {A : DefSet (M := M) S n m}
    (E : Set (Fin m → RV (M := M))) (hA : ∀ p ∈ carrier A, p.2 ∈ E)
    (p : Point (M := M) n m) (hp : p ∈ hull (carrier A)) : p.2 ∈ E := by
  obtain ⟨q,hq,he⟩ := hp
  exact ((sameRV_iff _ _).mp he).2 ▸ hA q hq

namespace Focus
variable {A H : DefSet (M := M) S n m} {i : Fin n} {k : Fin m}

theorem rvSlice_active_condition (D : SpecialTransformations.Section5.Focus A i k)
    (E : Set (Fin m → RV (M := M)))
    (hA : carrier A = {p | p ∈ carrier H ∧ p.2 ∈ E})
    (p : Point (M := M) n m) (hp : p ∈ carrier H) (hl : p ∈ D.locus) : p ∈ carrier A := by
  apply (Set.ext_iff.mp hA p).mpr
  exact ⟨hp,rv_labels_predicate_hull E (fun q hq => ((Set.ext_iff.mp hA q).mp hq).2)
    p (D.locus_subset hl)⟩

def rvSliceExtend (D : SpecialTransformations.Section5.Focus A i k)
    (E : Set (Fin m → RV (M := M)))
    (hA : carrier A = {p | p ∈ carrier H ∧ p.2 ∈ E})
    (kH : Fin m) (hTag : Tagged (carrier H) i kH) :
    SpecialTransformations.Section5.Focus H i kH :=
  extend D kH hTag (rvSlice_active_condition D E hA)

theorem rvSliceExtend_eta (D : SpecialTransformations.Section5.Focus A i k)
    (E : Set (Fin m → RV (M := M)))
    (hA : carrier A = {p | p ∈ carrier H ∧ p.2 ∈ E})
    (kH : Fin m) (hTag : Tagged (carrier H) i kH)
    (p : Point (M := M) n m) (hp : p ∈ carrier H) :
    (rvSliceExtend D E hA kH hTag).toFocusGeometry.eta p = D.toFocusGeometry.eta p :=
  extend_eta D kH hTag (rvSlice_active_condition D E hA) p hp

theorem rvSliceExtend_inactive (D : SpecialTransformations.Section5.Focus A i k)
    (E : Set (Fin m → RV (M := M)))
    (hA : carrier A = {p | p ∈ carrier H ∧ p.2 ∈ E})
    (kH : Fin m) (hTag : Tagged (carrier H) i kH)
    (p : Point (M := M) n m) (hp : p ∈ carrier H) (hOff : p.2 ∉ E) :
    (rvSliceExtend D E hA kH hTag).toFocusGeometry.eta p = p := by
  rw [rvSliceExtend_eta D E hA kH hTag p hp]
  apply if_neg
  intro hl
  exact hOff (((Set.ext_iff.mp hA p).mp (rvSlice_active_condition D E hA p hp hl)).2)

theorem rvSliceExtend_gamma {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
    (D : SpecialTransformations.Section5.Focus A i k)
    (E : Set (Fin m → RV (M := M)))
    (hA : carrier A = {p | p ∈ carrier H ∧ p.2 ∈ E})
    (kH : Fin m) (hTag : Tagged (carrier H) i kH)
    (hH : GammaSetDefinable G (carrier H)) (hD : GammaFocusDefinable G D) :
    GammaFocusDefinable G (rvSliceExtend D E hA kH hTag) :=
  extend_gamma D kH hTag (rvSlice_active_condition D E hA) hH hD

end Focus
end IntegrationInACVF.Section5
