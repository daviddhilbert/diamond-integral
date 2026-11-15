import IntegrationSection5.RVSliceHeadImages
import IntegrationSection5.HeadPreparation
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m a : ℕ}

theorem headSaturated_rvLabels (D : Set (Point (M := M) (n+1) m)) (hD : HeadSaturated D)
    (ρ : Fin a → Fin m) (E : Set (Fin a → RV (M := M))) :
    HeadSaturated {p | p ∈ D ∧ p.2 ∘ ρ ∈ E} := by
  intro p hp x hx
  exact ⟨hD p hp.1 x hx,hp.2⟩

namespace HeadPreparation
variable {A R : DefSet (M := M) S (n+1) m}

def rvSliceSubset (T : HeadPreparation A) (E : Set (Fin m → RV (M := M)))
    (hR : carrier R = {p | p ∈ carrier A ∧ p.2 ∈ E}) : carrier R ⊆ carrier A :=
  fun p hp => ((Set.ext_iff.mp hR p).mp hp).1

theorem rvSliceImage (T : HeadPreparation A) (E : Set (Fin m → RV (M := M)))
    (hR : carrier R = {p | p ∈ carrier A ∧ p.2 ∈ E}) :
    carrier (restrictPointImage T.map R (T.rvSliceSubset E hR)) =
      {q | q ∈ carrier T.target ∧ q.2 ∘ suffixIndex (specialRelative_rvArity_le T.special) ∈ E} := by
  apply restrictPointImage_rvSlice T.map T.bijective.2 _ _ E hR
  intro p
  funext j
  exact specialRelative_oldLabels T.special p j

def rvSliceRestriction (T : HeadPreparation A) (E : Set (Fin m → RV (M := M)))
    (hR : carrier R = {p | p ∈ carrier A ∧ p.2 ∈ E}) {previous ending : Option Bool}
    (hBound : SpecialRelativeBoundary T.map 0 previous ending) : HeadPreparation R where
  arity := T.arity
  target := restrictPointImage T.map R (T.rvSliceSubset E hR)
  map := restrictPointMap T.map R (T.rvSliceSubset E hR)
  special := specialRelativeBoundary_forget (specialRelativeBoundary_restrict T.map R (T.rvSliceSubset E hR) hBound)
  saturated := (T.rvSliceImage E hR).symm ▸ headSaturated_rvLabels (carrier T.target) T.saturated _ E

theorem rvSliceRestriction_gamma (T : HeadPreparation A) (E : Set (Fin m → RV (M := M)))
    (hR : carrier R = {p | p ∈ carrier A ∧ p.2 ∈ E}) {previous ending : Option Bool}
    (hBound : SpecialRelativeBoundary T.map 0 previous ending)
    (hRΓ : GammaSetDefinable G (carrier R)) (hTΓ : GammaGraphDefinable G (pointMapGraph T.map)) :
    GammaGraphDefinable G (pointMapGraph (T.rvSliceRestriction E hR hBound).map) :=
  gamma_restrictPointMap T.map R (T.rvSliceSubset E hR) hRΓ hTΓ

theorem rvSliceRestriction_target_gamma (T : HeadPreparation A) (E : Set (Fin m → RV (M := M)))
    (hR : carrier R = {p | p ∈ carrier A ∧ p.2 ∈ E}) {previous ending : Option Bool}
    (hBound : SpecialRelativeBoundary T.map 0 previous ending)
    (hRΓ : GammaSetDefinable G (carrier R)) (hTΓ : GammaGraphDefinable G (pointMapGraph T.map)) :
    GammaSetDefinable G (carrier (T.rvSliceRestriction E hR hBound).target) :=
  gamma_restrictPointImage T.map R (T.rvSliceSubset E hR) hRΓ hTΓ

end HeadPreparation
end IntegrationInACVF.Section5
