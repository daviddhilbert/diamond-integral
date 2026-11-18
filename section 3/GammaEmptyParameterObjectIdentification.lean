import «section 3».GammaEmptyIndexedMeasuredComparison

/-! The principal value of a complete empty-parameter row is the class
of its literal measured RV object. Both the empty index and harmless
degree reindexing are accounted for by actual measured arrows. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 SpecialTransformations.Section5
open IntegrationInACVF.Section6 IntegrationInACVF.Section6.FiniteRV IntegrationInACVF.Section7
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}

theorem gammaMeasuredPrincipalValue_reindex_degree {j l : ℕ} (h : j = l)
    (U : GammaGroundMeasuredRVObject hc B j) (e : Fin l ≃ Fin j) :
    gammaMeasuredPrincipalValue (U.reindexVolume e) = gammaMeasuredPrincipalValue U := by
  cases h
  exact gammaMeasuredPrincipalValue_iso
    (show GammaGroundMeasuredRVHom (U.reindexVolume e) U from
      ⟨GammaGroundBijection.id U.underlying.domain,U.reindex_combinedWeight e⟩)

theorem gammaEmptyParameterValue_actual_rv {k : ℕ}
    (U : GammaGroundMeasuredRVObject hc B (k+1))
    (F : GammaMeasuredRVSchema hc B 0 U.underlying.arity (k+1) (fun _ => .rv))
    (hF : F.valid Fin.elim0)
    (hD : ∀ r, r ∈ F.object.rowDomain Fin.elim0 ↔ r ∈ U.underlying.domain.carrier)
    (hV : ∀ r y, F.object.rowVolume Fin.elim0 r y ↔
      ∃ u : U.underlying.domain, u.val = r ∧ (U.underlying.volume u).val = y)
    (hW : ∀ r c, F.rowDensity Fin.elim0 r c ↔
      ∃ u : U.underlying.domain, u.val = r ∧ (U.form u).val = (volumeGammaSpace hc).decode c) :
    F.emptyParameterValue hF = gammaMeasuredPrincipalValue U := by
  let BP := gammaEmptyParameterIndex B
  let hAll := fun t (_ : t ∈ (Set.univ : Set (Fin 0 → RV (M := M)))) => F.emptyRV_valid hF t
  let P := F.emptyRV.object.indexedPresentation BP (fun t ht => (hAll t ht).1)
  let e : Fin ((0+k)+1) ≃ Fin (k+1) := finCongr (by omega)
  have H := gammaEmptyIndexed_measured_hom U F hF hD hV hW P
  have h : F.emptyParameterValue hF = gammaMeasuredPrincipalValue (U.reindexVolume e) :=
    gammaMeasuredPrincipalValue_iso H
  exact h.trans (gammaMeasuredPrincipalValue_reindex_degree (by omega) U e)

theorem gammaEmptyParameterValue_actual {k : ℕ} {sp : Fin 0 → SortTag}
    (U : GammaGroundMeasuredRVObject hc B (k+1))
    (F : GammaMeasuredRVSchema hc B 0 U.underlying.arity (k+1) sp)
    (hF : F.valid Fin.elim0)
    (hD : ∀ r, r ∈ F.object.rowDomain Fin.elim0 ↔ r ∈ U.underlying.domain.carrier)
    (hV : ∀ r y, F.object.rowVolume Fin.elim0 r y ↔
      ∃ u : U.underlying.domain, u.val = r ∧ (U.underlying.volume u).val = y)
    (hW : ∀ r c, F.rowDensity Fin.elim0 r c ↔
      ∃ u : U.underlying.domain, u.val = r ∧ (U.form u).val = (volumeGammaSpace hc).decode c) :
    F.emptyParameterValue hF = gammaMeasuredPrincipalValue U := by
  have he := gammaEmptyParameterSortEq sp
  cases he
  exact gammaEmptyParameterValue_actual_rv U F hF hD hV hW

end DiamondIntegral.Section3
