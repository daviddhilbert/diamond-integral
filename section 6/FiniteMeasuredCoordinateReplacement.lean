import «section 6».FiniteRVFactorizations
import «section 6».StructuralRVMeasures

/-! Intermediate measured objects for finite coordinate replacement.
Their actual Gamma forms keep the original total weight exactly, while
all original RV labels and finite volume fibres are retained. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def measuredPartialReplacement (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V) (I : Finset (Fin n))
    (hFin : U.object.domain.carrier.Finite) : MeasuredRVObject (M := M) S n where
  object := rvPartialReplacement U.object (V.object.volume.comp e.iso.hom.map) I
  finiteVolume := rvPartialReplacement_finiteVolume U.object _ I hFin
  nonzero := rvPartialReplacement_nonzero U.object _ I U.nonzero (fun u => V.nonzero (e.iso.hom.map u))
  form := gammaMapDiv hc (gammaMapMul hc U.form (rvVolumeGammaMap hc U.object))
    (rvVolumeGammaMap hc (rvPartialReplacement U.object (V.object.volume.comp e.iso.hom.map) I))

theorem measuredPartialReplacement_totalWeight (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V) (I : Finset (Fin n))
    (hFin : U.object.domain.carrier.Finite) (u : U.object.domain) :
    (measuredPartialReplacement hc e I hFin).totalWeight u = U.totalWeight u := by
  let W := measuredPartialReplacement hc e I hFin
  change ((gammaMapValue U.form u * gammaMapValue (rvVolumeGammaMap hc U.object) u) /
    gammaMapValue (rvVolumeGammaMap hc W.object) u) * W.volumeGamma u = U.totalWeight u
  rw [rvVolumeGammaMap_value hc U.object U.nonzero,rvVolumeGammaMap_value hc W.object W.nonzero]
  change (U.totalWeight u / W.volumeGamma u) * W.volumeGamma u = U.totalWeight u
  exact div_mul_cancel _ _

def measuredPartialReplacementStep (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V) (I : Finset (Fin n)) (i : Fin n)
    (hFin : U.object.domain.carrier.Finite) :
    MeasuredRVIso (measuredPartialReplacement hc e I hFin) (measuredPartialReplacement hc e (insert i I) hFin) where
  iso := rvPartialReplacementStep U.object (V.object.volume.comp e.iso.hom.map) I i hFin
    U.nonzero (fun u => V.nonzero (e.iso.hom.map u))
  balance u := (measuredPartialReplacement_totalWeight hc e I hFin u).trans
    (measuredPartialReplacement_totalWeight hc e (insert i I) hFin u).symm

def MeasuredRVUnaryChain.comp {U V W : MeasuredRVObject (M := M) S n} :
    MeasuredRVUnaryChain S n U V → MeasuredRVUnaryChain S n V W → MeasuredRVUnaryChain S n U W
  | .identity _,H => H
  | .step i e h T,H => .step i e h (T.comp H)

theorem MeasuredRVUnaryChain.comp_map {U V W : MeasuredRVObject (M := M) S n}
    (T : MeasuredRVUnaryChain S n U V) (H : MeasuredRVUnaryChain S n V W) (u : U.object.domain) :
    (T.comp H).iso.iso.hom.map u = H.iso.iso.hom.map (T.iso.iso.hom.map u) := by
  induction T with
  | identity U => rfl
  | step i e h T ih => exact ih H (e.iso.hom.map u)

theorem exists_finite_measured_replacement_chain (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V) (I : Finset (Fin n))
    (hFin : U.object.domain.carrier.Finite) :
    ∃ T : MeasuredRVUnaryChain S n (measuredPartialReplacement hc e ∅ hFin) (measuredPartialReplacement hc e I hFin),
      ∀ u, T.iso.iso.hom.map u = u := by
  induction I using Finset.induction_on with
  | empty => exact ⟨.identity _,fun _ => rfl⟩
  | @insert i I hi ih =>
    obtain ⟨T,hT⟩ := ih
    let H : MeasuredRVUnaryChain S n (measuredPartialReplacement hc e I hFin)
        (measuredPartialReplacement hc e (insert i I) hFin) :=
      .step i (measuredPartialReplacementStep hc e I i hFin)
        (rvPartialReplacementStep_unary U.object _ I i hFin U.nonzero
          (fun u => V.nonzero (e.iso.hom.map u))) (.identity _)
    refine ⟨T.comp H,fun u => ?_⟩
    rw [MeasuredRVUnaryChain.comp_map,hT]
    rfl

end DiamondIntegral.Section6
