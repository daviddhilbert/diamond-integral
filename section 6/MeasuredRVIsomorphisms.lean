import Section9.GammaJacobian
import «section 6».GammaMapArithmetic
import Section7.LiftedIsomorphism

/-! Actual finite-volume RV objects with Gamma forms and their measured
isomorphisms. The balance equation is the paper's Gamma Jacobian rule,
written in the multiplicative quotient group. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

structure MeasuredRVObject (S : Set M) (k : ℕ) where
  object : RVObject (M := M) S k
  finiteVolume : object.volume.FiniteFibres
  nonzero : ∀ u : object.domain, ∀ i, (object.value u i).val ≠ iRVZero
  form : Map object.domain (DefSet.univ (rawGammaPresentation (M := M)) S)

def MeasuredRVObject.volumeGamma (U : MeasuredRVObject (M := M) S k) (u : U.object.domain) : Gamma M :=
  rvVolumeGamma (U.object.value u) (U.nonzero u)

def MeasuredRVObject.totalWeight (U : MeasuredRVObject (M := M) S k) (u : U.object.domain) : Gamma M :=
  gammaMapValue U.form u * U.volumeGamma u

structure MeasuredRVIso (U V : MeasuredRVObject (M := M) S k) where
  iso : U.object ≅ V.object
  balance : ∀ u : U.object.domain, U.totalWeight u = V.totalWeight (iso.hom.map u)

def MeasuredRVIso.identity (U : MeasuredRVObject (M := M) S k) : MeasuredRVIso U U :=
  ⟨Iso.refl _,fun _ => rfl⟩

def MeasuredRVIso.comp {U V W : MeasuredRVObject (M := M) S k}
    (e : MeasuredRVIso U V) (f : MeasuredRVIso V W) : MeasuredRVIso U W :=
  ⟨e.iso ≪≫ f.iso,fun u => (e.balance u).trans (f.balance (e.iso.hom.map u))⟩

def MeasuredRVIso.symm {U V : MeasuredRVObject (M := M) S k} (e : MeasuredRVIso U V) :
    MeasuredRVIso V U := by
  refine ⟨e.iso.symm,fun v => ?_⟩
  have h := e.balance (e.iso.inv.map v)
  rw [SpecialTransformations.Section7.rvIso_apply_inv] at h
  exact h.symm

theorem MeasuredRVIso.gamma_jacobian {U V : MeasuredRVObject (M := M) S k} (e : MeasuredRVIso U V)
    (u : U.object.domain) :
    gammaMapValue U.form u / gammaMapValue V.form (e.iso.hom.map u) =
      rvGammaJacobian (U.object.value u) (V.object.value (e.iso.hom.map u))
        (U.nonzero u) (V.nonzero (e.iso.hom.map u)) := by
  have h := e.balance u
  change gammaMapValue U.form u * U.volumeGamma u =
    gammaMapValue V.form (e.iso.hom.map u) * V.volumeGamma (e.iso.hom.map u) at h
  change _ = V.volumeGamma (e.iso.hom.map u) / U.volumeGamma u
  apply (div_eq_div_iff_mul_eq_mul).mpr
  exact h.trans (mul_comm _ _)

def MeasuredRVObject.doublyBounded (U : MeasuredRVObject (M := M) S k) : Prop :=
  RVValueDoublyBounded U.object.domain.carrier ∧ RVValueDoublyBounded (Set.range U.object.value)

end DiamondIntegral.Section6
