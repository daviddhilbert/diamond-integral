import «section 6».RVTupleAssembly
import «section 6».RVUnaryChainConditions

/-! On finite nonzero volume domains every definable label bijection is
an actual RV isomorphism. The finite-volume-image clauses and equal
weights are proved explicitly. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

def rvIsoOfFiniteNonzeroDomains {U V : RVObject (M := M) S n}
    (F : Map U.domain V.domain) (hF : Function.Bijective F)
    (hUF : U.domain.carrier.Finite) (hVF : V.domain.carrier.Finite)
    (hU : ∀ u i, (U.value u i).val ≠ iRVZero)
    (hV : ∀ v i, (V.value v i).val ≠ iRVZero) : U ≅ V where
  hom := {
    map := F
    volumetric u := by simp [rvWeight,hU u,hV (F u)]
    finite_volume_images t := by
      letI : Finite U.domain := hUF.to_subtype
      apply (Set.finite_range (fun u : U.domain => V.value (F u))).subset
      rintro s ⟨u,_,he⟩
      exact ⟨u,he⟩ }
  inv := {
    map := F.inverse hF
    volumetric v := by simp [rvWeight,hV v,hU (F.inverse hF v)]
    finite_volume_images t := by
      letI : Finite V.domain := hVF.to_subtype
      apply (Set.finite_range (fun v : V.domain => U.value (F.inverse hF v))).subset
      rintro s ⟨v,_,he⟩
      exact ⟨v,he⟩ }
  hom_inv_id := by apply RVHom.ext; apply Map.ext; intro u; exact Map.inverse_apply F hF u
  inv_hom_id := by apply RVHom.ext; apply Map.ext; intro v; exact Map.apply_inverse F hF v

def RVUnaryChain.comp {U V W : RVObject (M := M) S n} :
    RVUnaryChain S n U V → RVUnaryChain S n V W → RVUnaryChain S n U W
  | .identity _,H => H
  | .step i e h T,H => .step i e h (T.comp H)

theorem RVUnaryChain.comp_map {U V W : RVObject (M := M) S n}
    (T : RVUnaryChain S n U V) (H : RVUnaryChain S n V W) (u : U.domain) :
    (T.comp H).iso.hom.map u = H.iso.hom.map (T.iso.hom.map u) := by
  induction T with
  | identity U => rfl
  | step i e h T ih => exact ih H (e.hom.map u)

theorem RVUnaryChain.comp_finiteVolume {U V W : RVObject (M := M) S n}
    (T : RVUnaryChain S n U V) (H : RVUnaryChain S n V W)
    (hT : T.finiteVolume) (hH : H.finiteVolume) : (T.comp H).finiteVolume := by
  induction T with
  | identity U => exact hH
  | step i e h T ih => exact ⟨hT.1,ih H hT.2 hH⟩

end DiamondIntegral.Section6
