import IntegrationSection5.SurjectiveHeadFactorKernels
import IntegrationSection5.HeadProjectionPadding
import IntegrationSection5.GammaOrderedContraction
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
variable {S : Set M} {m b : ℕ} {R : DefSet (M := M) S 2 m} {B : DefSet (M := M) S 1 b}

def factorHeadProjection {r s : ℕ} (σT : Fin b → Fin r) (σU : Fin b → Fin s) (hU : Function.Bijective σU) :
    Fin (1+s) → Fin (1+r) := headPaddingProjection (σT ∘ (Equiv.ofBijective σU hU).symm)

theorem head_projection_of_factor (T U : HeadPreparation R)
    (σT : Fin b → Fin T.arity) (σU : Fin b → Fin U.arity) (hU : Function.Bijective σU)
    (d : Map R B)
    (hT : ∀ p : R, activeUnaryProjection 0 σT (T.map p).val = (d p).val)
    (hF : ∀ p : R, activeUnaryProjection 0 σU (U.map p).val = (d p).val) (p : R) :
    headKey (U.map p).val = activeUnaryProjection 0 (factorHeadProjection σT σU hU) (headKey (T.map p).val) := by
  apply Prod.ext
  · funext i; fin_cases i
    exact (specialRelative_unaryRelative U.special p 1 (by decide)).trans
      (specialRelative_unaryRelative T.special p 1 (by decide)).symm
  · funext j
    cases j using Fin.addCases with
    | left j =>
      fin_cases j
      have hz : factorHeadProjection σT σU hU (0 : Fin (1+U.arity)) = 0 :=
        Fin.append_left (fun _ : Fin 1 => 0) (Fin.natAdd 1 ∘ (σT ∘ (Equiv.ofBijective σU hU).symm)) (0 : Fin 1)
      change (headKey (U.map p).val).2 0 = (headKey (T.map p).val).2 (factorHeadProjection σT σU hU 0)
      rw [hz]
      change rv (vfAt (U.map p).val 0) = rv (vfAt (T.map p).val 0)
      exact congrArg rv ((congrArg (fun q : Point (M := M) 1 b => vfAt q 0) (hF p)).trans
        (congrArg (fun q : Point (M := M) 1 b => vfAt q 0) (hT p)).symm)
    | right j =>
      change (headKey (U.map p).val).2 (Fin.natAdd 1 j) =
        (headKey (T.map p).val).2 (factorHeadProjection σT σU hU (Fin.natAdd 1 j))
      rw [factorHeadProjection,headPaddingProjection,Fin.append_right]
      simp only [headKey,Function.comp_apply,Fin.append_right]
      change (U.map p).val.2 j = (T.map p).val.2 (σT ((Equiv.ofBijective σU hU).symm j))
      let k := (Equiv.ofBijective σU hU).symm j
      have hk : σU k = j := (Equiv.ofBijective σU hU).apply_symm_apply j
      have hu := congrFun (congrArg (fun q : Point (M := M) 1 b => q.2) (hF p)) k
      have ht := congrFun (congrArg (fun q : Point (M := M) 1 b => q.2) (hT p)) k
      change (U.map p).val.2 (σU k) = (d p).val.2 k at hu
      rw [hk] at hu
      exact hu.trans ht.symm

def headProjectionPaddingOfKernels (T U : HeadPreparation R)
    (σT : Fin b → Fin T.arity) (σU : Fin b → Fin U.arity) (hU : Function.Bijective σU)
    (d : Map R B)
    (hT : ∀ p : R, activeUnaryProjection 0 σT (T.map p).val = (d p).val)
    (hF : ∀ p : R, activeUnaryProjection 0 σU (U.map p).val = (d p).val)
    (hKernel : ∀ p q : R, T.contractionMap p = T.contractionMap q ↔ U.contractionMap p = U.contractionMap q)
    (hRV : ∀ p q : R, SameRV (T.contractionMap p).val (T.contractionMap q).val ↔
      SameRV (U.contractionMap p).val (U.contractionMap q).val)
    (hTΓ : GammaGraphDefinable G (pointMapGraph T.map)) (hTargetT : GammaSetDefinable G (carrier T.target))
    (hUΓ : GammaGraphDefinable G (pointMapGraph U.map)) (hTargetU : GammaSetDefinable G (carrier U.target)) :
    RVProjectionPadding (G := G) T.contractedSet U.contractedSet (factorHeadProjection σT σU hU) := by
  let q := T.contractionMap
  let f := U.contractionMap
  let e := gammaPointIsoOfSurjectiveKernels q T.contractionMap_surjective f U.contractionMap_surjective hKernel
    (gamma_headContraction_graph T hTΓ hTargetT) (gamma_headContraction_graph U hUΓ hTargetU)
  refine ⟨e,?_,?_⟩
  · intro p
    obtain ⟨a,rfl⟩ := T.contractionMap_surjective p
    change ((gammaPointIsoOfSurjectiveKernels q _ f _ hKernel _ _).equiv (q a)).val = _
    rw [gammaPointIsoOfSurjectiveKernels_square]
    change (headKeyMap U.target (U.map a)).val = activeUnaryProjection 0 (factorHeadProjection σT σU hU)
      (headKeyMap T.target (T.map a)).val
    rw [headKeyMap_apply,headKeyMap_apply]
    exact head_projection_of_factor T U σT σU hU d hT hF a
  · intro p r
    exact gammaPointIsoOfSurjectiveKernels_sameRV_iff q T.contractionMap_surjective f U.contractionMap_surjective hKernel
      (gamma_headContraction_graph T hTΓ hTargetT) (gamma_headContraction_graph U hUΓ hTargetU) hRV p r

end IntegrationInACVF.Section5
