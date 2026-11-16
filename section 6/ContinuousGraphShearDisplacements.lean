import «section 6».GraphShearDisplacements
import «section 6».ContinuousInactiveDescent
import «section 6».PartialFocusRVFamilyTemplates

/-! The original-base inactive displacement family of a proper
stable shear is continuous for every pair of RV label tuples, including
its zero extension outside the actual projected graph domain. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S} {B : DefSet (rawMixedSpace (M := M) (n+1) s) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem graphShearBaseDisplacement_continuous
    (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : Map A B) (hF : ProperCovariantHomeomorphism f)
    (hStable : SameLabelShearDisplacement f (Fin.last n)) (w : Fin (r+s) → RVInfinity M) :
    Continuous (totalFocusFibre (graphShearBaseDisplacement hc f hStable) w) := by
  let u := w ∘ Fin.castAdd s
  let v := w ∘ Fin.natAdd r
  let D := graphFibreSource f u v
  let C := (vfDropLast (graphChartDomain hc f)).image
  let δ := graphShearBaseDisplacement hc f hStable
  let g (x : Fin (n+1) → VF M) : Fin 1 → VF M :=
    fun _ => graphFibreMap f u v x (Fin.last n)-x (Fin.last n)
  have hG : Continuous g := continuous_pi (fun _ =>
    ((continuous_apply (Fin.last n)).comp (hF.graphFibreMap_continuous hv u v)).sub (continuous_apply (Fin.last n)))
  have hFibre : vfFibre C.carrier w=Fin.init '' D := by
    rw [vfDropLast_image_fibre,graphChartDomain_fibre]
  obtain ⟨α,β,hα,hβ,hInv,hRange,hCov⟩ := hF.covariant.radii u v
  apply continuous_init_descent_of_invariant hv α D hInv g hG (totalFocusFibre δ w)
  · intro x hx
    have hxD : (x,w) ∈ (graphChartDomain hc f).carrier :=
      (Set.ext_iff.mp (graphChartDomain_fibre hc f w) x).mpr hx
    let q : graphChartDomain hc f := ⟨(x,w),hxD⟩
    have hxC : (Fin.init x,w) ∈ C.carrier := ⟨q,rfl⟩
    rw [totalFocusFibre_at δ w (Fin.init x) hxC]
    change (δ ((vfDropLast (graphChartDomain hc f)).toImage q)).val=g x
    rw [graphShearBaseDisplacement_factor]
    funext i
    have hi : i=(0 : Fin 1) := Subsingleton.elim _ _
    subst i
    change (graphChartScalarMap hc f (Fin.last n) q).val 0-x (Fin.last n)=g x 0
    have hAt := congrFun (totalGraphChartScalar_value hc f (Fin.last n) w x) 0
    rw [totalFocusFibre_at _ w x hxD] at hAt
    change (graphChartScalarMap hc f (Fin.last n) q).val 0=graphFibreMap f u v x (Fin.last n) at hAt
    rw [hAt]
  · intro b hb
    have hbC : (b,w) ∉ C.carrier := fun h => hb ((Set.ext_iff.mp hFibre b).mp h)
    exact totalFocusFibre_off δ w b hbC

theorem graphShearBaseDisplacement_family_definable
    (hc : CanonicalStructure.IsCanonical (M := M)) (f : Map A B)
    (hStable : SameLabelShearDisplacement f (Fin.last n)) :
    S.Definable LRV (rvVFGraph (totalFocusFibre (graphShearBaseDisplacement hc f hStable))) := by
  let δ := graphShearBaseDisplacement hc f hStable
  rw [rvVFGraph_eq_functionFamilyGraph (totalFocusFamilyCode δ) (totalFocusFibre δ) (totalFocusFamilyCode_at δ)]
  exact rvFunctionFamilyGraph_definable _ (totalFocusFamilyCode_definable δ)

end DiamondIntegral.Section6
