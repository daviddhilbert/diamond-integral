import «section 6».UnaryBoundaryCoreComponents
import «section 6».CoordinateCoreFormConstancy

/-! A boundary-core component and its regularization preserve exactly
equality of old labels. Their whole-disc image is tagged, so paired
whole-fibre matching survives both actual preparations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (F : UnaryFocusData A) (d : (Fin r → RVInfinity M) → VF M)
variable (E : CentripetalData (G := G) A)
variable (hCoord : E.coordinate=0) (hActive : E.activeTags=F.activeTags)
variable (hFocus : ∀ x u,E.focus x u=F.focus u-d u)
variable (hCore : ∀ p ∈ A.carrier,E.core p=false)
variable (hAll : ∀ p ∈ A.carrier,p.2 ∈ F.activeTags.carrier)
variable (hd : ∀ u ∈ F.activeTags.carrier,d u ≠ 0)
variable (hDiscs : ∀ u (hu : u ∈ F.activeTags.carrier) (x : VF M),
  ((fun _ : Fin 1 => x),u) ∈ A.carrier ↔ x ∈ centeredGammaDisc (F.focus u) (finiteValue (d u) (hd u hu)))
include hCoord hActive hFocus hCore hAll hd hDiscs

theorem unary_boundary_component_image_tagged :
    ∀ p ∈ E.map.image.carrier,∀ q ∈ E.map.image.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1 := by
  have hImage := unary_boundary_component_image F d E hCoord hActive hFocus hCore hAll hd hDiscs
  intro p hp q hq hTags
  rw [hImage] at hp hq
  obtain ⟨u,hu,hpu,hpRV⟩ := hp
  obtain ⟨v,hv,hqv,hqRV⟩ := hq
  have huv : u=v := by
    funext i
    have hh := congrFun (hpu.symm.trans (hTags.trans hqv)) (Fin.natAdd 1 i)
    simpa only [Fin.append_right] using hh
  funext i
  fin_cases i
  exact hpRV.trans ((congrArg (fun t => rv M (d t)) huv).trans hqRV.symm)

theorem unary_boundary_step_tags_iff (h00 : M ⊨ Axioms.ACVF00) (p q : A) :
    ((centripetalStepMap E) p).val.2=((centripetalStepMap E) q).val.2 ↔ p.val.2=q.val.2 := by
  constructor
  · exact fun h => (E.coordinate_step_same_labels h00 p q h).1
  · intro hTags
    have hComponentTags : (E.bijection p).val.2=(E.bijection q).val.2 := by
      change (E.point p.val).2=(E.point q.val).2
      simp only [CentripetalData.point,hCore p.val p.property,hCore q.val q.property,hTags]
    have hRV := unary_boundary_component_image_tagged F d E hCoord hActive hFocus hCore hAll hd hDiscs
      (E.bijection p).val (E.bijection p).property (E.bijection q).val (E.bijection q).property hComponentTags
    change Fin.append (tupleRV M (E.point p.val).1) (E.point p.val).2=
      Fin.append (tupleRV M (E.point q.val).1) (E.point q.val).2
    change tupleRV M (E.point p.val).1=tupleRV M (E.point q.val).1 at hRV
    change (E.point p.val).2=(E.point q.val).2 at hComponentTags
    rw [hRV,hComponentTags]

end DiamondIntegral.Section6
