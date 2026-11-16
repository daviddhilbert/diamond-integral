import «section 6».RVGrafting
import «section 6».MixedInteriorRadii
import «section 6».GammaFormMaps
import «section 6».LocallyConstantGammaBounds

/-! Open fibres of an actual RV label map on a proper invariant source
have one uniform constancy radius. Least radii are selected on the
grafted graph and pulled back to the original bounded source before
applying the partition bound. No bound on the new labels is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r q : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {D : DefSet (rawMixedSpace (M := M) 0 q) S}

theorem graft_fibre_eq_label_source (hc : CanonicalStructure.IsCanonical (M := M)) (τ : Map A D)
    (w : Fin (r+q) → RVInfinity M) :
    vfFibre (graftMap hc τ).image.carrier w=graphFibreSource τ (w ∘ Fin.castAdd q) (w ∘ Fin.natAdd r) := by
  ext x
  rw [graft_image_fibre,graft_range_eq_source,graft_source_iff]
  exact and_iff_right rfl

theorem graft_fibre_replacement (hc : CanonicalStructure.IsCanonical (M := M)) (τ : Map A D)
    (p : A) (b : Fin n → VF M)
    (hb : (b,(graft hc τ p).val.2) ∈ (graftMap hc τ).image.carrier) :
    ∃ z : A,z.val=(b,p.val.2) ∧ (graft hc τ z).val.2=(graft hc τ p).val.2 := by
  obtain ⟨z,hz⟩ := hb
  change (graft hc τ z).val=(b,(graft hc τ p).val.2) at hz
  have hVF := congrArg Prod.fst hz
  have hTags := congrArg Prod.snd hz
  have hOld : z.val.2=p.val.2 := by
    funext i
    have h := congrFun hTags (Fin.castAdd q i)
    simpa only [graft_apply,Fin.append_left] using h
  exact ⟨z,Prod.ext hVF hOld,hTags⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_open_rv_label_radius_partition
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (τ : Map A D) (hOpen : ∀ u v,IsOpen (graphFibreSource τ u v)) :
    ∃ p : Mixed M n r → Gamma M,S.Definable LRV (mixedGammaGraph A.carrier p) ∧
      IsMixedOpenDiscPartition A.carrier p ∧
      ∀ a : A,IsLeast (InteriorRadii (vfFibre (graftMap hc τ).image.carrier (graft hc τ a).val.2) a.val.1) (p a.val) := by
  let H := (graftMap hc τ).image
  let g := graft hc τ
  have hHOpen (w) : IsOpen (vfFibre H.carrier w) := by
    rw [graft_fibre_eq_label_source hc τ w]
    exact hOpen _ _
  obtain ⟨pH,hLeast,hGraph⟩ := exists_mixed_least_interior_radius_graph h00 hc hv H.carrier
    (mixed_tuple_image_definable S H.carrier H.definable) hHOpen
  let P := (gammaFormMap H pH hGraph).comp g
  let p := gammaFormExtension P
  have hAt (a : A) : p a.val=pH (g a).val := by
    change gammaFormExtension P a.val=pH (g a).val
    rw [gammaFormExtension_at]
    rfl
  have hMin (a : A) :
      IsLeast (InteriorRadii (vfFibre H.carrier (g a).val.2) a.val.1) (p a.val) := by
    rw [hAt a]
    exact hLeast (g a).val (g a).property
  refine ⟨p,gammaFormExtension_graph_definable P,?_,hMin⟩
  intro u a ha b hb hNear
  let a₀ : A := ⟨(a,u),ha⟩
  let b₀ : A := ⟨(b,u),hb⟩
  have hbH : (b,(g a₀).val.2) ∈ H.carrier := (hMin a₀).1.2 hNear
  obtain ⟨z,hz,hTags⟩ := graft_fibre_replacement hc τ a₀ b hbH
  have hZ : z=b₀ := Subtype.ext hz
  have hBTags : (g b₀).val.2=(g a₀).val.2 := hZ ▸ hTags
  let w := (g a₀).val.2
  have hPart := least_interior_radii_partition (fun x => pH (x,w)) (fun x hx => hLeast (x,w) hx)
  have hNearH : b ∈ vfBall a (pH (a,w)) := by
    have he := hAt a₀
    change p (a,u)=pH (a,w) at he
    exact he ▸ hNear
  have hEq := hPart a (g a₀).property b hbH hNearH
  change p b₀.val=p a₀.val
  rw [hAt b₀,hAt a₀]
  have hBValue : (g b₀).val=(b,w) := Prod.ext rfl hBTags
  rw [hBValue]
  exact hEq

theorem open_rv_labels_uniform_radius
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (τ : Map A D) (hA : ProperInvariant S A.carrier)
    (hOpen : ∀ u v,IsOpen (graphFibreSource τ u v)) :
    ∃ δ : Gamma M,∀ p z : A,p.val.2=z.val.2 → Congruent (fun _ => δ) p.val.1 z.val.1 → τ p=τ z := by
  obtain ⟨p,hGraph,hPart,hMin⟩ := exists_open_rv_label_radius_partition h00 hc hv τ hOpen
  obtain ⟨δ,hδ⟩ := hA.partition_bounds h00 hc linear hκ hs hv hsmall hΓ p hPart hGraph
  refine ⟨δ,fun a b hTags hNear => ?_⟩
  have hbBall : b.val.1 ∈ vfBall a.val.1 (p a.val) := vfBall_anti (hδ a.val a.property).2 hNear.symm
  have hbH : (b.val.1,(graft hc τ a).val.2) ∈ (graftMap hc τ).image.carrier := (hMin a).1.2 hbBall
  obtain ⟨z,hz,hZTags⟩ := graft_fibre_replacement hc τ a b.val.1 hbH
  have hZ : z=b := Subtype.ext (hz.trans (Prod.ext rfl hTags))
  have hG : (graft hc τ b).val.2=(graft hc τ a).val.2 := hZ ▸ hZTags
  apply Subtype.ext
  apply Prod.ext
  · funext i
    exact i.elim0
  · funext i
    have h := congrFun hG (Fin.natAdd r i)
    simpa only [graft_apply,Fin.append_right] using h.symm

end DiamondIntegral.Section6
