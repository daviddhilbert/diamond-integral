import IntegrationSection5.PaddedProductCompletion
import IntegrationSection5.RVSliceMapImage
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
namespace IntegrationInACVF.Section5.PaddedProductCompletion
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {a b l : ℕ}
variable {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b} {H D : DefSet (M := M) S 1 l}
variable {u : SpecialBijection A B} {ρ : Fin a → Fin l} {E : Set (Fin a → RV (M := M))} {previous : Option Bool}

theorem inactive_vf (C : PaddedProductCompletion (G := G) u H ρ E previous)
    (p : H) (hp : p.val.2 ∘ ρ ∉ E) : vfAt (C.preparation.map p).val 0 = vfAt p.val 0 := by
  have hFlag : (C.preMap p).val.2 ∘ (Fin.natAdd 1 ∘ ρ) ∉ E := by
    rw [C.prefix_formula]
    exact (congrArg (fun s => s ∘ ρ) (coordinateCanonical_oldRV 0 p.val)).symm ▸ hp
  exact (C.head.inactive_vf (C.preMap p) hFlag).trans
    (congrArg (fun q : Point (M := M) 1 (1+l) => vfAt q 0) (C.prefix_formula p))

theorem inactive_sameRV (C : PaddedProductCompletion (G := G) u H ρ E previous)
    (p q : H) (hp : p.val.2 ∘ ρ ∉ E) (hq : q.val.2 ∘ ρ ∉ E) (he : SameRV p.val q.val) :
    SameRV (C.preparation.map p).val (C.preparation.map q).val := by
  have hFlag (p : H) (hp : p.val.2 ∘ ρ ∉ E) : (C.preMap p).val.2 ∘ (Fin.natAdd 1 ∘ ρ) ∉ E := by
    rw [C.prefix_formula]
    exact (congrArg (fun s => s ∘ ρ) (coordinateCanonical_oldRV 0 p.val)).symm ▸ hp
  apply C.head.inactive_sameRV (C.preMap p) (C.preMap q) (hFlag p hp) (hFlag q hq)
  rw [C.prefix_formula,C.prefix_formula]
  exact coordinateCanonical_sameRV 0 he

def inactivePadding (C : PaddedProductCompletion (G := G) u H ρ E previous)
    (hDH : carrier D ⊆ carrier H) (hDG : GammaSetDefinable G (carrier D))
    (hOff : ∀ p : D, p.val.2 ∘ ρ ∉ E) :
    RVProjectionPadding (G := G) (restrictPointImage C.preparation.map D hDH) D
      (suffixIndex (specialRelative_rvArity_le C.preparation.special)) :=
  inactiveProjectionPadding C.preparation.map C.preparation.bijective hDH hDG C.graph
    (fun p => C.inactive_vf ⟨p.val,hDH p.property⟩ (hOff p)) _
    (fun p => funext (specialRelative_oldLabels C.preparation.special p))
    (fun p q he => C.inactive_sameRV ⟨p.val,hDH p.property⟩ ⟨q.val,hDH q.property⟩ (hOff p) (hOff q) he)

end IntegrationInACVF.Section5.PaddedProductCompletion
