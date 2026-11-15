import IntegrationSection5.NonrectangleMatchedPrograms
import IntegrationSection5.FixedVFFiniteImage
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m u w : ℕ} {S : Set M}

def gammaSpecialIso {A : DefSet (M := M) S n m} {B : DefSet (M := M) S n w}
    (T : SpecialBijection A B) (hT : GammaChainDefinable G T.chain) :
    GammaIso G (carrier A) (carrier B) where
  equiv := T.equiv
  graph := GammaChainDefinable.graph (gammaLogicInput G) T.chain hT

theorem gammaIso_coordinate_image_finite {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    {A : Set (Point (M := M) n m)} {B : Set (Point (M := M) u w)}
    (e : GammaIso G A B) (i : Fin u) (x : Fin n → VF (M := M)) :
    {y : VF (M := M) | ∃ a : A, a.val.1 = x ∧ vfAt (e.equiv a).val i = y}.Finite :=
  fixed_vf_scalar_image_finite hκ hs G hsmall A (fun a => vfAt (e.equiv a).val i)
    (gamma_iso_coordinate_scalar_graph e i) x

theorem gammaIso_coordinate_finite_values {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk G.real < κ)
    {A : Set (Point (M := M) n m)} {B : Set (Point (M := M) u w)}
    (e : GammaIso G A B) (i : Fin u) (X : Set (Fin n → VF (M := M))) (hX : X.Finite) :
    {y : VF (M := M) | ∃ a : A, a.val.1 ∈ X ∧ vfAt (e.equiv a).val i = y}.Finite := by
  have h := hX.biUnion (fun x _ => gammaIso_coordinate_image_finite hκ hs hsmall e i x)
  apply h.subset
  rintro y ⟨a,ha,hy⟩
  exact Set.mem_biUnion ha ⟨a,rfl,hy⟩

namespace PositionedCellLabelInjection.NonrectangleMatchedHeads
variable {m : ℕ} {A : Set (Point (M := M) 2 m)} {T : PositionedCellLabelInjection G A}

def recoverA (Q : NonrectangleMatchedHeads T) :
    GammaIso G (carrier Q.unary.targetA) (carrier (Q.first.left.toHead Q.first.left_saturated).contractedSet) :=
  gammaIsoCastTarget ((gammaSpecialIso Q.unary.specialA Q.unary.gammaA).symm (gammaLogicInput G))
    Q.unary.sourceA_eq

def recoverB (Q : NonrectangleMatchedHeads T) :
    GammaIso G (carrier Q.unary.targetB) (carrier (Q.first.right.toHead Q.first.right_saturated).contractedSet) :=
  gammaIsoCastTarget ((gammaSpecialIso Q.unary.specialB Q.unary.gammaB).symm (gammaLogicInput G))
    Q.unary.sourceB_eq

theorem recoverA_values (Q : NonrectangleMatchedHeads T) (a : Q.unary.targetA) :
    (Q.recoverA.equiv a).val = (Q.unary.specialA.inverseMap a).val :=
  gammaIsoCastTarget_apply _ _ a

theorem recoverB_values (Q : NonrectangleMatchedHeads T) (a : Q.unary.targetB) :
    (Q.recoverB.equiv a).val = (Q.unary.specialB.inverseMap a).val :=
  gammaIsoCastTarget_apply _ _ a

end PositionedCellLabelInjection.NonrectangleMatchedHeads
end IntegrationInACVF.Section5
