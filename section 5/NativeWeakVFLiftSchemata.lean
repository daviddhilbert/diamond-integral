import «section 5».NativeVFLiftEqualitySchemata
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
open DiamondIntegral.Section3 DiamondIntegral.Section4 Section3RVCodeBridge
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {B : Base (M := M)}
variable {p n r m s : ℕ} {sp : Fin p → SortTag}

def NativeVFLiftEqualitySchema.ValidWeak (hc : CanonicalStructure.IsCanonical (M := M))
    {kind : EulerKind} {D : Set (Fin (p+(n+r)) → M)} {E : Set (Fin (p+(m+s)) → M)}
    (W : NativeVFLiftEqualitySchema (B := B) (sp := sp) hc kind D E) (z : Fin p → M) : Prop :=
  W.leftRV.valid z ∧ W.rightRV.valid z ∧
    W.leftLift.valid D (finiteRVSchemaLiftDomain hc W.leftRV).val z ∧
      W.rightLift.valid E (finiteRVSchemaLiftDomain hc W.rightRV).val z ∧ W.evaluation.Valid hc z

theorem NativeVFLiftEqualitySchema.validWeak_definable (hc : CanonicalStructure.IsCanonical (M := M))
    {kind : EulerKind} {D : Set (Fin (p+(n+r)) → M)} {E : Set (Fin (p+(m+s)) → M)}
    (hD : DefinableOverBase B (Fin.append sp (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))) D)
    (hE : DefinableOverBase B (Fin.append sp (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv))) E)
    (W : NativeVFLiftEqualitySchema (B := B) (sp := sp) hc kind D E) :
    DefinableOverBase B sp {z | W.ValidWeak hc z} :=
  W.leftRV.valid_definable.inter
    (W.rightRV.valid_definable.inter
      ((W.leftLift.valid_definable hD (finiteRVSchemaLiftDomain hc W.leftRV).property).inter
        ((W.rightLift.valid_definable hE (finiteRVSchemaLiftDomain hc W.rightRV).property).inter
          (W.evaluation.valid_definable hc))))

theorem native_vf_weak_lift_equality_finite_catalog
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (hr : Cardinal.mk B.real < κ) (hγ : Cardinal.mk B.gamma < κ)
    (kind : EulerKind) (X : Set (Fin p → M)) (hX : DefinableOverBase B sp X)
    (D : Set (Fin (p+(n+r)) → M)) (E : Set (Fin (p+(m+s)) → M))
    (hD : DefinableOverBase B (Fin.append sp (Fin.append (fun _ : Fin n => .vf) (fun _ : Fin r => .rv))) D)
    (hE : DefinableOverBase B (Fin.append sp (Fin.append (fun _ : Fin m => .vf) (fun _ : Fin s => .rv))) E)
    (hrow : ∀ z ∈ X, ∃ W : NativeVFLiftEqualitySchema (B := B) (sp := sp) hc kind D E, W.ValidWeak hc z) :
    ∃ J : Finset (NativeVFLiftEqualitySchema (B := B) (sp := sp) hc kind D E),
      ∀ z ∈ X, ∃ W ∈ J, W.ValidWeak hc z :=
  gamma_finite_witnesses hκ hs hr hγ sp X hX
    (fun W : NativeVFLiftEqualitySchema (B := B) (sp := sp) hc kind D E => {z | W.ValidWeak hc z})
    (fun W => W.validWeak_definable hc hD hE) hrow

end DiamondIntegral.Section5
