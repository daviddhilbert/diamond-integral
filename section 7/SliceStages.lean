import «section 7».StageSlices
import «section 6».DiamondLift

/-! The slice of a contraction stage at a point, as a stage (for Lemma 7.23
with `n > 2`).

`StageSlices` restricts a stage `H` of `Y ⊆ VF^{m+1} × RV^r` to the slices over a
point `b ∈ VFᵐ`. When the slice of the exceptional set of `H` is small (VF
dimension `0`, or empty), these data form a standard contraction stage of the
unary slice `Y_b` over any base containing `S ∪ b` (`sliceStage`): its target is
the slice of the target of `H`, it retains the old labels of `H`, and its
leading label is that of `H`. Its contracted set is the RV fibre of the
contracted set of `H` over `b` (`mem_sliceStage_contracted`). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section9
open SpecialTransformations.Section4 SpecialTransformations.DefinableGeometry

namespace DiamondIntegral.Section7.SliceStages
open DiamondIntegral.Section6 DiamondIntegral.Section2
open DiamondIntegral.Section7.FibreRestriction DiamondIntegral.Section7.StageSlices

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {S S' : Set M} {m r : ℕ} {Y : DefSet (rawMixedSpace (M := M) (m + 1) r) S}
variable (H : StandardContractionStage (G := G) Y) (b : Fin m → VF M) (hS : S ∪ Set.range (vfValues b) ⊆ S')

omit [M ⊨ Axioms.ACVF] in
theorem defSet_eq {P : Space LRV M} {T : Set M} {A A' : DefSet P T} (h : A'.carrier = A.carrier) : A' = A := by
  cases A; cases A'
  cases h
  rfl

/-- Membership in the contracted set of the slice target. -/
theorem mem_targetSlice_contracted (w : Fin H.arity → RVInfinity M) :
    ((Fin.elim0, w) : Mixed M 0 H.arity) ∈ (vfDropLast (sliceSet H.target b hS)).image.carrier ↔
      ((b, w) : Mixed M m H.arity) ∈ H.contracted.carrier := by
  constructor
  · rintro ⟨p, hp⟩
    have h2 : p.val.2 = w := congrArg Prod.snd hp
    have hm := (mem_targetSlice H b hS p.val).mp p.property
    rw [h2] at hm
    exact hm.1
  · intro hw
    obtain ⟨x, hx⟩ := DiamondIntegral.Section2.tupleRV_surjective (M := M) (fun _ : Fin 1 => w H.leading)
    have hm : ((x, w) : Mixed M 1 H.arity) ∈ (sliceSet H.target b hS).carrier :=
      (mem_targetSlice H b hS (x, w)).mpr ⟨hw, congrFun hx 0⟩
    refine ⟨⟨_, hm⟩, ?_⟩
    change ((Fin.init x, w) : Mixed M 0 H.arity) = (Fin.elim0, w)
    exact Prod.ext (Subsingleton.elim _ _) rfl

/-- The slice of the target is the RV-disc bundle over its contracted set. -/
theorem targetSlice_bundle :
    (sliceSet H.target b hS).carrier =
      (rvCoordinateBundle (vfDropLast (sliceSet H.target b hS)).image H.leading).carrier := by
  ext ⟨x, w⟩
  change _ ↔ ((Fin.init x, w) : Mixed M 0 H.arity) ∈ (vfDropLast (sliceSet H.target b hS)).image.carrier ∧
    rv M (x (Fin.last 0)) = w H.leading
  have he : (Fin.init x : Fin 0 → VF M) = Fin.elim0 := Subsingleton.elim _ _
  rw [he, mem_targetSlice_contracted H b hS w, mem_targetSlice H b hS (x, w)]
  rfl

/-- **The slice of a stage at a point, as a stage.** -/
def sliceStage (hgood : vfDim (rawRVSpace (M := M) 1) (sliceSet H.exceptional b hS) < 1 ∨
      (sliceSet H.exceptional b hS).carrier = ∅) : StandardContractionStage (G := G) (sliceSet Y b hS) where
  arity := H.arity
  target := sliceSet H.target b hS
  lift := stageSlice H b hS
  home := stageSlice_homeo H b hS
  proper := targetSlice_proper H b hS
  doublyBounded := targetSlice_doublyBounded H b hS
  relative := fun _ i => i.elim0
  oldLabels := H.oldLabels
  oldLabels_injective := H.oldLabels_injective
  retained := stageSlice_retained H b hS
  leading := H.leading
  bundle := targetSlice_bundle H b hS
  exceptional := sliceSet H.exceptional b hS
  exceptional_subset := fun p hp => H.exceptional_subset hp
  exceptional_dim := by
    rcases hgood with h | h
    · exact h
    · have he : sliceSet H.exceptional b hS = DefSet.empty (rawMixedSpace (M := M) 1 r) S' :=
        defSet_eq (h.trans rfl)
      rw [he]
      exact DiamondIntegral.Section6.DiamondLift.vfDim_empty_lt 0
  unitDerivative := fun q hq => by
    have hnot : (liftElem q).val ∉ H.exceptional.carrier := hq
    obtain ⟨L, hL, hdet⟩ := H.unitDerivative (liftElem q) hnot
    obtain ⟨L₁, hL₁, hdet₁⟩ := sliceMap_derivative H.lift (stage_fix H) q hL
    exact ⟨L₁, hL₁, hdet₁.trans hdet⟩

theorem sliceStage_arity (hgood) : (sliceStage H b hS hgood).arity = H.arity := rfl
theorem sliceStage_oldLabels (hgood) : (sliceStage H b hS hgood).oldLabels = H.oldLabels := rfl
theorem sliceStage_leading (hgood) : (sliceStage H b hS hgood).leading = H.leading := rfl

/-- The contracted set of the slice stage is the RV fibre of the contracted set
of `H` over `b`. -/
theorem mem_sliceStage_contracted (hgood) (w : Fin H.arity → RVInfinity M) :
    ((Fin.elim0, w) : Mixed M 0 H.arity) ∈ (sliceStage H b hS hgood).contracted.carrier ↔
      ((b, w) : Mixed M m H.arity) ∈ H.contracted.carrier :=
  mem_targetSlice_contracted H b hS w

end DiamondIntegral.Section7.SliceStages
