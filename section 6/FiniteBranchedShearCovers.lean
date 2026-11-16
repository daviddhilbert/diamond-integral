import «section 6».PaddedBranchedShearAdmissibility

/-! Local witnesses yield a finite disjoint choice cover of complete
admissible templates, all with the same output arity, retained-label
selector and active leading coordinate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {p n r : ℕ}

structure FiniteBranchedShearCover
    (A : MixedSetParameterTemplate (M := M) S p (n+1) r) (U : Set (Fin p → M)) where
  arity : ℕ
  count : ℕ
  templates : Fin count → BranchedShearChartTemplate (M := M) S p n r arity
  labels : Fin r → Fin arity
  labels_injective : Function.Injective labels
  leading : Fin arity
  labels_eq : ∀ i,(templates i).labels=labels
  leading_eq : ∀ i,(templates i).leading=leading
  choices : Fin count → Set (Fin p → M)
  choices_definable : ∀ i,S.Definable LRV (choices i)
  choices_good : ∀ i,choices i ⊆ U ∩ (templates i).good A
  cover : ∀ a ∈ U,∃ i,a ∈ choices i
  disjoint : ∀ i j a,a ∈ choices i → a ∈ choices j → i=j

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_finite_branched_shear_cover
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {κ : Cardinal} (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (A : MixedSetParameterTemplate (M := M) S p (n+1) r)
    (U : Set (Fin p → M)) (hU : S.Definable LRV U)
    (hLocal : ∀ a ∈ U,Nonempty (BranchedShearData (G := G) (A.fibre a))) :
    Nonempty (FiniteBranchedShearCover A U) := by
  obtain ⟨k,arity,T,hCover⟩ := exists_finite_branched_shear_templates hv hs hsmall A U hU hLocal
  let P := fun i => paddedShearTemplate T i
  have hPCover : ∀ a ∈ U,∃ i,a ∈ (P i).good A := by
    intro a ha
    obtain ⟨i,hi⟩ := hCover a ha
    exact ⟨i,paddedShearTemplate_good hv T i A a hi⟩
  obtain ⟨C,hC,hSub,hCov,hDisj⟩ := exists_disjoint_definable_finite_choice U hU
    (fun i => (P i).good A) (fun i => (P i).good_definable A) hPCover
  exact ⟨{
    arity := packedBranchArity r arity
    count := k
    templates := P
    labels := packedBranchOld r arity
    labels_injective := packedBranchOld_injective arity
    leading := packedBranchLeading r arity
    labels_eq := fun _ => rfl
    leading_eq := fun _ => rfl
    choices := C
    choices_definable := hC
    choices_good := hSub
    cover := hCov
    disjoint := hDisj }⟩

end DiamondIntegral.Section6
