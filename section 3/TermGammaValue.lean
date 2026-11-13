import «section 3».CommonNamesGammaClosure
import Section3.RVExchange
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section3.GammaParameters
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

theorem gammaPullback_value_eq_same_scalar (t : CanonicalRV.RVSort M) (ht : t ≠ 0) :
    Values.gammaPullback {Values.gammaOf t (fun h => ht (Subtype.ext (h.trans RVOperations.zero_val.symm)))} =
      {x | SameScalar x t.val} := by
  ext x
  have ht0 : t.val ≠ iRVZero := fun h => ht (Subtype.ext (h.trans RVOperations.zero_val.symm))
  constructor
  · rintro ⟨hx,h0,hval⟩
    have he : Values.vrv ⟨x,hx⟩ = Values.vrv t := congrArg Subtype.val (Set.mem_singleton_iff.mp hval)
    exact ⟨⟨hx,h0⟩,⟨t.property,ht0⟩,(Values.vrv_eq_iff _ _).mp he⟩
  · intro hs
    refine ⟨hs.1.1,hs.1.2,?_⟩
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    exact (Values.vrv_eq_iff _ _).mpr hs.2.2

/-- A real-base definable nonzero RV point has a definable Gamma value,
via its complete same-value fibre, without naming another representative. -/
theorem gamma_value_definable_of_rv_definable (S : Set M) (t : CanonicalRV.RVSort M)
    (ht : t ≠ 0) (hdef : DefinableClosureAt S .rv t.val) :
    Values.GammaDefinable S {Values.gammaOf t (fun h => ht (Subtype.ext (h.trans RVOperations.zero_val.symm)))} := by
  let δ := Values.gammaOf t (fun h => ht (Subtype.ext (h.trans RVOperations.zero_val.symm)))
  let R : M → M → Prop := SameScalar
  let W := Values.gammaPullback {δ}
  have hW : W = {x | R x t.val} := gammaPullback_value_eq_same_scalar t ht
  have hproper : W ⊆ {x | sortEval SortTag.rv x} := fun _ hx => hx.choose
  have hd := (definableAt_iff_normalized_raw S .rv {t.val}).mp hdef |>.1
  have hsame : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 2)
      {z | R (z 0) (z 1)} := same_scalar_normalized_definable S
  have hN : @Set.Definable M S LRV (CanonicalStructure.normalize (M := M)) (Fin 1) {z | z 0 ∈ W} := by
    letI := CanonicalStructure.normalize (M := M)
    have hs := hd.preimage_comp (fun _ : Fin 1 => (1 : Fin 2))
    have hh := (hsame.inter hs).image_comp (fun _ : Fin 1 => (0 : Fin 2))
    convert hh using 1
    ext z
    simp only [Set.mem_image,Set.mem_inter_iff,Set.mem_preimage,Set.mem_ofPred_eq,Set.mem_singleton_iff,Function.comp_apply]
    change z 0 ∈ W ↔ ∃ w : Fin 2 → M,
      (R (w 0) (w 1) ∧ w 1 = t.val) ∧ (fun _ : Fin 1 => w 0) = z
    rw [hW]
    constructor
    · intro hz
      refine ⟨![z 0,t.val],⟨hz,rfl⟩,?_⟩
      funext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      rfl
    · rintro ⟨w,⟨hw,hw1⟩,he⟩
      have hw0 : w 0 = z 0 := congrFun he 0
      rwa [hw0,hw1] at hw
  exact (definableAt_iff_normalized_raw S .rv W).mpr ⟨hN,hproper⟩
end DiamondIntegral.Section3
