import «section 3».GammaGroundMapComposition

/-! Complete same-ground relations are closed under converse, finite
alternatives and composition, without naming imaginary representatives. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}
variable {P Q R : Space LRV M}

def GammaGroundRelationDefinable (hc : CanonicalStructure.IsCanonical (M := M))
    (ground : GammaParameters.Base (M := M)) (P Q : Space LRV M) (r : P.Carrier → Q.Carrier → Prop) : Prop :=
  GammaGroundDefinable hc ground (P.prod Q) {z | r z.1 z.2}

namespace GammaGroundRelationDefinable
variable {r t : P.Carrier → Q.Carrier → Prop} {s : Q.Carrier → R.Carrier → Prop}

theorem congr (hr : GammaGroundRelationDefinable hc ground P Q r) (h : ∀ x y, r x y ↔ t x y) :
    GammaGroundRelationDefinable hc ground P Q t := GammaGroundDefinable.congr hr (fun z => h z.1 z.2)

theorem symm (hr : GammaGroundRelationDefinable hc ground P Q r) :
    GammaGroundRelationDefinable hc ground Q P (fun y x => r x y) :=
  hr.preimage (universalProductSwap Q P ground.real)

theorem comp (hr : GammaGroundRelationDefinable hc ground P Q r)
    (hs : GammaGroundRelationDefinable hc ground Q R s) :
    GammaGroundRelationDefinable hc ground P R (fun x z => ∃ y, r x y ∧ s y z) := by
  have hh : GammaGroundDefinable hc ground (P.prod (Q.prod R)) {z | r z.1 z.2.1 ∧ s z.2.1 z.2.2} :=
    (hr.preimage (universalTripleFirstSecond P Q R ground.real)).inter
      (hs.preimage (universalProductSnd P (Q.prod R) ground.real))
  apply (hh.image (universalTripleFirstThird P Q R ground.real)).congr
  intro z
  constructor
  · rintro ⟨w, ⟨hF, hG⟩, hw⟩
    change (w.1, w.2.2) = z at hw
    have h1 := congrArg Prod.fst hw
    have h2 := congrArg Prod.snd hw
    exact ⟨w.2.1, h1 ▸ hF, h2 ▸ hG⟩
  · rintro ⟨y, hF, hG⟩
    exact ⟨(z.1, (y, z.2)), ⟨hF, hG⟩, rfl⟩

theorem exists_finite {ι : Type} [Finite ι] {T : ι → P.Carrier → Q.Carrier → Prop}
    (h : ∀ i, GammaGroundRelationDefinable hc ground P Q (T i)) :
    GammaGroundRelationDefinable hc ground P Q (fun x y => ∃ i, T i x y) := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  have hf : ∀ f : Finset ι, GammaGroundDefinable hc ground (P.prod Q) {z | ∃ i ∈ f, T i z.1 z.2} := by
    intro f
    induction f using Finset.induction_on with
    | empty =>
      apply (GammaGroundDefinable.of_real (DefSet.empty (P.prod Q) ground.real).definable).congr
      intro z
      simp [DefSet.empty]
    | @insert i f hi ih =>
      apply ((h i).union ih).congr
      intro z
      simp
  apply (hf Finset.univ).congr
  intro z
  simp

end GammaGroundRelationDefinable
end DiamondIntegral.Section3
