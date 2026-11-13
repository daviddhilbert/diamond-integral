import «section 3».ImaginaryParameters
import Section4.MapProduct

/-! Real-base definable maps act on named-imaginary definable sets by
images and inverse images without adding any real representative. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M]
variable {P Q R : Space L M} {S : Set M} {p : P.Carrier}

theorem ImaginaryDefinable.image {A : Set Q.Carrier}
    (hA : ImaginaryDefinable P p Q S A)
    (f : Map (DefSet.univ Q S) (DefSet.univ R S)) :
    ImaginaryDefinable P p R S {y | ∃ x ∈ A, (f ⟨x, Set.mem_univ _⟩).val = y} := by
  obtain ⟨T, hT, ht⟩ := hA
  let D : DefSet (P.prod Q) S := ⟨T, hT⟩
  let F : Map D ((DefSet.univ P S).prod (DefSet.univ R S)) :=
    (Map.prodMap (Map.id (DefSet.univ P S)) f).restrict (fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩)
  refine ⟨F.image.carrier, F.image.definable, fun y => ?_⟩
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ⟨⟨(p, x), (ht x).mp hx⟩, Prod.ext rfl hxy⟩
  · rintro ⟨a, ha⟩
    have hp : a.val.1 = p := congrArg Prod.fst ha
    have hxy : (f ⟨a.val.2, Set.mem_univ _⟩).val = y := congrArg Prod.snd ha
    refine ⟨a.val.2, (ht _).mpr ?_, hxy⟩
    exact (congrArg (fun z => (z, a.val.2) ∈ T) hp).mp a.property

theorem ImaginaryDefinable.preimage {A : Set R.Carrier}
    (hA : ImaginaryDefinable P p R S A)
    (f : Map (DefSet.univ Q S) (DefSet.univ R S)) :
    ImaginaryDefinable P p Q S {x | (f ⟨x, Set.mem_univ _⟩).val ∈ A} := by
  obtain ⟨T, hT, ht⟩ := hA
  let F := Map.prodMap (Map.id (DefSet.univ P S)) f
  let D : Set (P.prod Q).Carrier := {z | (F ⟨z, Set.mem_univ _, Set.mem_univ _⟩).val ∈ T}
  have hD : (P.prod Q).Definable S D := by
    have h := F.definable_preimage hT
    convert h using 1
    ext z
    constructor
    · intro hz
      exact ⟨⟨z, Set.mem_univ _, Set.mem_univ _⟩, rfl, hz⟩
    · rintro ⟨a, rfl, ha⟩
      exact ha
  exact ⟨D, hD, fun x => ht _⟩

end DiamondIntegral.Section3
