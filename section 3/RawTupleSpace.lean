import «section 3».GammaGroundParameters
import Section4.RealPresentations
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M]

def rawTupleSpace (L : Language) (M : Type) [L.Structure M] (ι : Type) [Finite ι] : Space L M where
  Carrier := ι → M
  Index := ι
  finiteIndex := inferInstance
  domain := Set.univ
  domain_definable := Set.definable_univ
  decode := Subtype.val
  onto x := ⟨⟨x, Set.mem_univ _⟩, rfl⟩
  diagonal_definable := by
    have h : (∅ : Set M).Definable L {z : ι ⊕ ι → M | ∀ i, z (.inl i) = z (.inr i)} := by
      simp only [Set.ofPred_forall]
      exact Set.definable_iInter_of_finite (fun i =>
        (Set.DefinableFun.proj L).ofPred_eq (Set.DefinableFun.proj L))
    convert h using 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_univ, exists_prop, true_and]
    exact funext_iff

theorem rawTupleSpace_definable_iff {ι : Type} [Finite ι] {S : Set M} {A : Set (ι → M)} :
    (rawTupleSpace L M ι).Definable S A ↔ S.Definable L A := by
  have he : (rawTupleSpace L M ι).preimage A = A := by
    ext z
    simp [Space.preimage, rawTupleSpace]
  change S.Definable L _ ↔ _
  rw [he]

theorem ImaginaryDefinable.on_real_codes {P Q : Space L M} {p : P.Carrier} {S : Set M} {A : Set Q.Carrier}
    (hA : ImaginaryDefinable P p Q S A) :
    ImaginaryDefinable P p (rawTupleSpace L M Q.Index) S (Q.preimage A) := by
  obtain ⟨R, hR, hr⟩ := hA
  let D : Set (P.prod (rawTupleSpace L M Q.Index)).Carrier :=
    {z | ∃ hx : z.2 ∈ Q.domain, (z.1, Q.decode ⟨z.2, hx⟩) ∈ R}
  have hD : (P.prod (rawTupleSpace L M Q.Index)).Definable S D := by
    have he : (P.prod (rawTupleSpace L M Q.Index)).preimage D = (P.prod Q).preimage R := by
      ext z
      constructor
      · rintro ⟨⟨hp, _⟩, hq, hz⟩
        exact ⟨⟨hp, hq⟩, hz⟩
      · rintro ⟨⟨hp, hq⟩, hz⟩
        exact ⟨⟨hp, Set.mem_univ _⟩, hq, hz⟩
    change S.Definable L ((P.prod (rawTupleSpace L M Q.Index)).preimage D)
    rw [he]
    exact hR
  refine ⟨D, hD, fun x => ?_⟩
  change (∃ hx : x ∈ Q.domain, Q.decode ⟨x, hx⟩ ∈ A) ↔
    ∃ hx : x ∈ Q.domain, (p, Q.decode ⟨x, hx⟩) ∈ R
  exact exists_congr (fun hx => hr _)

end DiamondIntegral.Section3
