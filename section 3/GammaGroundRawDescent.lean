import «section 3».GammaGroundRawLogic

/-! Passing to real-code predicates and back retains the complete
imaginary presentation. No representative is adjoined to the ground. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
section General
variable {L : Language} {M : Type} [L.Structure M]

def realCodeSpace (Q : Space L M) : Space L M where
  Carrier := Q.domain
  Index := Q.Index
  finiteIndex := Q.finiteIndex
  domain := Q.domain
  domain_definable := Q.domain_definable
  decode := id
  onto c := ⟨c, rfl⟩
  diagonal_definable := by
    have hl := Q.domain_definable.preimage_comp (Sum.inl : Q.Index → Q.Index ⊕ Q.Index)
    have hr := Q.domain_definable.preimage_comp (Sum.inr : Q.Index → Q.Index ⊕ Q.Index)
    have he : (∅ : Set M).Definable L {z : Q.Index ⊕ Q.Index → M | ∀ i, z (.inl i) = z (.inr i)} := by
      simp only [Set.ofPred_forall]
      exact Set.definable_iInter_of_finite (fun i =>
        (Set.DefinableFun.proj L).ofPred_eq (Set.DefinableFun.proj L))
    convert hl.inter (hr.inter he) using 1
    ext z
    constructor
    · rintro ⟨hp, hq, h⟩
      exact ⟨hp, hq, fun i => congrArg (fun c : Q.domain => c.val i) h⟩
    · rintro ⟨hp, hq, h⟩
      exact ⟨hp, hq, Subtype.ext (funext h)⟩

def realCodeDecodeMap (Q : Space L M) (S : Set M) :
    Map (DefSet.univ (realCodeSpace Q) S) (DefSet.univ Q S) :=
  Map.ofCodes _ Q.decode id (fun _ => Set.DefinableFun.proj L) (fun c => c.property) (fun _ => rfl)

def realCodeTupleMap (Q : Space L M) (S : Set M) :
    Map (DefSet.univ (realCodeSpace Q) S) (DefSet.univ (rawTupleSpace L M Q.Index) S) :=
  Map.ofCodes _ Subtype.val id (fun _ => Set.DefinableFun.proj L) (fun _ => Set.mem_univ _) (fun _ => rfl)
end General

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)}

theorem GammaGroundDefinable.of_real_codes {Q : Space LRV M} {A : Set Q.Carrier}
    (hA : GammaGroundRawDefinable hc ground (Q.preimage A)) : GammaGroundDefinable hc ground Q A := by
  have hcode := GammaGroundDefinable.preimage hA (realCodeTupleMap Q ground.real)
  have himg := hcode.image (realCodeDecodeMap Q ground.real)
  apply himg.congr
  intro y
  constructor
  · rintro ⟨c, hc, hy⟩
    exact hy ▸ (Q.preimage_decode A c).mp hc
  · intro hy
    obtain ⟨c, rfl⟩ := Q.onto y
    exact ⟨c, (Q.preimage_decode A c).mpr hy, rfl⟩

theorem gammaGroundDefinable_iff_raw_codes {Q : Space LRV M} {A : Set Q.Carrier} :
    GammaGroundDefinable hc ground Q A ↔ GammaGroundRawDefinable hc ground (Q.preimage A) :=
  ⟨GammaGroundDefinable.on_real_codes, GammaGroundDefinable.of_real_codes⟩

end DiamondIntegral.Section3
