import «section 3».FiniteFamilies
import Section4.RealPresentations
import Section4.MapCorestrict

/-! The real codes of an imaginary presentation form a definable real
space. Its quotient map keeps every representative. For Gamma powers these
are exactly the nonzero RV representatives used in a valuation contraction. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry

noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M] {S : Set M}

def codeSpace (P : Space L M) : Space L M where
  Carrier := P.domain
  Index := P.Index
  finiteIndex := inferInstance
  domain := P.domain
  domain_definable := P.domain_definable
  decode z := z
  onto := Function.surjective_id
  diagonal_definable := by
    have hl := P.domain_definable.preimage_comp (Sum.inl : P.Index → P.Index ⊕ P.Index)
    have hr := P.domain_definable.preimage_comp (Sum.inr : P.Index → P.Index ⊕ P.Index)
    have he (i : P.Index) : (∅ : Set M).Definable L
        {z : P.Index ⊕ P.Index → M | z (.inl i) = z (.inr i)} :=
      (Set.DefinableFun.proj L).ofPred_eq (Set.DefinableFun.proj L)
    convert hl.inter (hr.inter (Set.definable_iInter_of_finite he)) using 1
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter]
    constructor
    · rintro ⟨hx, hy, hxy⟩
      exact ⟨hx, hy, fun i => congrFun (congrArg Subtype.val hxy) i⟩
    · rintro ⟨hx, hy, hxy⟩
      exact ⟨hx, hy, Subtype.ext (funext hxy)⟩

def codePreimage {P : Space L M} (A : DefSet P S) : DefSet (codeSpace P) S where
  carrier := {c | P.decode c ∈ A.carrier}
  definable := A.definable

def codeDecode {P : Space L M} (A : DefSet P S) : Map (codePreimage A) A :=
  (Map.ofCodes (codePreimage A) P.decode id
    (fun _ => Set.DefinableFun.proj L)
    (fun c => c.property) (fun _ => rfl)).corestrict (fun a => a.property)

theorem codeDecode_surjective {P : Space L M} (A : DefSet P S) :
    Function.Surjective (codeDecode A) := by
  intro a
  obtain ⟨c, hc⟩ := P.onto a.val
  exact ⟨⟨c, show P.decode c ∈ A.carrier from hc.symm ▸ a.property⟩, Subtype.ext hc⟩

def FiniteFamily.codeLift {P : Space L M} (A : FiniteFamily P S) :
    FiniteFamily (codeSpace P) S := ⟨A.tags, fun i => codePreimage (A.piece i)⟩

def FiniteFamily.decode {P : Space L M} (A : FiniteFamily P S)
    (c : A.codeLift.Carrier) : A.Carrier := ⟨c.1, codeDecode (A.piece c.1) c.2⟩

theorem FiniteFamily.decode_surjective {P : Space L M} (A : FiniteFamily P S) :
    Function.Surjective A.decode := by
  rintro ⟨i, a⟩
  obtain ⟨c, rfl⟩ := codeDecode_surjective (A.piece i) a
  exact ⟨⟨i, c⟩, rfl⟩

end DiamondIntegral.Section3
