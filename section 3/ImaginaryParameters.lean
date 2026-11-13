import Section4.Products
import Section4.CodeMaps

/-! Definability over actual named imaginary values is a fibre of a
complete definable relation over the original real base. Passing to a
chosen real code is an explicit parameter expansion, with no generation
claim about that expanded base. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry
noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M]
variable {P Q : Space L M} {S : Set M} {p : P.Carrier}

def ImaginaryDefinable (P : Space L M) (p : P.Carrier) (Q : Space L M) (S : Set M)
    (A : Set Q.Carrier) : Prop :=
  ∃ R : Set (P.prod Q).Carrier, (P.prod Q).Definable S R ∧ ∀ x, x ∈ A ↔ (p, x) ∈ R

structure NamedDefSet (P : Space L M) (p : P.Carrier) (Q : Space L M) (S : Set M) where
  carrier : Set Q.Carrier
  definable : ImaginaryDefinable P p Q S carrier

instance namedDefSetCoeSort : CoeSort (NamedDefSet P p Q S) (Type _) := ⟨fun A => ↥A.carrier⟩

theorem ImaginaryDefinable.of_real {A : Set Q.Carrier} (hA : Q.Definable S A) :
    ImaginaryDefinable P p Q S A := by
  exact ⟨Set.univ ×ˢ A, (DefSet.prod (DefSet.univ P S) ⟨A, hA⟩).definable,
    fun _ => ⟨fun h => ⟨Set.mem_univ _, h⟩, fun h => h.2⟩⟩

theorem ImaginaryDefinable.inter {A B : Set Q.Carrier}
    (hA : ImaginaryDefinable P p Q S A) (hB : ImaginaryDefinable P p Q S B) :
    ImaginaryDefinable P p Q S (A ∩ B) := by
  obtain ⟨R, hR, hr⟩ := hA
  obtain ⟨T, hT, ht⟩ := hB
  exact ⟨R ∩ T, hR.inter _ hT, fun x => and_congr (hr x) (ht x)⟩

theorem ImaginaryDefinable.union {A B : Set Q.Carrier}
    (hA : ImaginaryDefinable P p Q S A) (hB : ImaginaryDefinable P p Q S B) :
    ImaginaryDefinable P p Q S (A ∪ B) := by
  obtain ⟨R, hR, hr⟩ := hA
  obtain ⟨T, hT, ht⟩ := hB
  exact ⟨R ∪ T, hR.union _ hT, fun x => or_congr (hr x) (ht x)⟩

theorem ImaginaryDefinable.compl {A : Set Q.Carrier} (hA : ImaginaryDefinable P p Q S A) :
    ImaginaryDefinable P p Q S Aᶜ := by
  obtain ⟨R, hR, hr⟩ := hA
  exact ⟨Rᶜ, hR.compl _, fun x => not_congr (hr x)⟩

theorem ImaginaryDefinable.mono {A : Set Q.Carrier} {T : Set M}
    (hA : ImaginaryDefinable P p Q S A) (hST : S ⊆ T) : ImaginaryDefinable P p Q T A := by
  obtain ⟨R, hR, hr⟩ := hA
  exact ⟨R, hR.mono _ hST, hr⟩

def realCodeParameters (S : Set M) (c : P.domain) : Set M := S ∪ Set.range c.val

theorem ImaginaryDefinable.over_real_code {A : Set Q.Carrier}
    (hA : ImaginaryDefinable P p Q S A) (c : P.domain) (hp : P.decode c = p) :
    Q.Definable (realCodeParameters S c) A := by
  obtain ⟨R, hR, hr⟩ := hA
  let F : (Q.Index → M) → (P.Index ⊕ Q.Index → M) := fun x => Sum.elim c.val x
  have hF : (realCodeParameters S c).DefinableMap L F := by
    intro i
    cases i with
    | inl i => exact L.definableFun_const Q.Index (Or.inr (Set.mem_range_self i))
    | inr i => exact Set.DefinableFun.proj L
  have hRR : (realCodeParameters S c).Definable L ((P.prod Q).preimage R) :=
    hR.mono _ (fun _ h => Or.inl h)
  have hf := hRR.preimage_map hF
  change (realCodeParameters S c).Definable L (Q.preimage A)
  convert hf using 1
  ext x
  change (∃ hx : x ∈ Q.domain, Q.decode ⟨x, hx⟩ ∈ A) ↔
    (∃ h : Sum.elim c.val x ∈ (P.prod Q).domain, (P.prod Q).decode ⟨Sum.elim c.val x, h⟩ ∈ R)
  constructor
  · rintro ⟨hx, ha⟩
    refine ⟨⟨c.property, hx⟩, ?_⟩
    change (P.decode c, Q.decode ⟨x, hx⟩) ∈ R
    rw [hp]
    exact (hr _).mp ha
  · rintro ⟨h, hR⟩
    have hx : x ∈ Q.domain := h.2
    refine ⟨hx, (hr _).mpr ?_⟩
    change (P.decode c, Q.decode ⟨x, hx⟩) ∈ R at hR
    rwa [hp] at hR

def NamedDefSet.overRealCode (A : NamedDefSet P p Q S) (c : P.domain) (hp : P.decode c = p) :
    DefSet Q (realCodeParameters S c) := ⟨A.carrier, A.definable.over_real_code c hp⟩

def NamedDefSet.ofReal (A : DefSet Q S) : NamedDefSet P p Q S :=
  ⟨A.carrier, ImaginaryDefinable.of_real A.definable⟩

def NamedDefSet.empty (P : Space L M) (p : P.Carrier) (Q : Space L M) (S : Set M) : NamedDefSet P p Q S :=
  .ofReal (DefSet.empty Q S)

def NamedDefSet.univ (P : Space L M) (p : P.Carrier) (Q : Space L M) (S : Set M) : NamedDefSet P p Q S :=
  .ofReal (DefSet.univ Q S)

def NamedDefSet.inter (A B : NamedDefSet P p Q S) : NamedDefSet P p Q S :=
  ⟨A.carrier ∩ B.carrier, A.definable.inter B.definable⟩

def NamedDefSet.union (A B : NamedDefSet P p Q S) : NamedDefSet P p Q S :=
  ⟨A.carrier ∪ B.carrier, A.definable.union B.definable⟩

def NamedDefSet.compl (A : NamedDefSet P p Q S) : NamedDefSet P p Q S :=
  ⟨A.carrierᶜ, A.definable.compl⟩

def NamedDefSet.sdiff (A B : NamedDefSet P p Q S) : NamedDefSet P p Q S := A.inter B.compl

end DiamondIntegral.Section3
