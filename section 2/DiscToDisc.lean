import «section 2».PrimitiveDiscs
import «section 2».AtomicBaseChange
import Section4.RealPresentations

/-! The concentric terminology and the quoted Lemma 2.32.
The disc-to-disc partition is [18, Propositions 3.19 and 3.21], accepted by the
author while its Section 3 is being formalized. Its input is replaceable
and explicit, with the standing hypotheses retained. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

def mixedTuple {n r : ℕ} (x : Mixed M n r) : Fin (n+r) → M :=
  Fin.append (vfValues x.1) (rvValues x.2)

def mixedSort (n r : ℕ) : Fin (n+r) → SortTag := Fin.append (fun _ => .vf) (fun _ => .rv)

def MixedDefinable (E : ParameterBase M) {n r : ℕ} (A : Set (Mixed M n r)) : Prop :=
  GammaParameters.DefinableOverBase E (mixedSort n r) (mixedTuple '' A)

def mixedMapGraph {n r k s : ℕ} (A : Set (Mixed M n r)) (f : Mixed M n r → Mixed M k s) :
    Set (Fin ((n+r)+(k+s)) → M) :=
  {z | ∃ x ∈ A, Fin.append (mixedTuple x) (mixedTuple (f x)) = z}

def MixedMapDefinable (E : ParameterBase M) {n r k s : ℕ}
    (A : Set (Mixed M n r)) (f : Mixed M n r → Mixed M k s) : Prop :=
  GammaParameters.DefinableOverBase E (Fin.append (mixedSort n r) (mixedSort k s)) (mixedMapGraph A f)

/-- Fix both input and output RV labels before testing images of VF discs.
The open discs have finite Gamma radii, including for the zero RV label. -/
def FibreConcentric {r s : ℕ} (A : Set (Mixed M 1 r)) (f : Mixed M 1 r → Mixed M 1 s) : Prop :=
  ∀ (t : Fin r → RVInfinity M) (u : Fin s → RVInfinity M) (D : Set (VF M)),
    IsOpenDisc (Subtype.val '' D) →
    (∀ x ∈ D, ((fun _ => x),t) ∈ A ∧ (f ((fun _ => x),t)).2 = u) →
    IsOpenDisc (Subtype.val '' ((fun x => (f ((fun _ => x),t)).1 0) '' D))

def HasDiscToDiscProperty {r s : ℕ} (A : Set (Mixed M 1 r)) (B : Set (Mixed M 1 s))
    (f : Mixed M 1 r → Mixed M 1 s) : Prop :=
  Set.BijOn f A B ∧ FibreConcentric A f ∧
    ∃ g : Mixed M 1 s → Mixed M 1 r,
      Set.BijOn g B A ∧ Set.InvOn g f A B ∧ FibreConcentric B g

theorem FibreConcentric.mono {r s : ℕ} {A C : Set (Mixed M 1 r)}
    {f : Mixed M 1 r → Mixed M 1 s} (hf : FibreConcentric A f) (hCA : C ⊆ A) :
    FibreConcentric C f := by
  intro t u D hD hDC
  exact hf t u D hD (fun x hx => ⟨hCA (hDC x hx).1,(hDC x hx).2⟩)

def DiscToDiscPartition (E : ParameterBase M) {r s : ℕ}
    (A : Set (Mixed M 1 r)) (f : Mixed M 1 r → Mixed M 1 s) : Prop :=
  ∃ k : ℕ, ∃ P : Fin k → Set (Mixed M 1 r),
    (⋃ i, P i) = A ∧ Pairwise (fun i j => Disjoint (P i) (P j)) ∧
    ∀ i, MixedDefinable E (P i) ∧ HasDiscToDiscProperty (P i) (f '' P i) f

/-- Accepted [18, Proposition 3.19 and its mixed-coordinate form 3.21].
The external partition proof is not
duplicated here. Definability is over the fixed real/Gamma base. -/
def DiscToDiscPartitionInput (E : ParameterBase M) : Prop :=
  (M ⊨ Axioms.ACVF00) → NontrivialDefinableGamma E →
    ∀ (r s : ℕ) (A : Set (Mixed M 1 r)) (B : Set (Mixed M 1 s))
      (f : Mixed M 1 r → Mixed M 1 s),
      MixedDefinable E A → MixedDefinable E B → MixedMapDefinable E A f → Set.BijOn f A B →
        DiscToDiscPartition E A f

/-- Lemma 2.32 is an integration of the author-accepted cited theorem.
The finite family and each full branch graph keep the original RV labels. -/
theorem lemma_2_32 (h00 : M ⊨ Axioms.ACVF00) (E : ParameterBase M)
    (cited : DiscToDiscPartitionInput E) (hΓ : NontrivialDefinableGamma E)
    {r s : ℕ} (A : Set (Mixed M 1 r)) (B : Set (Mixed M 1 s))
    (f : Mixed M 1 r → Mixed M 1 s) (hA : MixedDefinable E A) (hB : MixedDefinable E B)
    (hf : MixedMapDefinable E A f) (hbij : Set.BijOn f A B) : DiscToDiscPartition E A f :=
  cited h00 hΓ r s A B f hA hB hf hbij

end DiamondIntegral.Section2
