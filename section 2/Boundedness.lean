import «section 2».Differentiation

/-! Terminology 2.39 uses all coordinate values, rather than the minimum
tuple value from differentiation. Actual existing Gamma-infinity coordinates
are retained. Finite Gamma bounds exclude infinity from a doubly bounded box.
The companion library writes the Gamma group operation multiplicatively, so
the inverse of a finite value represents its additive negative. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m l k : ℕ}

abbrev ValuedCoordinates (n m l : ℕ) := Mixed M n m × (Fin l → GammaInfinity M)

def valuationCoordinates (p : ValuedCoordinates (M := M) n m l) :
    Fin (n + m + l) → GammaInfinity M :=
  Fin.append (Fin.append (coordinateValues p.1.1) (fun j => Values.vrv (p.1.2 j))) p.2

/-- The coordinatewise valuation image, distinct from any coordinate projection. -/
def valim (A : Set (ValuedCoordinates (M := M) n m l)) :
    Set (Fin (n + m + l) → GammaInfinity M) := valuationCoordinates '' A

def GammaBoundedBy (γ : Gamma M) (I : Set (Fin k → GammaInfinity M)) : Prop :=
  ∀ x ∈ I, ∀ i, γ.val ≤ x i

def GammaDoublyBoundedBy (γ : Gamma M) (I : Set (Fin k → GammaInfinity M)) : Prop :=
  ∀ x ∈ I, ∀ i, (γ⁻¹).val ≤ x i ∧ x i ≤ γ.val

def BoundedBy (γ : Gamma M) (A : Set (ValuedCoordinates (M := M) n m l)) : Prop :=
  GammaBoundedBy γ (valim A)

def DoublyBoundedBy (γ : Gamma M) (A : Set (ValuedCoordinates (M := M) n m l)) : Prop :=
  GammaDoublyBoundedBy γ (valim A)

def IsBounded (A : Set (ValuedCoordinates (M := M) n m l)) : Prop :=
  ∃ γ : Gamma M, BoundedBy γ A

def IsDoublyBounded (A : Set (ValuedCoordinates (M := M) n m l)) : Prop :=
  ∃ γ : Gamma M, DoublyBoundedBy γ A

theorem boundedBy_iff (γ : Gamma M) (A : Set (ValuedCoordinates (M := M) n m l)) :
    BoundedBy γ A ↔ ∀ p ∈ A, ∀ i, γ.val ≤ valuationCoordinates p i := by
  constructor
  · intro h p hp
    exact h _ ⟨p, hp, rfl⟩
  · rintro h _ ⟨p, hp, rfl⟩
    exact h p hp

theorem doublyBoundedBy_iff (γ : Gamma M) (A : Set (ValuedCoordinates (M := M) n m l)) :
    DoublyBoundedBy γ A ↔
      ∀ p ∈ A, ∀ i, (γ⁻¹).val ≤ valuationCoordinates p i ∧
        valuationCoordinates p i ≤ γ.val := by
  constructor
  · intro h p hp
    exact h _ ⟨p, hp, rfl⟩
  · rintro h _ ⟨p, hp, rfl⟩
    exact h p hp

theorem GammaDoublyBoundedBy.finite_values {γ : Gamma M}
    {I : Set (Fin k → GammaInfinity M)} (hI : GammaDoublyBoundedBy γ I)
    {x : Fin k → GammaInfinity M} (hx : x ∈ I) (i : Fin k) :
    x i ≠ Values.infinity := by
  intro he
  have h := (hI x hx i).2
  rw [he] at h
  exact γ.property (le_antisymm (Values.le_infinity _) h)

theorem DoublyBoundedBy.vf_ne_zero {γ : Gamma M}
    {A : Set (ValuedCoordinates (M := M) n m l)} (hA : DoublyBoundedBy γ A)
    {p : ValuedCoordinates (M := M) n m l} (hp : p ∈ A) (i : Fin n) : p.1.1 i ≠ 0 := by
  intro he
  have hfin := hA.finite_values ⟨p, hp, rfl⟩ ((i.castAdd m).castAdd l)
  apply hfin
  simpa only [valuationCoordinates, Fin.append_left, coordinateValues, he] using
    (vfValue_eq_infinity_iff (0 : VF M)).mpr rfl

theorem DoublyBoundedBy.rv_ne_zero {γ : Gamma M}
    {A : Set (ValuedCoordinates (M := M) n m l)} (hA : DoublyBoundedBy γ A)
    {p : ValuedCoordinates (M := M) n m l} (hp : p ∈ A) (j : Fin m) :
    p.1.2 j ≠ rvZero M := by
  intro he
  have hfin := hA.finite_values ⟨p, hp, rfl⟩ ((Fin.natAdd n j).castAdd l)
  apply hfin
  simp only [valuationCoordinates, Fin.append_left, Fin.append_right, he]
  exact (Values.vrv_eq_infinity_iff _).mpr rfl

theorem DoublyBoundedBy.gamma_ne_infinity {γ : Gamma M}
    {A : Set (ValuedCoordinates (M := M) n m l)} (hA : DoublyBoundedBy γ A)
    {p : ValuedCoordinates (M := M) n m l} (hp : p ∈ A) (j : Fin l) :
    p.2 j ≠ Values.infinity := by
  have hfin := hA.finite_values ⟨p, hp, rfl⟩ (Fin.natAdd (n+m) j)
  simpa only [valuationCoordinates, Fin.append_right] using hfin

theorem BoundedBy.subset {γ : Gamma M}
    {A C : Set (ValuedCoordinates (M := M) n m l)}
    (hA : BoundedBy γ A) (hCA : C ⊆ A) : BoundedBy γ C :=
  (boundedBy_iff γ C).mpr (fun p hp => (boundedBy_iff γ A).mp hA p (hCA hp))

theorem DoublyBoundedBy.subset {γ : Gamma M}
    {A C : Set (ValuedCoordinates (M := M) n m l)}
    (hA : DoublyBoundedBy γ A) (hCA : C ⊆ A) : DoublyBoundedBy γ C :=
  (doublyBoundedBy_iff γ C).mpr (fun p hp => (doublyBoundedBy_iff γ A).mp hA p (hCA hp))

end DiamondIntegral.Section2
