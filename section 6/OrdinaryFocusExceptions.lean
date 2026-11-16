import «section 6».OrdinaryChainExceptions

/-! The original-base finite exceptional projection contains every
ordinary focus event, and its complement avoids zero at every stage.
No individual exceptional point or RV parameter is named. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r s : ℕ}

theorem ordinaryChainZeroSources_subset
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    (T : SpecialTransformations.Section5.Chain R 1 A B) :
    ordinaryChainZeroSources T ⊆ SpecialTransformations.Section5.carrier A := by
  cases T with
  | nil A => exact fun _ h => h.1
  | cons p tail =>
    rintro q (h | ⟨a,rfl,_⟩)
    · exact h.1
    · exact a.property

theorem ordinaryChainZeroSources_contains_zero
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (p : A) (hp : p.val.1 0=(0 : VF M)) : p.val ∈ ordinaryChainZeroSources T := by
  cases T with
  | nil A => exact ⟨p.property,hp⟩
  | cons a tail => exact Or.inl ⟨p.property,hp⟩

theorem ordinaryChain_nonzero_off_zeroSources
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (p : A) (hp : p.val ∉ ordinaryChainZeroSources T) : (T.toMap p).val.1 0 ≠ (0 : VF M) := by
  induction T with
  | nil A =>
    intro he
    exact hp ⟨p.property,he⟩
  | cons a tail ih =>
    apply ih (a.toMap p)
    intro he
    exact hp (Or.inr ⟨p,rfl,he⟩)

theorem ordinary_focus_event_mem_zeroSources
    {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
    {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}
    {j : Fin r} (D : SpecialTransformations.Section5.Focus A 0 j)
    (T : SpecialTransformations.Section5.Chain R 1 D.etaImage B)
    (p : A) (hActive : p.val ∈ D.locus) (hFocus : p.val.1 0=D.center p.val) :
    p.val ∈ ordinaryChainZeroSources (.cons (.centripetal D) T) := by
  apply Or.inr
  refine ⟨p,rfl,ordinaryChainZeroSources_contains_zero T ((SpecialTransformations.Section5.Primitive.centripetal D).toMap p) ?_⟩
  change (D.toFocusGeometry.eta p.val).1 0=0
  simp only [SpecialTransformations.Section5.FocusGeometry.eta,if_pos hActive,
    SpecialTransformations.Section5.replace,Function.update_self,hFocus,sub_self]

namespace OriginalBaseOrdinarySpecial
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable {B : DefSet (rawMixedSpace (M := M) 1 s) S} {f : Map A B}

def exceptions (T : OriginalBaseOrdinarySpecial A B f) (hc : CanonicalStructure.IsCanonical (M := M)) :
    DefSet (rawMixedSpace (M := M) 1 r) S :=
  ⟨ordinaryChainZeroSources T.special.chain,ordinary_named_gamma_set_definable hc _
    (ordinaryChainZeroSources_gamma_definable hc T.special.chain T.graphs)⟩

theorem exceptions_subset (T : OriginalBaseOrdinarySpecial A B f)
    (hc : CanonicalStructure.IsCanonical (M := M)) : (T.exceptions hc).carrier ⊆ A.carrier := by
  intro p hp
  exact (Set.ext_iff.mp T.source_eq p).mp (ordinaryChainZeroSources_subset T.special.chain hp)

theorem exceptions_finite_vfProjection (T : OriginalBaseOrdinarySpecial A B f)
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ) :
    (Prod.fst '' (T.exceptions hc).carrier).Finite :=
  ordinaryChainZeroSources_finite_vfProjection hc hκ hs hsmall T.special.chain T.graphs

theorem nonzero_off_exceptions (T : OriginalBaseOrdinarySpecial A B f)
    (hc : CanonicalStructure.IsCanonical (M := M)) (p : A) (hp : p.val ∉ (T.exceptions hc).carrier) :
    (f p).val.1 0 ≠ 0 := by
  rw [← T.agrees p]
  exact ordinaryChain_nonzero_off_zeroSources T.special.chain _ hp

end OriginalBaseOrdinarySpecial
end DiamondIntegral.Section6
