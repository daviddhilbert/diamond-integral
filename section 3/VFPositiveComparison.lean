import «section 3».VFCoproducts

/-! Fixed-degree VF positive equality is exactly original-base definable
isomorphism. Forgetting a dimension bound creates no identifications. -/
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (Section2.VF M) G]
variable {S : Set M} {k l : ℕ}

def vfCompanionFiniteIso {U : VFObject (M := M) S k} {V : VFObject (M := M) S l}
    (f : DefinableBijection U.domain V.domain) : U.toCompanionFinite ≅ V.toCompanionFinite :=
  vfFiniteAllIsoOfAmbient (DefinableSetCat.isoOfBijective f.map f.bijective)

def vfBijectionOfFiniteIso {U : VFObject (M := M) S k} {V : VFObject (M := M) S l}
    (e : U.toCompanionFinite ≅ V.toCompanionFinite) : DefinableBijection U.domain V.domain :=
  ⟨e.hom.hom, DefinableSetCat.bijective_of_iso ((vfFiniteProperty S).ι.mapIso e)⟩

theorem vfFiniteClass_cut (U : VFObject (M := M) S k)
    (X : DefSet (rawMixedSpace (M := M) U.vfArity U.rvArity) S)
    (hX : X.carrier ⊆ U.domain.carrier) :
    vfFiniteClass (U.restrict X hX).toCompanionFinite +
      vfFiniteClass (U.restrict (U.difference X) (fun _ h => h.1)).toCompanionFinite =
        vfFiniteClass U.toCompanionFinite := by
  let Y := U.difference X
  have hY : Y.carrier ⊆ U.domain.carrier := fun _ h => h.1
  have hu : (X.union Y).carrier = U.domain.carrier := by
    ext t
    change ((t ∈ X.carrier) ∨ (t ∈ U.domain.carrier ∧ t ∉ X.carrier)) ↔ t ∈ U.domain.carrier
    constructor
    · exact fun h => h.elim (fun h => hX h) (fun h => h.1)
    · intro h
      by_cases hx : t ∈ X.carrier
      · exact Or.inl hx
      · exact Or.inr ⟨h, hx⟩
  have hi : (X.inter Y).carrier = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro _ ⟨hx, hy⟩
    exact hy.2 hx
  let D := U.restrict (X.union Y) (fun _ h => h.elim (fun h => hX h) (fun h => h.1))
  let E := U.restrict (X.inter Y) (fun _ h => hX h.1)
  have h := vfFiniteClass_scissor (A := (U.restrict X hX).toCompanionFinite)
    (B := (U.restrict Y hY).toCompanionFinite) (C := D.toCompanionFinite) (D := E.toCompanionFinite)
    ⟨(U.vfArity, U.rvArity), X, Y, rfl, rfl, rfl, rfl⟩
  have hd := vfFiniteClass_iso (vfCompanionFiniteIso (U := D) (V := U) (DefinableBijection.ofCarrierEq hu))
  have he := vfFiniteClass_iso (vfCompanionFiniteIso (U := E) (V := VFObject.empty S k)
    (DefinableBijection.ofEmpty hi rfl))
  rw [hd, he] at h
  change _ = vfFiniteClass U.toCompanionFinite + vfFiniteClass (vfFiniteAllEmpty S) at h
  simpa only [vfFiniteClass_empty, add_zero] using h

def vfToFiniteKPlus : VFKPlus (M := M) S k →+ VFFiniteKPlus S :=
  PositiveAdditiveGrothendieck.lift (vfPresentation S k) {
    toFun (U : VFObject (M := M) S k) := vfFiniteClass U.toCompanionFinite
    iso := fun h => by obtain ⟨e⟩ := h; exact vfFiniteClass_iso (vfCompanionFiniteIso e.hom)
    empty := vfFiniteClass_empty
    scissor := by
      intro A B D E h
      obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
      subst A
      subst B
      subst D
      subst E
      change _ = vfFiniteClass U.toCompanionFinite + vfFiniteClass (vfFiniteAllEmpty S)
      rw [vfFiniteClass_empty, add_zero]
      exact vfFiniteClass_cut U X hX }

@[simp] theorem vfToFiniteKPlus_class (U : VFObject (M := M) S k) :
    vfToFiniteKPlus (vfClass U) = vfFiniteClass U.toCompanionFinite :=
  PositiveAdditiveGrothendieck.lift_of _ _ U

theorem vfClass_eq_iff_iso {U V : VFObject (M := M) S k} :
    vfClass U = vfClass V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    have ht := congrArg vfToFiniteKPlus h
    rw [vfToFiniteKPlus_class, vfToFiniteKPlus_class] at ht
    obtain ⟨e⟩ := vfFiniteClass_eq_iff_iso.mp ht
    exact ⟨asIso (show U ⟶ V from vfBijectionOfFiniteIso e)⟩
  · rintro ⟨e⟩
    exact vfClass_iso e

theorem vfToFiniteKPlus_injective (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hs : Saturated M κ) (hS : Cardinal.mk S < κ)
    (hv : ∀ x y : Section2.VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y) :
    Function.Injective (vfToFiniteKPlus (M := M) (S := S) (k := k)) := by
  intro a b h
  obtain ⟨U, rfl⟩ := vfClass_surjective hc hs hS hv a
  obtain ⟨V, rfl⟩ := vfClass_surjective hc hs hS hv b
  rw [vfToFiniteKPlus_class, vfToFiniteKPlus_class] at h
  obtain ⟨e⟩ := vfFiniteClass_eq_iff_iso.mp h
  exact vfClass_iso (asIso (show U ⟶ V from vfBijectionOfFiniteIso e))

end DiamondIntegral.Section3
