import «section 3».RVCoproducts
import Section4.RVPositiveIsoComparison
import Section4.RVEmptyIso

/-! The positive quotient has exactly the intended identifications:
equality of two object classes means a genuine same-base definable
bijection. A checked comparison to the companion category uses the full
nonzero weight and the literal finite target fibres; it changes no base. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section4

noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

def rvAmbientHom {U V : RVObject (M := M) S k} (f : Map U.domain V.domain) :
    RVHom U.toCompanion.obj V.toCompanion.obj where
  map := f
  volumetric a := by
    change rvWeight (U.volume a).val ≤ rvWeight (V.volume (f a)).val
    have hU : rvWeight (U.volume a).val = k := by simp [rvWeight, U.nonzero a]
    have hV : rvWeight (V.volume (f a)).val = k := by simp [rvWeight, V.nonzero (f a)]
    rw [hU, hV]
  finite_volume_images t := by
    apply ((U.finite ⟨t, Set.mem_univ _⟩).image (fun a : U.domain => (V.volume (f a)).val)).subset
    rintro s ⟨a, ha, hs⟩
    exact ⟨a, Subtype.ext ha, hs⟩

def rvAmbientIso {U V : RVObject (M := M) S k} (f : DefinableBijection U.domain V.domain) :
    U.toCompanion.obj ≅ V.toCompanion.obj where
  hom := rvAmbientHom f.map
  inv := rvAmbientHom f.symm.map
  hom_inv_id := by apply RVHom.ext; apply Map.ext; intro a; exact f.symm_apply_apply a
  inv_hom_id := by apply RVHom.ext; apply Map.ext; intro a; exact f.apply_symm_apply a

abbrev AmbientRVKPlus (S : Set M) (k : ℕ) := SpecialTransformations.Section4.RVKPlus (M := M) S k

def rvAmbientClass (U : RVObject (M := M) S k) : AmbientRVKPlus S k :=
  SpecialTransformations.Section4.rvClass U.toCompanion.obj

theorem rvAmbientClass_scissor {A B D E : RVObject (M := M) S k} (h : RVScissor A B D E) :
    rvAmbientClass A + rvAmbientClass B = rvAmbientClass D + rvAmbientClass E := by
  classical
  obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
  subst A
  subst B
  subst D
  subst E
  let W := U.toCompanion.obj
  let Y := U.difference X
  have hY : Y.carrier ⊆ W.domain.carrier := fun _ ht => ht.1
  have hUnion : (X.union Y).carrier = W.domain.carrier := by
    ext t
    constructor
    · rintro (hx | hy)
      · exact hX hx
      · exact hy.1
    · intro ht
      by_cases hx : t ∈ X.carrier
      · exact Or.inl hx
      · exact Or.inr ⟨ht, hx⟩
  have hInter : (X.inter Y).carrier = ∅ := by
    apply Set.Subset.antisymm
    · rintro t ⟨hx, hy⟩
      exact (hy.2 hx).elim
    · exact Set.empty_subset _
  let eUnion : W.restrict (X.union Y) (fun _ h => h.elim (fun hx => hX hx) (fun h => h.1)) ≅ W :=
    rvIsoOfVolumePreservingBijection (Map.inclusion hUnion.le) (by
      constructor
      · intro a b he
        exact Subtype.ext (congrArg (fun a : W.domain => a.val) he)
      · intro a
        exact ⟨⟨a.val, hUnion.ge a.property⟩, Subtype.ext rfl⟩) (fun _ => rfl)
  let eInter := rvEmptyIso (W.restrict (X.inter Y) (fun _ h => hX h.1)) hInter
  have hs := SpecialTransformations.Section4.rvClass_scissor
    (S := S) (k := k) ⟨W, X, Y, hX, hY, rfl, rfl, rfl, rfl⟩
  rw [SpecialTransformations.Section4.rvClass_iso eUnion,
    SpecialTransformations.Section4.rvClass_iso eInter,
    SpecialTransformations.Section4.rvClass_empty, add_zero] at hs
  change SpecialTransformations.Section4.rvClass (W.restrict X hX) +
      SpecialTransformations.Section4.rvClass (W.restrict Y hY) =
    SpecialTransformations.Section4.rvClass W +
      SpecialTransformations.Section4.rvClass (SpecialTransformations.Section4.RVObject.empty S k)
  rw [SpecialTransformations.Section4.rvClass_empty, add_zero]
  exact hs

def rvToAmbientKPlus : RVKPlus (M := M) S k →+ AmbientRVKPlus S k :=
  PositiveAdditiveGrothendieck.lift (rvPresentation S k) {
    toFun := rvAmbientClass
    iso := fun h => by obtain ⟨e⟩ := h; exact SpecialTransformations.Section4.rvClass_iso (rvAmbientIso e.hom)
    empty := SpecialTransformations.Section4.rvClass_empty
    scissor := rvAmbientClass_scissor }

@[simp] theorem rvToAmbientKPlus_class (U : RVObject (M := M) S k) :
    rvToAmbientKPlus (rvClass U) = rvAmbientClass U := PositiveAdditiveGrothendieck.lift_of _ _ U

theorem rvClass_eq_iff_iso {U V : RVObject (M := M) S k} :
    rvClass U = rvClass V ↔ Nonempty (U ≅ V) := by
  constructor
  · intro h
    have hc := congrArg rvToAmbientKPlus h
    rw [rvToAmbientKPlus_class, rvToAmbientKPlus_class] at hc
    obtain ⟨e⟩ := SpecialTransformations.Section4.rvClass_eq_iff_iso.mp hc
    have hi : Function.LeftInverse e.inv.map e.hom.map := fun a =>
      congrArg (fun f : U.toCompanion.obj ⟶ U.toCompanion.obj => f.map a) e.hom_inv_id
    have hs : Function.RightInverse e.inv.map e.hom.map := fun a =>
      congrArg (fun f : V.toCompanion.obj ⟶ V.toCompanion.obj => f.map a) e.inv_hom_id
    let f : U ⟶ V := ⟨e.hom.map, ⟨hi.injective, hs.surjective⟩⟩
    exact ⟨asIso f⟩
  · rintro ⟨e⟩
    exact rvClass_iso e

theorem rvToAmbientKPlus_injective : Function.Injective (rvToAmbientKPlus (M := M) (S := S) (k := k)) := by
  intro a b he
  obtain ⟨U, rfl⟩ := rvClass_surjective a
  obtain ⟨V, rfl⟩ := rvClass_surjective b
  obtain ⟨e⟩ := SpecialTransformations.Section4.rvClass_eq_iff_iso.mp
    (show rvAmbientClass U = rvAmbientClass V by simpa only [rvToAmbientKPlus_class] using he)
  have hi : Function.LeftInverse e.inv.map e.hom.map := fun a =>
    congrArg (fun f : U.toCompanion.obj ⟶ U.toCompanion.obj => f.map a) e.hom_inv_id
  have hs : Function.RightInverse e.inv.map e.hom.map := fun a =>
    congrArg (fun f : V.toCompanion.obj ⟶ V.toCompanion.obj => f.map a) e.inv_hom_id
  let f : U ⟶ V := ⟨e.hom.map, ⟨hi.injective, hs.surjective⟩⟩
  exact rvClass_iso (asIso f)

end DiamondIntegral.Section3
