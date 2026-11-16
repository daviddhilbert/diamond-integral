import «section 6».FiniteCentripetalGluing

/-! The tag-locus extension applies to an actual RV-pullback piece of
a regularized ambient set. Literal restrictions are special chains,
rather than merely pointwise descriptions of an unconstructed map. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A C : DefSet (rawMixedSpace (M := M) n r) S}

theorem pullback_piece_eq_tag_locus
    (hCA : C.carrier ⊆ A.carrier) (hC : IsRVPullback C.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    C.carrier = (focusActive A (locusTags A C)).carrier := by
  rw [focusActive_locus A C hC htag]
  exact (Set.inter_eq_right.mpr hCA).symm

theorem CentripetalData.point_inactive_full (D : CentripetalData (G := G) A)
    (p : Mixed M n r) (hu : p.2 ∉ D.activeTags.carrier) :
    D.point p = (p.1,Fin.append (fun _ : Fin 1 => branchTag false) p.2) := by
  apply Prod.ext (D.point_inactive hu)
  change Fin.append (fun _ : Fin 1 => branchTag (D.core p)) p.2 = _
  rw [D.core_inactive hu]

theorem exists_centripetal_extension_of_pullback_piece
    (h00 : M ⊨ Axioms.ACVF00) (D : CentripetalData (G := G) C)
    (hCA : C.carrier ⊆ A.carrier) (hC : IsRVPullback C.carrier)
    (hA : ProperInvariant S A.carrier) (hAD : VFDoublyBounded A.carrier)
    (htag : ∀ p ∈ A.carrier, ∀ q ∈ A.carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1) :
    ∃ E : CentripetalData (G := G) A,
      E.coordinate = D.coordinate ∧ E.coefficient = D.coefficient ∧
      (∀ p ∈ C.carrier, E.point p = D.point p) ∧
      (∀ p ∈ A.carrier, p ∉ C.carrier → E.point p =
        (p.1,Fin.append (fun _ : Fin 1 => branchTag false) p.2)) ∧
      SpecialCovariantChain (G := G) C (E.bijection.restrict hCA).image (E.bijection.restrict hCA).toImage := by
  have he := pullback_piece_eq_tag_locus hCA hC htag
  let E := D.extendOnTags (locusTags A C) he hA hAD htag
  have hpoint (p) (hp : p ∈ C.carrier) : E.point p = D.point p :=
    D.extendOnTags_point _ he hA hAD htag p hp
  refine ⟨E,rfl,rfl,hpoint,?_,?_⟩
  · exact fun p hp hpC => D.extendOnTags_outside _ he hA hAD htag p hp hpC
  · exact centripetal_restriction_chain h00 E D hCA (fun p hp => (hpoint p hp).symm)

end DiamondIntegral.Section6
