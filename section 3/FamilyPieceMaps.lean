import «section 3».FiniteFamilies

/-! Piecewise bijections assemble into a definable bijection of tagged
families, even when the source and target imaginary presentations differ. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language
open SpecialTransformations.DefinableGeometry

noncomputable section
namespace DiamondIntegral.Section3
variable {L : Language} {M : Type} [L.Structure M] {S : Set M} {P Q : Space L M}

def FamilyBijection.pieces (A : FiniteFamily P S) (piece : Fin A.tags → DefSet Q S)
    (f : ∀ i, DefinableBijection (A.piece i) (piece i)) :
    FamilyBijection A ⟨A.tags, piece⟩ where
  equiv := Equiv.sigmaCongrRight (fun i => Equiv.ofBijective (f i).map (f i).bijective)
  definable := by
    classical
    intro i j
    by_cases he : i = j
    · subst j
      exact (f i).map.graph_definable.congr P Q (by
        intro x y
        constructor
        · rintro ⟨a, rfl, rfl⟩
          exact ⟨a, (f i).map a, rfl, rfl, rfl⟩
        · rintro ⟨a, b, rfl, rfl, hab⟩
          have hab' : (f i).map a = b := by
            change (⟨i, (f i).map a⟩ : Σ i, piece i) = ⟨i, b⟩ at hab
            simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hab
          exact ⟨a, rfl, congrArg Subtype.val hab'⟩)
    · have hd : P.RelationDefinable Q S (fun _ _ => False) := by
        change S.Definable L _
        simpa [Space.relation] using
          (Set.definable_empty : S.Definable L (∅ : Set (P.Index ⊕ Q.Index → M)))
      exact hd.congr P Q (by
        intro x y
        constructor
        · exact False.elim
        · rintro ⟨a, b, _, _, hab⟩
          exact he (congrArg Sigma.fst hab))

end DiamondIntegral.Section3
