import «section 3».MeasuredGammaCoproductIsomorphisms

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def measuredGammaPartitionHom (A : MeasuredGammaObject hc S k)
    (X Y : Fin A.underlying.tags → DefSet ((volumeGammaSpace hc).power (Fin k)) S)
    (hX : ∀ i, (X i).carrier ⊆ (A.underlying.piece i).carrier)
    (hY : ∀ i, (Y i).carrier ⊆ (A.underlying.piece i).carrier)
    (hd : ∀ i, Disjoint (X i).carrier (Y i).carrier)
    (hu : ∀ i, ((X i).union (Y i)).carrier = (A.underlying.piece i).carrier) :
    MeasuredGammaHom ((A.restrict X hX).coprod (A.restrict Y hY)) A where
  underlying := gammaPartitionHom A.underlying X Y hX hY hd hu
  preserves x := by
    change ((A.restrict X hX).coprod (A.restrict Y hY)).combinedWeight x =
      A.combinedWeight (familyPartitionMap A.underlying X Y hX hY x)
    rcases familyCoprod_cases (A.underlying.restrict X) (A.underlying.restrict Y) x with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · calc
        _ = (A.restrict X hX).combinedWeight a := measuredGammaCoprod_combined_left (A.restrict X hX) (A.restrict Y hY) a
        _ = A.combinedWeight ⟨a.1, Map.inclusion (hX a.1) a.2⟩ := rfl
        _ = _ := congrArg A.combinedWeight (familyPartitionMap_inl A.underlying X Y hX hY a).symm
    · calc
        _ = (A.restrict Y hY).combinedWeight b := measuredGammaCoprod_combined_right (A.restrict X hX) (A.restrict Y hY) b
        _ = A.combinedWeight ⟨b.1, Map.inclusion (hY b.1) b.2⟩ := rfl
        _ = _ := congrArg A.combinedWeight (familyPartitionMap_inr A.underlying X Y hX hY b).symm

theorem measuredGammaIsoClass_scissor {A B D E : MeasuredGammaObject hc S k}
    (h : MeasuredGammaScissor A B D E) :
    measuredGammaIsoClass A + measuredGammaIsoClass B = measuredGammaIsoClass D + measuredGammaIsoClass E := by
  obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
  subst A
  subst B
  subst D
  subst E
  have hd : ∀ i, Disjoint (X i).carrier ((U.underlying.difference X) i).carrier := fun i =>
    Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)
  have hu : ∀ i, ((X i).union ((U.underlying.difference X) i)).carrier = (U.underlying.piece i).carrier := by
    intro i
    ext t
    change (t ∈ (X i).carrier ∨ (t ∈ (U.underlying.piece i).carrier ∧ t ∉ (X i).carrier)) ↔ t ∈ (U.underlying.piece i).carrier
    constructor
    · exact fun h => h.elim (fun h => hX i h) (fun h => h.1)
    · intro ht
      by_cases hx : t ∈ (X i).carrier
      · exact Or.inl hx
      · exact Or.inr ⟨ht, hx⟩
  rw [measuredGammaIsoClass_empty, add_zero, ← measuredGammaIsoClass_coprod]
  exact measuredGammaIsoClass_eq_iff.mpr ⟨asIso (show _ ⟶ _ from
    measuredGammaPartitionHom U X (U.underlying.difference X) hX (fun _ _ h => h.1) hd hu)⟩

def measuredGammaKPlusToIsoClasses : MeasuredGammaKPlus hc S k →+ MeasuredGammaIsoClasses hc S k :=
  PositiveAdditiveGrothendieck.lift (measuredGammaPresentation hc S k) {
    toFun := measuredGammaIsoClass
    iso := measuredGammaIsoClass_eq_iff.mpr
    empty := measuredGammaIsoClass_empty
    scissor := measuredGammaIsoClass_scissor }

@[simp] theorem measuredGammaKPlusToIsoClasses_class (A : MeasuredGammaObject hc S k) :
    measuredGammaKPlusToIsoClasses (measuredGammaClass A) = measuredGammaIsoClass A :=
  PositiveAdditiveGrothendieck.lift_of _ _ A

theorem measuredGammaClass_eq_iff_iso {A B : MeasuredGammaObject hc S k} :
    measuredGammaClass A = measuredGammaClass B ↔ Nonempty (A ≅ B) := by
  constructor
  · intro h
    apply measuredGammaIsoClass_eq_iff.mp
    simpa only [measuredGammaKPlusToIsoClasses_class] using congrArg measuredGammaKPlusToIsoClasses h
  · rintro ⟨e⟩
    exact measuredGammaClass_iso e

end DiamondIntegral.Section3
