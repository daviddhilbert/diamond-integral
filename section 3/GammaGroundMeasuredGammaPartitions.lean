import «section 3».GammaGroundMeasuredGammaCoproductIsomorphisms
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section3 SpecialTransformations.Section4
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {hc : CanonicalStructure.IsCanonical (M := M)} {ground : GammaParameters.Base (M := M)} {k : ℕ}

def gammaGroundMeasuredGammaPartitionHom (A : GammaGroundMeasuredGammaObject hc ground k)
    (X Y : Fin A.underlying.tags → GammaGroundDefSet hc ground ((volumeGammaSpace hc).power (Fin k)))
    (hX : ∀ i, (X i).carrier ⊆ (A.underlying.piece i).carrier)
    (hY : ∀ i, (Y i).carrier ⊆ (A.underlying.piece i).carrier)
    (hd : ∀ i, Disjoint (X i).carrier (Y i).carrier)
    (hu : ∀ i, ((X i).union (Y i)).carrier = (A.underlying.piece i).carrier) :
    GammaGroundMeasuredGammaHom ((A.restrict X hX).coprod (A.restrict Y hY)) A where
  underlying := gammaGroundGammaPartitionHom A.underlying X Y hX hY hd hu
  preserves x := by
    change ((A.restrict X hX).coprod (A.restrict Y hY)).combinedWeight x =
      A.combinedWeight (gammaGroundFamilyPartitionMap A.underlying X Y hX hY x)
    rcases gammaGroundFamilyCoprod_cases (A.underlying.restrict X) (A.underlying.restrict Y) x with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · calc
        _ = (A.restrict X hX).combinedWeight a := gammaGroundMeasuredGammaCoprod_combined_left (A.restrict X hX) (A.restrict Y hY) a
        _ = A.combinedWeight ⟨a.1, GammaGroundMap.inclusion (hX a.1) a.2⟩ := rfl
        _ = _ := congrArg A.combinedWeight (gammaGroundFamilyPartitionMap_inl A.underlying X Y hX hY a).symm
    · calc
        _ = (A.restrict Y hY).combinedWeight b := gammaGroundMeasuredGammaCoprod_combined_right (A.restrict X hX) (A.restrict Y hY) b
        _ = A.combinedWeight ⟨b.1, GammaGroundMap.inclusion (hY b.1) b.2⟩ := rfl
        _ = _ := congrArg A.combinedWeight (gammaGroundFamilyPartitionMap_inr A.underlying X Y hX hY b).symm

theorem gammaGroundMeasuredGammaIsoClass_scissor {A B D E : GammaGroundMeasuredGammaObject hc ground k}
    (h : GammaGroundMeasuredGammaScissor A B D E) :
    gammaGroundMeasuredGammaIsoClass A + gammaGroundMeasuredGammaIsoClass B = gammaGroundMeasuredGammaIsoClass D + gammaGroundMeasuredGammaIsoClass E := by
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
  rw [gammaGroundMeasuredGammaIsoClass_empty, add_zero, ← gammaGroundMeasuredGammaIsoClass_coprod]
  exact gammaGroundMeasuredGammaIsoClass_eq_iff.mpr ⟨asIso (show _ ⟶ _ from
    gammaGroundMeasuredGammaPartitionHom U X (U.underlying.difference X) hX (fun _ _ h => h.1) hd hu)⟩

def gammaGroundMeasuredGammaKPlusToIsoClasses : GammaGroundMeasuredGammaKPlus hc ground k →+ GammaGroundMeasuredGammaIsoClasses hc ground k :=
  PositiveAdditiveGrothendieck.lift (gammaGroundMeasuredGammaPresentation hc ground k) {
    toFun := gammaGroundMeasuredGammaIsoClass
    iso := gammaGroundMeasuredGammaIsoClass_eq_iff.mpr
    empty := gammaGroundMeasuredGammaIsoClass_empty
    scissor := gammaGroundMeasuredGammaIsoClass_scissor }

@[simp] theorem gammaGroundMeasuredGammaKPlusToIsoClasses_class (A : GammaGroundMeasuredGammaObject hc ground k) :
    gammaGroundMeasuredGammaKPlusToIsoClasses (gammaGroundMeasuredGammaClass A) = gammaGroundMeasuredGammaIsoClass A :=
  PositiveAdditiveGrothendieck.lift_of _ _ A

theorem gammaGroundMeasuredGammaClass_eq_iff_iso {A B : GammaGroundMeasuredGammaObject hc ground k} :
    gammaGroundMeasuredGammaClass A = gammaGroundMeasuredGammaClass B ↔ Nonempty (A ≅ B) := by
  constructor
  · intro h
    apply gammaGroundMeasuredGammaIsoClass_eq_iff.mp
    simpa only [gammaGroundMeasuredGammaKPlusToIsoClasses_class] using congrArg gammaGroundMeasuredGammaKPlusToIsoClasses h
  · rintro ⟨e⟩
    exact gammaGroundMeasuredGammaClass_iso e

end DiamondIntegral.Section3
