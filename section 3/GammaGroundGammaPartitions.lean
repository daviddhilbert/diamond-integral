import «section 3».GammaGroundGammaCoproducts
import «section 3».GammaGroundFamilyPartitions
/-! Actual Gamma partition isomorphisms and the resulting comparison
between positive scissor equality and genuine Gamma isomorphism. -/
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

def gammaGroundGammaPartitionHom (A : GammaGroundGammaObject hc ground k) (X Y : Fin A.tags → GammaGroundDefSet hc ground ((volumeGammaSpace hc).power (Fin k)))
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier) (hY : ∀ i, (Y i).carrier ⊆ (A.piece i).carrier)
    (hd : ∀ i, Disjoint (X i).carrier (Y i).carrier)
    (hu : ∀ i, ((X i).union (Y i)).carrier = (A.piece i).carrier) :
    GammaGroundGammaHom ((A.restrict X).coprod (A.restrict Y)) A where
  bijection := gammaGroundFamilyPartitionBijection A X Y hX hY hd hu
  contraction := by
    let CX := fun i => gammaGroundCodePreimage (X i)
    let CY := fun i => gammaGroundCodePreimage (Y i)
    have hCX : ∀ i, (CX i).carrier ⊆ (A.codeLift.piece i).carrier := fun i _ h => hX i h
    have hCY : ∀ i, (CY i).carrier ⊆ (A.codeLift.piece i).carrier := fun i _ h => hY i h
    have hdC : ∀ i, Disjoint (CX i).carrier (CY i).carrier := fun i =>
      Set.disjoint_left.mpr (fun _ hx hy => Set.disjoint_left.mp (hd i) hx hy)
    have huC : ∀ i, ((CX i).union (CY i)).carrier = (A.codeLift.piece i).carrier := by
      intro i
      ext c
      change ((((volumeGammaSpace hc).power (Fin k)).decode c ∈ (X i).carrier) ∨
        (((volumeGammaSpace hc).power (Fin k)).decode c ∈ (Y i).carrier)) ↔
        ((volumeGammaSpace hc).power (Fin k)).decode c ∈ (A.piece i).carrier
      rw [← hu i]
      rfl
    let F := gammaGroundFamilyPartitionBijection A.codeLift CX CY hCX hCY hdC huC
    let H := F.comp (gammaGroundFamilyCodeCoprodBridge (A.restrict X) (A.restrict Y))
    refine ⟨H, fun c => ?_⟩
    rcases gammaGroundFamilyCodeCoprod_cases (A.restrict X) (A.restrict Y) c with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · change A.decode (gammaGroundFamilyPartitionMap A.codeLift CX CY hCX hCY
        ((gammaGroundFamilyCodeCoprodBridge (A.restrict X) (A.restrict Y)).equiv
          (gammaGroundFamilyCodeCoprodInl (A.restrict X) (A.restrict Y) a))) =
        gammaGroundFamilyPartitionMap A X Y hX hY
          (((A.restrict X).coprod (A.restrict Y)).decode
            (gammaGroundFamilyCodeCoprodInl (A.restrict X) (A.restrict Y) a))
      rw [gammaGroundFamilyCodeCoprodBridge_inl]
      calc
        _ = A.decode ⟨a.1, GammaGroundMap.inclusion (hCX a.1) a.2⟩ :=
          congrArg A.decode (gammaGroundFamilyPartitionMap_inl A.codeLift CX CY hCX hCY a)
        _ = gammaGroundFamilyPartitionMap A X Y hX hY
            (gammaGroundFamilyCoprodInl (A.restrict X) (A.restrict Y) ((A.restrict X).decode a)) :=
          (gammaGroundFamilyPartitionMap_inl A X Y hX hY ((A.restrict X).decode a)).symm
        _ = _ := congrArg (gammaGroundFamilyPartitionMap A X Y hX hY)
          (gammaGroundFamilyCodeCoprod_decode_inl (A.restrict X) (A.restrict Y) a).symm
    · change A.decode (gammaGroundFamilyPartitionMap A.codeLift CX CY hCX hCY
        ((gammaGroundFamilyCodeCoprodBridge (A.restrict X) (A.restrict Y)).equiv
          (gammaGroundFamilyCodeCoprodInr (A.restrict X) (A.restrict Y) b))) =
        gammaGroundFamilyPartitionMap A X Y hX hY
          (((A.restrict X).coprod (A.restrict Y)).decode
            (gammaGroundFamilyCodeCoprodInr (A.restrict X) (A.restrict Y) b))
      rw [gammaGroundFamilyCodeCoprodBridge_inr]
      calc
        _ = A.decode ⟨b.1, GammaGroundMap.inclusion (hCY b.1) b.2⟩ :=
          congrArg A.decode (gammaGroundFamilyPartitionMap_inr A.codeLift CX CY hCX hCY b)
        _ = gammaGroundFamilyPartitionMap A X Y hX hY
            (gammaGroundFamilyCoprodInr (A.restrict X) (A.restrict Y) ((A.restrict Y).decode b)) :=
          (gammaGroundFamilyPartitionMap_inr A X Y hX hY ((A.restrict Y).decode b)).symm
        _ = _ := congrArg (gammaGroundFamilyPartitionMap A X Y hX hY)
          (gammaGroundFamilyCodeCoprod_decode_inr (A.restrict X) (A.restrict Y) b).symm

theorem gammaGroundGammaIsoClass_scissor {A B D E : GammaGroundGammaObject hc ground k} (h : GammaGroundGammaScissor A B D E) :
    gammaGroundGammaIsoClass A + gammaGroundGammaIsoClass B = gammaGroundGammaIsoClass D + gammaGroundGammaIsoClass E := by
  obtain ⟨U, X, hX, hA, hB, hD, hE⟩ := h
  subst A
  subst B
  subst D
  subst E
  have hd : ∀ i, Disjoint (X i).carrier ((U.difference X) i).carrier := fun i =>
    Set.disjoint_left.mpr (fun _ hx hy => hy.2 hx)
  have hu : ∀ i, ((X i).union ((U.difference X) i)).carrier = (U.piece i).carrier := by
    intro i
    ext t
    change (t ∈ (X i).carrier ∨ (t ∈ (U.piece i).carrier ∧ t ∉ (X i).carrier)) ↔ t ∈ (U.piece i).carrier
    constructor
    · exact fun h => h.elim (fun h => hX i h) (fun h => h.1)
    · intro ht
      by_cases hx : t ∈ (X i).carrier
      · exact Or.inl hx
      · exact Or.inr ⟨ht, hx⟩
  rw [gammaGroundGammaIsoClass_empty, add_zero, ← gammaGroundGammaIsoClass_coprod]
  exact gammaGroundGammaIsoClass_eq_iff.mpr ⟨asIso (show _ ⟶ _ from
    gammaGroundGammaPartitionHom U X (U.difference X) hX (fun _ _ h => h.1) hd hu)⟩

def gammaGroundGammaKPlusToIsoClasses : GammaGroundGammaKPlus hc ground k →+ GammaGroundGammaIsoClasses hc ground k :=
  PositiveAdditiveGrothendieck.lift (gammaGroundGammaPresentation hc ground k) {
    toFun := gammaGroundGammaIsoClass
    iso := gammaGroundGammaIsoClass_eq_iff.mpr
    empty := gammaGroundGammaIsoClass_empty
    scissor := gammaGroundGammaIsoClass_scissor }

@[simp] theorem gammaGroundGammaKPlusToIsoClasses_class (A : GammaGroundGammaObject hc ground k) :
    gammaGroundGammaKPlusToIsoClasses (gammaGroundGammaClass A) = gammaGroundGammaIsoClass A := PositiveAdditiveGrothendieck.lift_of _ _ A

theorem gammaGroundGammaClass_eq_iff_iso {A B : GammaGroundGammaObject hc ground k} :
    gammaGroundGammaClass A = gammaGroundGammaClass B ↔ Nonempty (A ≅ B) := by
  constructor
  · intro h
    apply gammaGroundGammaIsoClass_eq_iff.mp
    simpa only [gammaGroundGammaKPlusToIsoClasses_class] using congrArg gammaGroundGammaKPlusToIsoClasses h
  · rintro ⟨e⟩
    exact gammaGroundGammaClass_iso e

end DiamondIntegral.Section3
