import «section 3».GammaCoproducts
import «section 3».FamilyPartitions

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
variable {hc : CanonicalStructure.IsCanonical (M := M)} {S : Set M} {k : ℕ}

def gammaPartitionHom (A : GammaObject hc S k) (X Y : Fin A.tags → DefSet ((volumeGammaSpace hc).power (Fin k)) S)
    (hX : ∀ i, (X i).carrier ⊆ (A.piece i).carrier) (hY : ∀ i, (Y i).carrier ⊆ (A.piece i).carrier)
    (hd : ∀ i, Disjoint (X i).carrier (Y i).carrier)
    (hu : ∀ i, ((X i).union (Y i)).carrier = (A.piece i).carrier) :
    GammaHom ((A.restrict X).coprod (A.restrict Y)) A where
  bijection := familyPartitionBijection A X Y hX hY hd hu
  contraction := by
    let CX := fun i => codePreimage (X i)
    let CY := fun i => codePreimage (Y i)
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
    let F := familyPartitionBijection A.codeLift CX CY hCX hCY hdC huC
    let H := F.comp (familyCodeCoprodBridge (A.restrict X) (A.restrict Y))
    refine ⟨H, fun c => ?_⟩
    rcases familyCodeCoprod_cases (A.restrict X) (A.restrict Y) c with ⟨a, rfl⟩ | ⟨b, rfl⟩
    · change A.decode (familyPartitionMap A.codeLift CX CY hCX hCY
        ((familyCodeCoprodBridge (A.restrict X) (A.restrict Y)).equiv
          (familyCodeCoprodInl (A.restrict X) (A.restrict Y) a))) =
        familyPartitionMap A X Y hX hY
          (((A.restrict X).coprod (A.restrict Y)).decode
            (familyCodeCoprodInl (A.restrict X) (A.restrict Y) a))
      rw [familyCodeCoprodBridge_inl]
      calc
        _ = A.decode ⟨a.1, Map.inclusion (hCX a.1) a.2⟩ :=
          congrArg A.decode (familyPartitionMap_inl A.codeLift CX CY hCX hCY a)
        _ = familyPartitionMap A X Y hX hY
            (familyCoprodInl (A.restrict X) (A.restrict Y) ((A.restrict X).decode a)) :=
          (familyPartitionMap_inl A X Y hX hY ((A.restrict X).decode a)).symm
        _ = _ := congrArg (familyPartitionMap A X Y hX hY)
          (familyCodeCoprod_decode_inl (A.restrict X) (A.restrict Y) a).symm
    · change A.decode (familyPartitionMap A.codeLift CX CY hCX hCY
        ((familyCodeCoprodBridge (A.restrict X) (A.restrict Y)).equiv
          (familyCodeCoprodInr (A.restrict X) (A.restrict Y) b))) =
        familyPartitionMap A X Y hX hY
          (((A.restrict X).coprod (A.restrict Y)).decode
            (familyCodeCoprodInr (A.restrict X) (A.restrict Y) b))
      rw [familyCodeCoprodBridge_inr]
      calc
        _ = A.decode ⟨b.1, Map.inclusion (hCY b.1) b.2⟩ :=
          congrArg A.decode (familyPartitionMap_inr A.codeLift CX CY hCX hCY b)
        _ = familyPartitionMap A X Y hX hY
            (familyCoprodInr (A.restrict X) (A.restrict Y) ((A.restrict Y).decode b)) :=
          (familyPartitionMap_inr A X Y hX hY ((A.restrict Y).decode b)).symm
        _ = _ := congrArg (familyPartitionMap A X Y hX hY)
          (familyCodeCoprod_decode_inr (A.restrict X) (A.restrict Y) b).symm

theorem gammaIsoClass_scissor {A B D E : GammaObject hc S k} (h : GammaScissor A B D E) :
    gammaIsoClass A + gammaIsoClass B = gammaIsoClass D + gammaIsoClass E := by
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
  rw [gammaIsoClass_empty, add_zero, ← gammaIsoClass_coprod]
  exact gammaIsoClass_eq_iff.mpr ⟨asIso (show _ ⟶ _ from
    gammaPartitionHom U X (U.difference X) hX (fun _ _ h => h.1) hd hu)⟩

def gammaKPlusToIsoClasses : GammaKPlus hc S k →+ GammaIsoClasses hc S k :=
  PositiveAdditiveGrothendieck.lift (gammaPresentation hc S k) {
    toFun := gammaIsoClass
    iso := gammaIsoClass_eq_iff.mpr
    empty := gammaIsoClass_empty
    scissor := gammaIsoClass_scissor }

@[simp] theorem gammaKPlusToIsoClasses_class (A : GammaObject hc S k) :
    gammaKPlusToIsoClasses (gammaClass A) = gammaIsoClass A := PositiveAdditiveGrothendieck.lift_of _ _ A

theorem gammaClass_eq_iff_iso {A B : GammaObject hc S k} :
    gammaClass A = gammaClass B ↔ Nonempty (A ≅ B) := by
  constructor
  · intro h
    apply gammaIsoClass_eq_iff.mp
    simpa only [gammaKPlusToIsoClasses_class] using congrArg gammaKPlusToIsoClasses h
  · rintro ⟨e⟩
    exact gammaClass_iso e

end DiamondIntegral.Section3
