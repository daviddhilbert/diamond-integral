import «section 6».UnaryBoundaryFocus
import «section 6».ClopenCriterion

/-! Actual whole-core domains cut out by a center map and an offset
map. Their complete original-base defining formula and properness are
constructed before invoking any boundary-core preparation. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryFocusData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r : ℕ}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable (F : UnaryFocusData A)
variable (dMap : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S))

def offsetCoreCode (z : Fin 1 ⊕ Fin r → M) : Prop :=
  ¬ iLe (iRv (iVFAdd (z (.inl 0)) (iVFNeg (scalarCodeExtension F.focusMap z))))
    (iRv (scalarCodeExtension dMap z))

theorem offsetCoreCode_definable : S.Definable LRV {z | F.offsetCoreCode dMap z} :=
  (rvCode_compare_definable
    (rv_scalarCode_definable (scalarSubCode_definable (Set.DefinableFun.proj LRV)
      (scalarCodeExtension_definable F.focusMap)))
    (rv_scalarCode_definable (scalarCodeExtension_definable dMap))).compl

def offsetCoreDomain : DefSet (rawMixedSpace (M := M) 1 r) S := by
  refine ⟨{p | p ∈ (focusActive A F.activeTags).carrier ∧ F.offsetCoreCode dMap (mixedValues p)},?_⟩
  apply (mixed_definable_iff_values_image S _).mpr
  have h := ((mixed_definable_iff_values_image S _).mp (focusActive A F.activeTags).definable).inter
    (F.offsetCoreCode_definable dMap)
  convert h using 1
  ext z
  constructor
  · rintro ⟨p,⟨hp,hc⟩,he⟩
    exact ⟨⟨p,hp,he⟩,he ▸ hc⟩
  · rintro ⟨⟨p,hp,he⟩,hc⟩
    exact ⟨p,⟨hp,he.symm ▸ hc⟩,he⟩

theorem offsetCoreDomain_subset : (F.offsetCoreDomain dMap).carrier ⊆ A.carrier := fun _ hp => hp.1.1

variable (d : (Fin r → RVInfinity M) → VF M)
variable (hdMap : ∀ p : focusActive A F.activeTags,(dMap p).val 0=d p.val.2)
include hdMap in
theorem mem_offsetCoreDomain (p : Mixed M 1 r) :
    p ∈ (F.offsetCoreDomain dMap).carrier ↔ p ∈ A.carrier ∧ p.2 ∈ F.activeTags.carrier ∧
      vfValue (d p.2) < vfValue (p.1 0-F.focus p.2) := by
  by_cases hp : p ∈ (focusActive A F.activeTags).carrier
  · have hFocus := scalarCodeExtension_at F.focusMap ⟨p,hp⟩
    have hD := scalarCodeExtension_at dMap ⟨p,hp⟩
    rw [F.focusMap_eq] at hFocus
    rw [hdMap] at hD
    change (p ∈ (focusActive A F.activeTags).carrier ∧ F.offsetCoreCode dMap (mixedValues p)) ↔ _
    rw [and_iff_right hp]
    change F.offsetCoreCode dMap (mixedValues p) ↔ _
    rw [and_iff_right hp.1,and_iff_right hp.2]
    change (¬ iLe (iRv (iVFAdd _ (iVFNeg _))) (iRv _)) ↔ _
    rw [hFocus,hD]
    change (¬ iLe (rv M (p.1 0-F.focus p.2)).val (rv M (d p.2)).val) ↔ _
    rw [← Values.vrv_le_iff,not_le]
    rfl
  · constructor
    · exact fun h => (hp h.1).elim
    · exact fun h => (hp ⟨h.1,h.2.1⟩).elim

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
include hdMap in
theorem offsetCoreDomain_proper
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hd : ∀ u ∈ F.activeTags.carrier,d u ≠ 0) :
    ProperInvariant S (F.offsetCoreDomain dMap).carrier := by
  apply (lemma_6_5 h00 hc hκ hs hv _ (F.offsetCoreDomain dMap).definable
    (F.sourceProper.vfBounded.mono (F.offsetCoreDomain_subset dMap))
    (F.sourceProper.rvBounded.mono (F.offsetCoreDomain_subset dMap))).mpr
  intro u
  by_cases hu : u ∈ F.activeTags.carrier
  · have hFibre : vfFibre (F.offsetCoreDomain dMap).carrier u=
        vfFibre A.carrier u ∩ (fun x : Fin 1 → VF M => x 0) ⁻¹'
          centeredGammaDisc (F.focus u) (finiteValue (d u) (hd u hu)) := by
      ext x
      rw [show x ∈ vfFibre (F.offsetCoreDomain dMap).carrier u ↔ (x,u) ∈ (F.offsetCoreDomain dMap).carrier from Iff.rfl,
        F.mem_offsetCoreDomain dMap d hdMap]
      change ((x,u) ∈ A.carrier ∧ u ∈ F.activeTags.carrier ∧ vfValue (d u) < vfValue (x 0-F.focus u)) ↔
        ((x,u) ∈ A.carrier ∧ x 0 ∈ centeredGammaDisc (F.focus u) (finiteValue (d u) (hd u hu)))
      rw [mem_centeredGammaDisc]
      exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hu,h.2⟩⟩
    rw [hFibre]
    exact (F.sourceProper.clopen_fibres hv u).inter
      ((centeredGammaDisc_clopen hv _ _).preimage (continuous_apply 0))
  · have hEmpty : vfFibre (F.offsetCoreDomain dMap).carrier u=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hu ((F.mem_offsetCoreDomain dMap d hdMap (x,u)).mp hx).2.1
    rw [hEmpty]
    exact isClopen_empty

end DiamondIntegral.Section6.UnaryFocusData
