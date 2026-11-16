import «section 6».MeasuredRVCoverExtensionStep
import «section 6».FiniteDefSetIndexedUnions

/-! Assemble factorizations on a finite definable cover into one actual
whole-domain measured chain. Previously processed labels retain their
target volume. Every intermediate bound is proved on the full object. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem exists_measured_rv_factorization_from_cover (hc : CanonicalStructure.IsCanonical (M := M))
    (hn : 0 < n) {U V : MeasuredRVObject (M := M) S n} (e : MeasuredRVIso U V)
    {r : ℕ} (D : Fin r → DefSet (rawRVSpace (M := M) U.object.arity) S)
    (hD : ∀ j, (D j).carrier ⊆ U.object.domain.carrier)
    (hCover : ∀ u : U.object.domain, ∃ j, u.val ∈ (D j).carrier)
    (T : ∀ j, MeasuredRVUnaryChain S n (U.restrict (D j) (hD j))
      (V.restrict (e.iso.hom.map.restrict (hD j)).image (rvLabelImage_subset e.iso (D j) (hD j))))
    (hT : ∀ j, (T j).iso.iso.hom.map = (e.restrict (D j) (hD j)).iso.hom.map)
    (hTB : ∀ j, (U.doublyBounded ∧ V.doublyBounded) → (T j).doublyBounded) :
    ∃ L : MeasuredRVUnaryChain S n U V, L.iso.iso.hom.map = e.iso.hom.map ∧
      ((U.doublyBounded ∧ V.doublyBounded) → L.doublyBounded) := by
  let P (I : Finset (Fin r)) := finiteDefSetIndexedUnion D I
  have hP (I : Finset (Fin r)) : (P I).carrier ⊆ U.object.domain.carrier :=
    finiteDefSetIndexedUnion_subset D I U.object.domain hD
  let i₀ : Fin n := ⟨0,hn⟩
  have hPart (I : Finset (Fin r)) :
      ∃ L : MeasuredRVUnaryChain S n U (measuredRVLabelReplacement hc e (P I) (hP I)),
        (∀ u, L.iso.iso.hom.map u = u) ∧ ((U.doublyBounded ∧ V.doublyBounded) → L.doublyBounded) := by
    induction I using Finset.induction_on with
    | empty =>
      have hEmpty (u : U.object.domain) : u.val ∉ (P ∅).carrier := finiteDefSetIndexedUnion_empty D u.val
      let d := measuredRVLabelReplacementInitialIso hc e (P ∅) (hP ∅) hEmpty
      have hd : RVUnaryRelativeAt d.iso.hom.map i₀ := by
        intro u k hk
        exact congrFun (measuredRVLabelReplacement_of_not_mem hc e (P ∅) (hP ∅) u (hEmpty u)) k
      exact ⟨.step i₀ d hd (.identity _),fun _ => rfl,fun hB =>
        ⟨hB.1,measuredRVLabelReplacement_doublyBounded hc e (P ∅) (hP ∅) hB.1 hB.2⟩⟩
    | @insert i I hi ih =>
      obtain ⟨L,hL,hLB⟩ := ih
      have hUnion (u : U.object.domain) :
          u.val ∈ (P (insert i I)).carrier ↔ u.val ∈ (P I).carrier ∨ u.val ∈ (D i).carrier :=
        finiteDefSetIndexedUnion_insert D I i u.val
      obtain ⟨H,hH,hHB⟩ := exists_measured_rv_cover_extension_step hc hn e
        (P I) (D i) (P (insert i I)) (hP I) (hD i) (hP (insert i I)) hUnion (T i) (hT i)
      refine ⟨L.comp H,fun u => ?_,fun hB => L.comp_doublyBounded H (hLB hB) (hHB ⟨hB.1,hB.2,hTB i hB⟩)⟩
      rw [MeasuredRVUnaryChain.comp_map,hL,hH]
  obtain ⟨L,hL,hLB⟩ := hPart Finset.univ
  have hAll (u : U.object.domain) : u.val ∈ (P Finset.univ).carrier := by
    obtain ⟨j,hj⟩ := hCover u
    exact (finiteDefSetIndexedUnion_mem D Finset.univ u.val).mpr ⟨j,Finset.mem_univ j,hj⟩
  let d := measuredRVLabelReplacementFinalIso hc e (P Finset.univ) (hP Finset.univ) hAll
  have hd : RVUnaryRelativeAt d.iso.hom.map i₀ := by
    intro u k hk
    exact (congrFun (measuredRVLabelReplacement_of_mem hc e (P Finset.univ) (hP Finset.univ) u (hAll u)) k).symm
  let H : MeasuredRVUnaryChain S n (measuredRVLabelReplacement hc e (P Finset.univ) (hP Finset.univ)) V :=
    .step i₀ d hd (.identity V)
  refine ⟨L.comp H,?_,fun hB => L.comp_doublyBounded H (hLB hB)
    ⟨measuredRVLabelReplacement_doublyBounded hc e (P Finset.univ) (hP Finset.univ) hB.1 hB.2,hB.2⟩⟩
  apply Map.ext
  intro u
  rw [MeasuredRVUnaryChain.comp_map,hL]
  rfl

end DiamondIntegral.Section6
