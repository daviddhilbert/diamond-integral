import «section 3».IntegrationFullFiniteSupport
import IntegrationSection3ACVF.CoordinatePartitions
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M ι τ : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- A single finite partition only uses finite real support of its graph and
positive Gamma witness. All original imaginary parameters are retained. -/
theorem integrationFullCoordinatePartition [Finite ι] [Finite τ] {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ)
    (B : FullBaseAtomicity.Base (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (δ : Values.Gamma (M := M)) (hδ : FullGammaSyntax.Scalar B {δ}) (hδ1 : 1 < δ)
    (A : Set (ι → M)) (f : (ι → M) → (τ → M))
    (hf : FullBaseAtomicity.OverBase B (FiniteTupleGraphs.graph A f)) (hinj : Set.InjOn f A)
    (I : Set ι) (J : Set τ)
    (hSrcVF : ∀ i ∈ I, ∀ x ∈ A, iVF (x i)) (hTarVF : ∀ j ∈ J, ∀ x ∈ A, iVF (f x j)) :
    ∃ P : Finset (Set (ι → M)),
      (∀ W ∈ P, W.Nonempty ∧ W ⊆ A ∧ FullBaseAtomicity.OverBase B W ∧ CoordinateOpenToOpen.All W f I J) ∧
      (P : Set (Set (ι → M))).Pairwise Disjoint ∧ A = {x | ∃ W ∈ P, x ∈ W} := by
  obtain ⟨F,hFB,hfF⟩ := integrationFullFiniteRealSupport B _ hf
  obtain ⟨G,hGB,hδG⟩ := integrationFullFiniteRealSupport B _ hδ
  let C : FullBaseAtomicity.Base (M := M) := ⟨((F ∪ G : Finset M) : Set M),B.imaginary⟩
  have hFC : (F : Set M) ⊆ C.real := fun x hx => Finset.mem_union_left G hx
  have hGC : (G : Set M) ⊆ C.real := fun x hx => Finset.mem_union_right F hx
  have hCB : C.real ⊆ B.real := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hFB hx
    · exact hGB hx
  obtain ⟨P,hP,hDis,hCov⟩ := CoordinatePartitions.proposition_3_21 hκ hs C
    (integrationFinset_small (M := M) hκ (F ∪ G)) h00 δ
    (FullBaseAtomicity.OverBase.mono hδG hGC Set.Subset.rfl) hδ1 A f
    (FullBaseAtomicity.OverBase.mono hfF hFC Set.Subset.rfl) hinj I J hSrcVF hTarVF
  exact ⟨P,fun W hW => ⟨(hP W hW).1,(hP W hW).2.1,
    FullBaseAtomicity.OverBase.mono (hP W hW).2.2.1 hCB Set.Subset.rfl,(hP W hW).2.2.2⟩,hDis,hCov⟩
end DiamondIntegral.Section3
