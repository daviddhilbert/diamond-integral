import «section 6».ProgramTerminalData
import «section 6».PreparedFamilyAssembly

/-! Remove identity prefixes on the exact actual families, and
precompose regularization prefixes with exact full protected images.
No equality between untyped raw templates is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s q k : ℕ}
variable {B : DefSet (rawMixedSpace (M := M) 1 r) S}

theorem unaryIndexedMixedFamily_eq_of_fibres
    (η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S))
    (A D : MixedSetParameterTemplate (M := M) S 1 n s)
    (h : ∀ b : B,A.fibre (unaryFamilyParameter η b)=D.fibre (unaryFamilyParameter η b)) :
    unaryIndexedMixedFamily η A=unaryIndexedMixedFamily η D := by
  apply defSet_eq_of_carrier_eq
  ext p
  rw [mem_unaryIndexedMixedFamily,mem_unaryIndexedMixedFamily]
  constructor
  · rintro ⟨b,hb,hA⟩
    exact ⟨b,hb,h b ▸ hA⟩
  · rintro ⟨b,hb,hD⟩
    exact ⟨b,hb,(h b).symm ▸ hD⟩

variable {η : Map B (DefSet.univ (rawVFSpace (M := M) 1) S)}
variable {A : MixedSetParameterTemplate (M := M) S 1 n s}
variable {P : Fin k → MixedSetParameterTemplate (M := M) S 1 n s}
variable {C : DefSet (rawMixedSpace (M := M) (n+1) q) S} {π : Fin r → Fin q} {σ : Fin s → Fin q}

theorem identity_selected_piece_eq
    (hPA : ∀ b : B,∀ i,((P i).fibre (unaryFamilyParameter η b)).carrier ⊆
      (A.fibre (unaryFamilyParameter η b)).carrier) (i : Fin k) :
    rvLabelPullback C (Fin.addCases π σ)
      (unaryIndexedMixedFamily η ((CentripetalProgramTemplate.identity s).pieceTarget A (P i)))=
    rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)) := by
  rw [unaryIndexedMixedFamily_eq_of_fibres η _ (P i)
    (fun b => identity_pieceTarget_fibre A (P i) _ (hPA b i))]

def SelectedProgramContext.afterIdentity (X : SelectedProgramContext η A P C π σ)
    (hPA : ∀ b : B,∀ i,((P i).fibre (unaryFamilyParameter η b)).carrier ⊆
      (A.fibre (unaryFamilyParameter η b)).carrier) :
    SelectedProgramContext η ((CentripetalProgramTemplate.identity s).target A)
      (fun i => (CentripetalProgramTemplate.identity s).pieceTarget A (P i)) C π σ := by
  refine ⟨X.proper,X.doublyBounded,X.pullback,?_,?_⟩
  · intro p hp
    change selectedJointPoint π σ p ∈
      (unaryIndexedMixedFamily η ((CentripetalProgramTemplate.identity s).pieceTarget A A)).carrier
    rw [unaryIndexedMixedFamily_eq_of_fibres η _ A
      (fun b => identity_pieceTarget_fibre A A _ (Set.Subset.refl _))]
    exact X.source p hp
  · intro i
    rw [identity_selected_piece_eq hPA i]
    exact X.piecesProper i

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def SelectedProgramContext.precomposeRegularization
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : SelectedProgramContext η A P C π σ)
    (hPA : ∀ b : B,∀ i,((P i).fibre (unaryFamilyParameter η b)).carrier ⊆
      (A.fibre (unaryFamilyParameter η b)).carrier)
    (F : PreparedSynchronizedFamily (G := G) (regularizeMap C).image
      (fun i => rvLabelPullback (regularizeMap C).image
        (Fin.addCases (regularizedBaseLabels π) (regularizedTailLabels σ))
        (unaryIndexedMixedFamily η ((CentripetalProgramTemplate.regularize s).pieceTarget A (P i))))
      (fun i => rvLabelPullback_subset _ _ _)) :
    PreparedSynchronizedFamily (G := G) C
      (fun i => rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i)))
      (fun i => rvLabelPullback_subset C _ _) := by
  let Q (i) := rvLabelPullback C (Fin.addCases π σ) (unaryIndexedMixedFamily η (P i))
  have hQC (i) : (Q i).carrier ⊆ C.carrier := rvLabelPullback_subset C _ _
  let F' : PreparedSynchronizedFamily (G := G) (regularizeMap C).image
      (fun i => ((regularization C).restrict (hQC i)).image)
      (fun i z hz => by obtain ⟨p,hp⟩ := hz; exact hp ▸ ((regularization C).restrict (hQC i) p).property) :=
    F.changePieces (fun i => regularized_selected_family η A (P i) (fun b => hPA b i) C π σ X.base)
  exact F'.precompose hQC
    (.regularize C X.proper X.doublyBounded Q hQC X.piecesProper
      (fun i => X.doublyBounded.mono (hQC i)))

end DiamondIntegral.Section6
