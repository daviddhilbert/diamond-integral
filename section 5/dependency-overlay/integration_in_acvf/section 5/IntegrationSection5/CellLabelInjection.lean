import IntegrationSection5.RVRecodeInjection
import IntegrationSection5.GammaPermutationIso
import IntegrationSection5.MixedCellDecomposition

/-! The actual VF-coordinate-preserving RV-label injection in Corollary5.8.
Decomposition is applied to the swapped source so that the final cell
coordinates agree with the original VF tuple. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section5 SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section4 IntegrationInACVF.Section3ACVF
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m d : ℕ} {A : Set (Point (M := M) 2 m)}

structure CellLabelInjection (G : GammaParameters.Base (M := M)) {m : ℕ}
    (A : Set (Point (M := M) 2 m)) where
  arity : ℕ
  target : Set (Point (M := M) 2 arity)
  iso : GammaIso G A target
  fixes_vf : ∀ a : A, (iso.equiv a).val.1 = a.val.1
  cells : ∀ s, (nativeTwoFibre target s).Nonempty →
    Cells.DefinableTwoCell (RVLabelSlices.labelBase G s) (nativeTwoFibre target s)

theorem recoded_native_fibre (hA : GammaSetDefinable G A)
    (P : GammaRVMap G (vfPermutedSet A (Equiv.swap 0 1)) d) (a₀ : A) :
    let E := gammaPermutationIso A hA (Equiv.swap 0 1)
    let Q := P.precomp E.equiv E.graph
    nativeTwoFibre (rvRecodeTarget Q) (Q.toFun a₀) = mixedPairFibre P (E.equiv a₀) := by
  dsimp only
  let E := gammaPermutationIso A hA (Equiv.swap 0 1)
  let Q := P.precomp E.equiv E.graph
  ext p
  constructor
  · rintro ⟨a,he⟩
    have hv : a.val.1 = ![p.1,p.2] := congrArg Prod.fst he
    have hc : Q.toFun a = Q.toFun a₀ := congrArg Prod.snd he
    refine ⟨E.equiv a,?_,hc⟩
    change a.val.1 ∘ Equiv.swap 0 1 = ![p.2,p.1]
    rw [hv]
    funext i
    fin_cases i <;> rfl
  · rintro ⟨b,hb,hP⟩
    obtain ⟨a,rfl⟩ := E.equiv.surjective b
    refine ⟨a,Prod.ext ?_ hP⟩
    change a.val.1 ∘ Equiv.swap 0 1 = ![p.2,p.1] at hb
    funext i
    fin_cases i
    · exact congrFun hb 1
    · exact congrFun hb 0

theorem exists_cell_label_injection {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (h00 : M ⊨ Axioms.ACVF00) (G : GammaParameters.Base (M := M))
    (hsmall : Cardinal.mk G.real < κ) (hGenerated : VFGammaGeneratedBase G)
    (δ : Values.Gamma (M := M)) (hδ : δ ∈ G.gamma) (hδ1 : 1 < δ)
    {m : ℕ} (A : Set (Point (M := M) 2 m)) (hA : GammaSetDefinable G A) :
    Nonempty (CellLabelInjection G A) := by
  let E := gammaPermutationIso A hA (Equiv.swap 0 1)
  have hB := E.target_definable (gammaLogicInput G)
  obtain ⟨d,P,hP,hCells⟩ := mixed_two_cell_decomposition_with_rv hκ hs h00 G hsmall hGenerated
    δ hδ hδ1 _ hB
  let Q := P.precomp E.equiv E.graph
  have hLabels : ∀ a b, Q.toFun a = Q.toFun b → a.val.2 = b.val.2 := by
    intro a b he
    exact ((sameRV_iff _ _).mp (hP (E.equiv a) (E.equiv b) he)).2
  refine ⟨⟨d,rvRecodeTarget Q,rvRecodeIso Q hLabels,fun _ => rfl,?_⟩⟩
  intro s hs
  obtain ⟨p,a,ha⟩ := hs
  have hCode : Q.toFun a = s := congrArg Prod.snd ha
  have hEq := recoded_native_fibre hA P a
  change nativeTwoFibre (rvRecodeTarget Q) (Q.toFun a) = mixedPairFibre P (E.equiv a) at hEq
  rw [hCode] at hEq
  rw [hEq]
  have h := hCells (E.equiv a)
  change Cells.DefinableTwoCell (RVLabelSlices.labelBase G (Q.toFun a)) _ at h
  rwa [hCode] at h

end IntegrationInACVF.Section5
