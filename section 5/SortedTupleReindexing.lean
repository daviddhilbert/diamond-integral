import IntegrationSection6.GammaSortedTotalBijections

/-! Coordinate permutations preserve complete sorted original-language
domains and full bijection graphs. This groups VF and RV coordinates in
literal total mixed families without discarding any parameter block. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace DiamondIntegral.Section5
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section3.GammaParameters
open IntegrationInACVF.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {B : Base (M := M)} {a b c d : ℕ}

def sortedReindexedDomain (ρ : Fin a ≃ Fin c) (D : Set (Fin a → M)) : Set (Fin c → M) :=
  (fun w => w ∘ ρ.symm) '' D

def sortedReindexedEquiv (ρ : Fin a ≃ Fin c) (D : Set (Fin a → M)) : D ≃ sortedReindexedDomain ρ D :=
  Equiv.ofBijective (fun w => ⟨w.val ∘ ρ.symm,⟨w.val,w.property,rfl⟩⟩) ⟨by
    intro x y h
    apply Subtype.ext
    funext i
    have hi := congrFun (congrArg Subtype.val h) (ρ i)
    simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hi,by
      rintro ⟨w,x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩⟩

theorem sortedReindexedDomain_definable {sa : Fin a → SortTag}
    (ρ : Fin a ≃ Fin c) {D : Set (Fin a → M)} (hD : DefinableOverBase B sa D) :
    DefinableOverBase B (sa ∘ ρ.symm) (sortedReindexedDomain ρ D) := hD.image_real ρ.symm

def reindexPairCoordinates (ρ : Fin a ≃ Fin c) (τ : Fin b ≃ Fin d) : Fin (c+d) → Fin (a+b) :=
  Fin.addCases (fun i => Fin.castAdd b (ρ.symm i)) (fun j => Fin.natAdd a (τ.symm j))

omit [LRV.Structure M] [M ⊨ Axioms.ACVF] in
theorem reindexPairCoordinates_append {α : Type*} (ρ : Fin a ≃ Fin c) (τ : Fin b ≃ Fin d)
    (x : Fin a → α) (y : Fin b → α) :
    Fin.append x y ∘ reindexPairCoordinates ρ τ = Fin.append (x ∘ ρ.symm) (y ∘ τ.symm) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp only [reindexPairCoordinates,Function.comp_apply,Fin.addCases_left,Fin.addCases_right,
      Fin.append_left,Fin.append_right]

def sortedIsoReindex {sa : Fin a → SortTag} {sb : Fin b → SortTag}
    {D : Set (Fin a → M)} {E : Set (Fin b → M)}
    (H : GammaSortedIso B sa sb D E) (ρ : Fin a ≃ Fin c) (τ : Fin b ≃ Fin d) :
    GammaSortedIso B (sa ∘ ρ.symm) (sb ∘ τ.symm)
      (sortedReindexedDomain ρ D) (sortedReindexedDomain τ E) := by
  let P := sortedReindexedEquiv ρ D
  let Q := sortedReindexedEquiv τ E
  let e := P.symm.trans (H.equiv.trans Q)
  have h := H.graph.image_real (reindexPairCoordinates ρ τ)
  have hsort : Fin.append sa sb ∘ reindexPairCoordinates ρ τ = Fin.append (sa ∘ ρ.symm) (sb ∘ τ.symm) :=
    reindexPairCoordinates_append ρ τ sa sb
  rw [hsort] at h
  refine ⟨e,?_⟩
  convert h using 1
  ext w
  constructor
  · rintro ⟨u,hu⟩
    let x := P.symm u
    have hx : x.val ∘ ρ.symm = u.val := congrArg Subtype.val (P.apply_symm_apply u)
    refine ⟨Fin.append x.val (H.equiv x).val,⟨x,rfl⟩,?_⟩
    change Fin.append x.val (H.equiv x).val ∘ reindexPairCoordinates ρ τ = w
    rw [reindexPairCoordinates_append,hx]
    exact hu
  · rintro ⟨v,⟨u,rfl⟩,hw⟩
    refine ⟨P u,?_⟩
    change Fin.append (u.val ∘ ρ.symm) ((H.equiv (P.symm (P u))).val ∘ τ.symm) = w
    rw [P.symm_apply_apply]
    exact (reindexPairCoordinates_append ρ τ _ _).symm.trans hw

end DiamondIntegral.Section5
