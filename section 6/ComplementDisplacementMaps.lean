import «section 6».RestoredComplementContractionStages
import «section 6».RVCoordinateDisplacements

/-! Construct the actual complementary undo map from the full inverse
of a prepared bijection. Its label constancy is proved from the checked
coordinate-displacement certificate, with no chosen VF representatives. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 12000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

def vfZeroLastMap (S : Set M) (n : ℕ) :
    Map (DefSet.univ (rawVFSpace (M := M) (n+1)) S) (DefSet.univ (rawVFSpace (M := M) (n+1)) S) := by
  let P := rawVFSpace (M := M) (n+1)
  let f (x : Fin (n+1) → VF M) := Function.update x (Fin.last n) 0
  let F (z : Fin (n+1) → M) := Function.update z (Fin.last n) iVFZero
  have hZero : S.DefinableFun LRV (fun _ : Fin (n+1) → M => iVFZero) :=
    (Set.DefinableFun.of_empty (Set.DefinableFun.fun_symbol (M := M) (L := LRV) Fn.vfZero)).comp (fun i => i.elim0)
  have hF : S.DefinableMap LRV F := by
    intro i
    by_cases hi : i=Fin.last n
    · subst i
      simpa only [F,Function.update_self] using hZero
    · simpa only [F,Function.update_of_ne hi] using (Set.DefinableFun.proj LRV (i := i) : S.DefinableFun LRV (fun z : Fin (n+1) → M => z i))
  have hCode (c : P.domain) : vfValues (f (P.decode c))=F c.val := by
    funext i
    change (f (P.decode c) i).val=F c.val i
    by_cases hi : i=Fin.last n
    · subst i
      simp only [f,F,Function.update_self]
      rfl
    · simp only [f,F,Function.update_of_ne hi]
      exact congrFun (vfValues_decode c) i
  have hDom (c : P.domain) : F c.val ∈ P.domain := ⟨f (P.decode c),hCode c⟩
  refine Map.ofCodes (DefSet.univ P S) f F hF hDom ?_
  intro c
  exact vfValues_injective ((vfValues_decode ⟨_,hDom c⟩).trans (hCode c).symm)

theorem vfZeroLastMap_value (S : Set M) (n : ℕ) (p : DefSet.univ (rawVFSpace (M := M) (n+1)) S) :
    (vfZeroLastMap S n p).val=Function.update p.val (Fin.last n) 0 := rfl

variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}
variable {B : DefSet (rawMixedSpace (M := M) (n+1) s) S}

def complementUndoShift (f : Map A B) (hf : Function.Bijective f) :
    Map B (DefSet.univ (rawVFSpace (M := M) (n+1)) S) := by
  let H := (mixedVFHeadMap A).comp (f.inverse hf)
  let D := (vfTupleBinaryMap S .sub).comp
    ((Map.inclusion (fun _ _ => Set.mem_univ _)).comp (H.pair (mixedVFHeadMap B)))
  exact (vfZeroLastMap S n).comp D

theorem complementUndoShift_last (f : Map A B) (hf : Function.Bijective f) (p : B) :
    rvTranslationVector (complementUndoShift f hf) p (Fin.last n)=0 := by
  change Function.update (fun i => (f.inverse hf p).val.1 i-p.val.1 i) (Fin.last n) 0 (Fin.last n)=0
  rw [Function.update_self]

theorem complementUndoShift_castSucc (f : Map A B) (hf : Function.Bijective f) (p : B) (i : Fin n) :
    rvTranslationVector (complementUndoShift f hf) p i.castSucc=
      (f.inverse hf p).val.1 i.castSucc-p.val.1 i.castSucc := by
  change Function.update (fun j => (f.inverse hf p).val.1 j-p.val.1 j) (Fin.last n) 0 i.castSucc=_
  rw [Function.update_of_ne (Fin.castSucc_ne_last i)]

theorem complementUndoShift_rv_constant
    (f : Map A B) (hf : Function.Bijective f) (hD : ∀ i : Fin n,RVCoordinateDisplacement f i.castSucc)
    (p z : B) (hTags : p.val.2=z.val.2) : complementUndoShift f hf p=complementUndoShift f hf z := by
  apply Subtype.ext
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact (complementUndoShift_last f hf p).trans (complementUndoShift_last f hf z).symm
  · change rvTranslationVector (complementUndoShift f hf) p j.castSucc=
      rvTranslationVector (complementUndoShift f hf) z j.castSucc
    rw [complementUndoShift_castSucc,complementUndoShift_castSucc]
    have h := hD j (f.inverse hf p) (f.inverse hf z) (by rw [Map.apply_inverse,Map.apply_inverse]; exact hTags)
    rw [Map.apply_inverse,Map.apply_inverse] at h
    simpa only [neg_sub] using congrArg (fun x : VF M => -x) h

theorem complementUndoShift_restores
    (f : Map A B) (hf : Function.Bijective f) (p : A) (i : Fin n) :
    (f p).val.1 i.castSucc+rvTranslationVector (complementUndoShift f hf) (f p) i.castSucc=p.val.1 i.castSucc := by
  rw [complementUndoShift_castSucc,Map.inverse_apply]
  abel

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem contraction_stage_of_rv_displacements
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    (linear : GammaPiecewiseRationalAffineInput (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    {f : Map A B} (H : SpecialCovariantChain (G := G) A B f)
    (hAD : VFDoublyBounded A.carrier) (hBD : VFDoublyBounded B.carrier)
    (hBRP : IsRVPullback B.carrier) (k : Fin s)
    (hLeading : ∀ p ∈ B.carrier,rv M (p.1 (Fin.last n))=p.2 k)
    (hD : ∀ i : Fin n,RVCoordinateDisplacement f i.castSucc) :
    Nonempty (StandardContractionStage (G := G) A) := by
  let hf := H.bijective h00
  exact contraction_stage_of_restored_complement h00 hc linear hκ hs hv hsmall hΓ H hAD hBD hBRP k hLeading
    (complementUndoShift f hf) (complementUndoShift_rv_constant f hf hD)
    (complementUndoShift_last f hf) (complementUndoShift_restores f hf)

end DiamondIntegral.Section6
