import «section 6».VFReindexRefinementFrames
import «section 6».SynchronizedChainTransport

/-! Actual synchronized finite-chain lifts through ordinary VF-coordinate permutations and RV-label
refinements. The commuting square determines every protected image. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s t : ℕ} {I : Type*}
variable {e : Fin n ≃ Fin n}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

structure VFReindexedChainLift
    {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (X : VFReindexRefinementFrame A e) (f : Map A B) (P : I → DefSet (rawMixedSpace (M := M) n r) S) where
  target : VFReindexRefinementFrame B e
  map : Map X.data.base target.data.base
  chain : SynchronizedCentripetalChain (G := G) I X.data.base target.data.base map (fun i => X.selectedPiece (P i))
  commutes : ∀ p : X.data.base,((map p).val.1 ∘ e.symm,(map p).val.2 ∘ target.data.labels)=(f (X.oldPoint p)).val

namespace VFReindexedChainLift
variable {A : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
variable {C : DefSet (rawMixedSpace (M := M) n t) S} {X : VFReindexRefinementFrame A e}
variable {f : Map A B} {g : Map B C} {P : I → DefSet (rawMixedSpace (M := M) n r) S}

theorem partition_image (h00 : M ⊨ Axioms.ACVF00)
    (F : VFReindexedChainLift (G := G) X f P) (hinj : Function.Injective f)
    (i : I) (hPA : (P i).carrier ⊆ A.carrier) :
    (F.map.restrict (X.selectedPiece_subset (P i))).image=
      F.target.selectedPiece (f.restrict hPA).image := by
  apply defSet_eq_of_carrier_eq
  ext q
  constructor
  · rintro ⟨p,rfl⟩
    let p' : X.data.base := ⟨p.val,X.selectedPiece_subset (P i) p.property⟩
    apply (F.target.mem_selectedPiece (f.restrict hPA).image (F.map p').val).mpr
    have hOld : (X.oldPoint p').val ∈ (P i).carrier := ((X.mem_selectedPiece (P i) p.val).mp p.property).2
    exact ⟨(F.map p').property,⟨⟨(X.oldPoint p').val,hOld⟩,(F.commutes p').symm⟩⟩
  · intro hq
    obtain ⟨hqT,hqOld⟩ := (F.target.mem_selectedPiece (f.restrict hPA).image q).mp hq
    obtain ⟨p,hp⟩ := (F.chain.toChain.toSpecial.bijective h00).surjective ⟨q,hqT⟩
    have hpoint : (F.map p).val=q := congrArg Subtype.val hp
    have hComm := F.commutes p
    rw [hpoint] at hComm
    obtain ⟨a,ha⟩ := hqOld
    have hEq : f ⟨a.val,hPA a.property⟩=f (X.oldPoint p) := Subtype.ext (ha.trans hComm)
    have hOld : (X.oldPoint p).val ∈ (P i).carrier := (congrArg Subtype.val (hinj hEq)) ▸ a.property
    exact ⟨⟨p.val,(X.mem_selectedPiece (P i) p.val).mpr ⟨p.property,hOld⟩⟩,hpoint⟩

def comp (h00 : M ⊨ Axioms.ACVF00) (hinj : Function.Injective f)
    (hPA : ∀ i,(P i).carrier ⊆ A.carrier)
    (F : VFReindexedChainLift (G := G) X f P)
    (H : VFReindexedChainLift (G := G) F.target g (fun i => (f.restrict (hPA i)).image)) :
    VFReindexedChainLift (G := G) X (g.comp f) P where
  target := H.target
  map := H.map.comp F.map
  chain := .comp _ (fun i => X.selectedPiece_subset (P i)) F.chain
    (H.chain.changePieces (fun i => (F.partition_image h00 hinj i (hPA i)).symm))
  commutes p := by
    have hMid : F.target.oldPoint (F.map p)=f (X.oldPoint p) := Subtype.ext (F.commutes p)
    exact (H.commutes (F.map p)).trans (congrArg (fun z : B => (g z).val) hMid)

def identity
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : VFReindexRefinementFrame A e) (P : I → DefSet (rawMixedSpace (M := M) n r) S)
    (hP : ∀ i,ProperInvariant S (P i).carrier) : VFReindexedChainLift (G := G) X (Map.id A) P where
  target := X
  map := Map.id X.data.base
  chain := .identity X.data.base X.data.proper _ (fun i => X.selectedPiece_subset (P i))
    (fun i => X.selectedPiece_properInvariant h00 hc hκ hs hv (P i) (hP i))
  commutes _ := rfl

def regularize
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (X : VFReindexRefinementFrame A e) (P : I → DefSet (rawMixedSpace (M := M) n r) S)
    (hP : ∀ i,ProperInvariant S (P i).carrier) : VFReindexedChainLift (G := G) X (regularization A) P where
  target := X.afterRegularization h00 hc hκ hs hv
  map := regularization X.data.base
  chain := .regularize X.data.base X.data.proper X.data.doublyBounded _ (fun i => X.selectedPiece_subset (P i))
    (fun i => X.selectedPiece_properInvariant h00 hc hκ hs hv (P i) (hP i))
    (fun i => X.selectedPiece_doublyBounded (P i))
  commutes p := by
    apply Prod.ext
    · rfl
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · change (DiamondIntegral.Section6.regularize p.val).2
        ((regularizedLabelSelection n X.data.labels ∘ regularizedVFPermutationLabels e) (Fin.castAdd r j))=
        (DiamondIntegral.Section6.regularize (X.oldPoint p).val).2 (Fin.castAdd r j)
      simp only [regularizedLabelSelection,
        regularizedVFPermutationLabels,Function.comp_apply,Fin.addCases_left,
        DiamondIntegral.Section6.regularize,Fin.append_left,VFReindexRefinementFrame.oldPoint,
        RVRefinementFrame.oldPoint,reindexVFPoint]
      rfl
    · change (DiamondIntegral.Section6.regularize p.val).2
        ((regularizedLabelSelection n X.data.labels ∘ regularizedVFPermutationLabels e) (Fin.natAdd n j))=
        (DiamondIntegral.Section6.regularize (X.oldPoint p).val).2 (Fin.natAdd n j)
      simp only [regularizedLabelSelection,
        regularizedVFPermutationLabels,Function.comp_apply,Fin.addCases_right,
        DiamondIntegral.Section6.regularize,Fin.append_right,VFReindexRefinementFrame.oldPoint,
        RVRefinementFrame.oldPoint,reindexVFPoint]

end VFReindexedChainLift
end DiamondIntegral.Section6
