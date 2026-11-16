import «section 6».UnaryRelativeMeasuredMatching

/-! Attach actual preliminary preparations to the completed unary
matching. The same final RV bijection and its measured identity survive
because the transported forms agree as actual original-base maps. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {r s a b : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S} {B : DefSet (rawMixedSpace (M := M) 1 s) S}
variable {A' : DefSet (rawMixedSpace (M := M) 1 a) S} {B' : DefSet (rawMixedSpace (M := M) 1 b) S}
variable {f : Map A B} {g : Map A' B'}
variable (α : Map A A') (β : Map B B')
variable (hα : UnaryRelativeApertureChain (G := G) A A' α)
variable (hβ : UnaryRelativeApertureChain (G := G) B B' β)
variable (hCommutes : ∀ p : A,g (α p)=β (f p))

def UnaryRelativePreparedMatching.precompose
    (H : UnaryRelativePreparedMatching (G := G) A' B' g) : UnaryRelativePreparedMatching (G := G) A B f where
  sourceArity := H.sourceArity
  targetArity := H.targetArity
  source := H.source
  target := H.target
  sourceMap := H.sourceMap.comp α
  targetMap := H.targetMap.comp β
  sourceChain := .comp hα H.sourceChain
  targetChain := .comp hβ H.targetChain
  sourceProper := H.sourceProper
  targetProper := H.targetProper
  sourceBounded := H.sourceBounded
  targetBounded := H.targetBounded
  sourcePullback := H.sourcePullback
  targetPullback := H.targetPullback
  sourceTagged := H.sourceTagged
  targetTagged := H.targetTagged
  map := H.map
  bijective := H.bijective
  commutes p := (H.commutes (α p)).trans (congrArg H.targetMap (hCommutes p))
  wholeFibres := H.wholeFibres

theorem UnaryRelativePreparedMatching.precompose_sourceForm
    (H : UnaryRelativePreparedMatching (G := G) A' B' g) (h00 : M ⊨ Axioms.ACVF00)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (ω' : Map A' (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hω : ∀ p : A,ω' (α p)=ω p) :
    (H.precompose α β hα hβ hCommutes).sourceForm h00 ω=H.sourceForm h00 ω' := by
  apply Map.ext
  intro p
  obtain ⟨q,rfl⟩ := (H.sourceChain.bijective h00).surjective p
  obtain ⟨p,rfl⟩ := (hα.bijective h00).surjective q
  have h := (H.precompose α β hα hβ hCommutes).sourceForm_transport h00 ω p
  change (H.precompose α β hα hβ hCommutes).sourceForm h00 ω (H.sourceMap (α p))=ω p at h
  rw [h,H.sourceForm_transport h00 ω' (α p)]
  exact (hω p).symm

theorem UnaryRelativePreparedMatching.precompose_targetForm
    (H : UnaryRelativePreparedMatching (G := G) A' B' g) (h00 : M ⊨ Axioms.ACVF00)
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (σ' : Map B' (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hσ : ∀ p : B,σ' (β p)=σ p) :
    (H.precompose α β hα hβ hCommutes).targetForm h00 σ=H.targetForm h00 σ' := by
  apply Map.ext
  intro p
  obtain ⟨q,rfl⟩ := (H.targetChain.bijective h00).surjective p
  obtain ⟨p,rfl⟩ := (hβ.bijective h00).surjective q
  have h := (H.precompose α β hα hβ hCommutes).targetForm_transport h00 σ p
  change (H.precompose α β hα hβ hCommutes).targetForm h00 σ (H.targetMap (β p))=σ p at h
  rw [h,H.targetForm_transport h00 σ' (β p)]
  exact (hσ p).symm

def UnaryRelativeMeasuredMatching.precompose (h00 : M ⊨ Axioms.ACVF00)
    (ω : Map A (DefSet.univ (rawGammaPresentation (M := M)) S))
    (σ : Map B (DefSet.univ (rawGammaPresentation (M := M)) S))
    (ω' : Map A' (DefSet.univ (rawGammaPresentation (M := M)) S))
    (σ' : Map B' (DefSet.univ (rawGammaPresentation (M := M)) S))
    (hω : ∀ p : A,ω' (α p)=ω p) (hσ : ∀ p : B,σ' (β p)=σ p)
    (H : UnaryRelativeMeasuredMatching (G := G) A' B' g h00 ω' σ') :
    UnaryRelativeMeasuredMatching (G := G) A B f h00 ω σ where
  geometry := H.geometry.precompose α β hα hβ hCommutes
  sourceIndex := H.sourceIndex
  targetIndex := H.targetIndex
  sourceLeading := H.sourceLeading
  targetLeading := H.targetLeading
  rv := by
    change PreparedUnaryRVMatching H.geometry.source H.geometry.target H.geometry.map
      (gammaFormExtension ((H.geometry.precompose α β hα hβ hCommutes).sourceForm h00 ω))
      (gammaFormExtension ((H.geometry.precompose α β hα hβ hCommutes).targetForm h00 σ)) H.sourceIndex H.targetIndex
    rw [H.geometry.precompose_sourceForm α β hα hβ hCommutes h00 ω ω' hω,
      H.geometry.precompose_targetForm α β hα hβ hCommutes h00 σ σ' hσ]
    exact H.rv

end DiamondIntegral.Section6
