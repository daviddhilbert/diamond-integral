import «section 6».CoordinateUnitVolumes
import «section 6».FiniteRVReplacementBounds

/-! Actual finite-volume intermediate objects for changing tail RV
coordinates one at a time. The unchanged finite head proves finite
volume without any finite-label assumption. Forms retain total weight. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {k m : ℕ}

def tailReplacementIndices (k : ℕ) (J : Finset (Fin m)) : Finset (Fin (k+m)) := J.image (productRight k m)

theorem head_not_mem_tailReplacementIndices (J : Finset (Fin m)) (i : Fin k) :
    productLeft k m i ∉ tailReplacementIndices k J := by
  rintro h
  obtain ⟨j,_,he⟩ := Finset.mem_image.mp h
  exact productLeft_ne_right i j he.symm

theorem tail_mem_tailReplacementIndices (J : Finset (Fin m)) (j : Fin m) :
    productRight k m j ∈ tailReplacementIndices k J ↔ j ∈ J := by
  exact Finset.mem_image.trans (by simp only [(productRight k m).injective.eq_iff,exists_eq_right])

def rvTailReplacement (U : RVObject (M := M) S (k+m))
    (Δ : Map U.domain (DefSet.univ (rawRVSpace (M := M) (k+m)) S)) (J : Finset (Fin m)) :=
  rvPartialReplacement U Δ (tailReplacementIndices k J)

theorem rvTailReplacement_head (U : RVObject (M := M) S (k+m))
    (Δ : Map U.domain (DefSet.univ (rawRVSpace (M := M) (k+m)) S)) (J : Finset (Fin m))
    (u : U.domain) (i : Fin k) : (rvTailReplacement U Δ J).value u (productLeft k m i)=U.value u (productLeft k m i) := by
  unfold rvTailReplacement
  rw [rvPartialReplacement_value,if_neg (head_not_mem_tailReplacementIndices J i)]

theorem rvTailReplacement_tail (U : RVObject (M := M) S (k+m))
    (Δ : Map U.domain (DefSet.univ (rawRVSpace (M := M) (k+m)) S)) (J : Finset (Fin m))
    (u : U.domain) (j : Fin m) : (rvTailReplacement U Δ J).value u (productRight k m j)=
      if j ∈ J then (Δ u).val (productRight k m j) else U.value u (productRight k m j) := by
  unfold rvTailReplacement
  rw [rvPartialReplacement_value]
  simp only [tail_mem_tailReplacementIndices]

theorem rvTailReplacement_finiteVolume (U : RVObject (M := M) S (k+m))
    (Δ : Map U.domain (DefSet.univ (rawRVSpace (M := M) (k+m)) S))
    (hU : (rvHeadVolume U (productLeft k m)).FiniteFibres) (J : Finset (Fin m)) :
    (rvTailReplacement U Δ J).volume.FiniteFibres := by
  apply finiteFibres_of_value_reflection (rvHeadVolume U (productLeft k m)) _ hU
  intro u w he
  apply Subtype.ext
  funext i
  change U.value u (productLeft k m i)=U.value w (productLeft k m i)
  have h := congrArg (fun z : DefSet.univ (rawRVSpace (M := M) (k+m)) S => z.val (productLeft k m i)) he
  change (rvTailReplacement U Δ J).value u (productLeft k m i)=
    (rvTailReplacement U Δ J).value w (productLeft k m i) at h
  rwa [rvTailReplacement_head,rvTailReplacement_head] at h

def measuredRVTailReplacement (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S (k+m)} (e : MeasuredRVIso U V)
    (hU : (rvHeadVolume U.object (productLeft k m)).FiniteFibres) (J : Finset (Fin m)) :=
  U.withVolume hc (rvTailReplacement U.object (V.object.volume.comp e.iso.hom.map) J).volume
    (rvTailReplacement_finiteVolume U.object _ hU J)
    (rvPartialReplacement_nonzero U.object _ _ U.nonzero (fun u => V.nonzero (e.iso.hom.map u)))

theorem measuredRVTailReplacement_head (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S (k+m)} (e : MeasuredRVIso U V)
    (hU : (rvHeadVolume U.object (productLeft k m)).FiniteFibres) (J : Finset (Fin m))
    (u : U.object.domain) (i : Fin k) :
    (measuredRVTailReplacement hc e hU J).object.value u (productLeft k m i)=U.object.value u (productLeft k m i) :=
  rvTailReplacement_head U.object _ J u i

theorem measuredRVTailReplacement_tail (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S (k+m)} (e : MeasuredRVIso U V)
    (hU : (rvHeadVolume U.object (productLeft k m)).FiniteFibres) (J : Finset (Fin m))
    (u : U.object.domain) (j : Fin m) :
    (measuredRVTailReplacement hc e hU J).object.value u (productRight k m j)=
      if j ∈ J then V.object.value (e.iso.hom.map u) (productRight k m j) else U.object.value u (productRight k m j) :=
  rvTailReplacement_tail U.object _ J u j

theorem measuredRVTailReplacement_totalWeight (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S (k+m)} (e : MeasuredRVIso U V)
    (hU : (rvHeadVolume U.object (productLeft k m)).FiniteFibres) (J : Finset (Fin m)) (u : U.object.domain) :
    (measuredRVTailReplacement hc e hU J).totalWeight u=U.totalWeight u :=
  U.withVolume_totalWeight hc _ _ _ u

theorem measuredRVTailReplacement_headFinite (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S (k+m)} (e : MeasuredRVIso U V)
    (hU : (rvHeadVolume U.object (productLeft k m)).FiniteFibres) (J : Finset (Fin m)) :
    (rvHeadVolume (measuredRVTailReplacement hc e hU J).object (productLeft k m)).FiniteFibres := by
  have he : rvHeadVolume (measuredRVTailReplacement hc e hU J).object (productLeft k m)=
      rvHeadVolume U.object (productLeft k m) := by
    apply Map.ext
    intro u
    apply Subtype.ext
    funext i
    exact measuredRVTailReplacement_head hc e hU J u i
  rw [he]
  exact hU

theorem measuredRVTailReplacement_doublyBounded (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S (k+m)} (e : MeasuredRVIso U V)
    (hU : (rvHeadVolume U.object (productLeft k m)).FiniteFibres) (J : Finset (Fin m))
    (hUB : U.doublyBounded) (hVB : V.doublyBounded) : (measuredRVTailReplacement hc e hU J).doublyBounded :=
  rvPartialReplacement_doublyBounded e.iso.hom.map _ hUB hVB

def measuredRVTailReplacementStep (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S (k+m)} (e : MeasuredRVIso U V)
    (hU : (rvHeadVolume U.object (productLeft k m)).FiniteFibres) (J : Finset (Fin m)) (j : Fin m) :
    MeasuredRVIso (measuredRVTailReplacement hc e hU J) (measuredRVTailReplacement hc e hU (insert j J)) where
  iso := rvIsoOfFiniteVolumeNonzero (Map.id U.object.domain) Function.bijective_id
    (measuredRVTailReplacement hc e hU J).finiteVolume (measuredRVTailReplacement hc e hU (insert j J)).finiteVolume
    (measuredRVTailReplacement hc e hU J).nonzero (measuredRVTailReplacement hc e hU (insert j J)).nonzero
  balance u := (measuredRVTailReplacement_totalWeight hc e hU J u).trans
    (measuredRVTailReplacement_totalWeight hc e hU (insert j J) u).symm

theorem measuredRVTailReplacementStep_unary (hc : CanonicalStructure.IsCanonical (M := M))
    {U V : MeasuredRVObject (M := M) S (k+m)} (e : MeasuredRVIso U V)
    (hU : (rvHeadVolume U.object (productLeft k m)).FiniteFibres) (J : Finset (Fin m)) (j : Fin m) :
    RVUnaryRelativeAt (measuredRVTailReplacementStep hc e hU J j).iso.hom.map (productRight k m j) := by
  intro u l hl
  obtain ⟨q,rfl⟩ := (finSumFinEquiv : Fin k ⊕ Fin m ≃ Fin (k+m)).surjective l
  cases q with
  | inl q =>
    change (measuredRVTailReplacement hc e hU (insert j J)).object.value u (productLeft k m q)=
      (measuredRVTailReplacement hc e hU J).object.value u (productLeft k m q)
    rw [measuredRVTailReplacement_head,measuredRVTailReplacement_head]
  | inr q =>
    have hq : q ≠ j := fun he => hl (congrArg (productRight k m) he)
    change (measuredRVTailReplacement hc e hU (insert j J)).object.value u (productRight k m q)=
      (measuredRVTailReplacement hc e hU J).object.value u (productRight k m q)
    rw [measuredRVTailReplacement_tail,measuredRVTailReplacement_tail]
    simp only [Finset.mem_insert,hq,false_or]

end DiamondIntegral.Section6
