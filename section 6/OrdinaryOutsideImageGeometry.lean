import «section 6».OrdinaryCenteredCoreImages

/-! Removing sufficiently small cores at ordinary zero-event centers
leaves an ordinary endpoint that is still an RV-pullback. The full
complement image is the target minus the union of the full core images. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S R : Set M} {r s : ℕ}
variable {A : SpecialTransformations.Section5.DefSet (M := M) R 1 r}
variable {B : SpecialTransformations.Section5.DefSet (M := M) R 1 s}

def ordinarySourceCoreUnion (E : Set A) (ρ : A → Gamma M) : Set (Mixed M 1 r) :=
  {x | x ∈ SpecialTransformations.Section5.carrier A ∧ ∃ p ∈ E,
    x.1 0 ∈ centeredGammaDisc (p.val.1 0) (ρ p) ∧ x.2=p.val.2}

def ordinaryTargetCoreUnion (T : SpecialTransformations.Section5.Chain R 1 A B) (E : Set A) (ρ : A → Gamma M) :
    Set (Mixed M 1 s) := {q | ∃ p ∈ E,q ∈ ordinaryCenteredCoreImage T p (ρ p)}

def ordinaryOutsideCoreImage (T : SpecialTransformations.Section5.Chain R 1 A B) (E : Set A) (ρ : A → Gamma M) :
    Set (Mixed M 1 s) := {q | ∃ a : A,a.val ∉ ordinarySourceCoreUnion E ρ ∧ (T.toMap a).val=q}

theorem ordinary_outside_core_image_eq
    (T : SpecialTransformations.Section5.Chain R 1 A B) (E : Set A) (ρ : A → Gamma M) :
    ordinaryOutsideCoreImage T E ρ=SpecialTransformations.Section5.carrier B \ ordinaryTargetCoreUnion T E ρ := by
  ext q
  constructor
  · rintro ⟨a,haOut,haMap⟩
    refine ⟨haMap ▸ (T.toMap a).property,?_⟩
    rintro ⟨p,hp,b,hbDisc,hbTags,hbMap⟩
    have hba : b=a := T.bijective.injective (Subtype.ext (hbMap.trans haMap.symm))
    rw [hba] at hbDisc hbTags
    exact haOut ⟨a.property,p,hp,hbDisc,hbTags⟩
  · rintro ⟨hqB,hqOut⟩
    obtain ⟨a,ha⟩ := T.bijective.surjective ⟨q,hqB⟩
    have haMap : (T.toMap a).val=q := congrArg Subtype.val ha
    refine ⟨a,?_,haMap⟩
    rintro ⟨haA,p,hp,haDisc,haTags⟩
    exact hqOut ⟨p,hp,a,haDisc,haTags,haMap⟩

theorem ordinary_target_core_union_rvPullback
    (T : SpecialTransformations.Section5.Chain R 1 A B) (E : Set A) (ρ : A → Gamma M)
    (hCores : ∀ p ∈ E,IsRVPullback (ordinaryCenteredCoreImage T p (ρ p))) :
    IsRVPullback (ordinaryTargetCoreUnion T E ρ) := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨z,⟨p,hp,hz⟩,hVF,hRV⟩ := (mem_rvHull_iff (ordinaryTargetCoreUnion T E ρ) q).mp hq
  exact ⟨p,hp,rvPullback_mem_of_sameRV (hCores p hp) hz hVF hRV⟩

theorem ordinary_outside_core_image_rvPullback
    (T : SpecialTransformations.Section5.Chain R 1 A B) (E : Set A) (ρ : A → Gamma M)
    (hB : IsRVPullback (SpecialTransformations.Section5.carrier B))
    (hCores : ∀ p ∈ E,IsRVPullback (ordinaryCenteredCoreImage T p (ρ p))) :
    IsRVPullback (ordinaryOutsideCoreImage T E ρ) := by
  rw [ordinary_outside_core_image_eq]
  have hUnion := ordinary_target_core_union_rvPullback T E ρ hCores
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro q hq
  obtain ⟨z,hz,hVF,hRV⟩ := (mem_rvHull_iff
    (SpecialTransformations.Section5.carrier B \ ordinaryTargetCoreUnion T E ρ) q).mp hq
  exact ⟨rvPullback_mem_of_sameRV hB hz.1 hVF hRV,
    fun hqUnion => hz.2 (rvPullback_mem_of_sameRV hUnion hqUnion hVF.symm hRV.symm)⟩

theorem finite_ordinary_zero_event_cores_leave_rvPullback_image
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ)
    (T : SpecialTransformations.Section5.Chain R 1 A B)
    (hT : SpecialTransformations.Section5.GammaChainDefinable (ordinaryNamedGammaBase S) T)
    (hB : IsRVPullback (SpecialTransformations.Section5.carrier B))
    (E : Set A) (hFinite : E.Finite) (hE : ∀ p ∈ E,p.val ∈ ordinaryChainZeroSources T) :
    ∃ η : Gamma M,1 ≤ η ∧ ∀ ρ : A → Gamma M,(∀ p ∈ E,η ≤ ρ p) →
      IsRVPullback (ordinaryOutsideCoreImage T E ρ) := by
  have hLocal (p : A) (hp : p ∈ E) := ordinary_centered_zero_event_core_images_rvPullback hc hs hsmall T hT hB p (hE p hp)
  let cutoff (p : A) : Gamma M := if hp : p ∈ E then (hLocal p hp).choose else 1
  obtain ⟨b,hb⟩ := (hFinite.image cutoff).bddAbove
  refine ⟨max b 1,le_max_right _ _,fun ρ hρ => ordinary_outside_core_image_rvPullback T E ρ hB ?_⟩
  intro p hp
  have hCut : (hLocal p hp).choose ≤ ρ p := by
    have hh := hb (Set.mem_image_of_mem cutoff hp)
    have hpb : (hLocal p hp).choose ≤ b := by simpa only [cutoff,dif_pos hp] using hh
    exact hpb.trans ((le_max_left _ _).trans (hρ p hp))
  exact (hLocal p hp).choose_spec.2 (ρ p) hCut

end DiamondIntegral.Section6
