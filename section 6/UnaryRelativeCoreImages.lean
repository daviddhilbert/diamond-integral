import «section 6».UnaryRelativeApertureHomeomorphism
import «section 6».CoreBranchImages

/-! The actual newly frozen component of a variable unary step is a
complete RV-pullback. Its source membership, branch tag, definable image,
proper invariance and bounds are retained, rather than postulated as a
core-preparation certificate. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6.UnaryRelativeApertureData
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {r : ℕ} {S : Set M}
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}

def coreImage (D : UnaryRelativeApertureData A) :
    DefSet (rawMixedSpace (M := M) 1 (1+r)) S :=
  rvTagSlice D.map.image (Fin.castAdd r (0 : Fin 1)) true

theorem mem_coreImage (D : UnaryRelativeApertureData A) (h00 : M ⊨ Axioms.ACVF00)
    (z : Mixed M 1 (1+r)) : z ∈ D.coreImage.carrier ↔
      ∃ p,p ∈ A.carrier ∧ D.core p=true ∧ D.point p=z := by
  constructor
  · rintro ⟨⟨p,hp⟩,hflag⟩
    change D.point p.val=z at hp
    have hh := congrArg (fun z : Mixed M 1 (1+r) => z.2 (Fin.castAdd r (0 : Fin 1))) hp
    simp only [point,Fin.append_left] at hh
    exact ⟨p.val,p.property,branchTag_injective h00 (hh.trans hflag),hp⟩
  · rintro ⟨p,hp,hcore,rfl⟩
    refine ⟨⟨⟨p,hp⟩,rfl⟩,?_⟩
    simp only [point,Fin.append_left,hcore]

theorem coreImage_rvPullback (D : UnaryRelativeApertureData A) (h00 : M ⊨ Axioms.ACVF00) :
    IsRVPullback D.coreImage.carrier := by
  apply Set.Subset.antisymm _ (subset_rvHull _)
  intro z hz
  obtain ⟨p,hp,hVF,hRV⟩ := (mem_rvHull_iff D.coreImage.carrier z).mp hz
  obtain ⟨a,ha,hcore,rfl⟩ := (D.mem_coreImage h00 p).mp hp
  have hu : a.2 ∈ D.focusData.activeTags.carrier := by
    by_contra hn
    exact Bool.noConfusion ((D.core_inactive (p := a) hn).symm.trans hcore)
  let p : focusActive A D.focusData.activeTags := ⟨a,ha,hu⟩
  have hy : rv M (z.1 0)=rv M (D.endpoint a.2) := by
    have h := congrFun hVF 0
    change rv M ((D.point a).1 0)=rv M (z.1 0) at h
    exact h.symm.trans (D.core_output_RV p hcore)
  obtain ⟨b,hTags,hbCore,hbValue⟩ := D.core_image_full_RV_disc p hcore (z.1 0) hy
  change b.val.2=a.2 at hTags
  apply (D.mem_coreImage h00 z).mpr
  refine ⟨b.val,b.property.1,hbCore,Prod.ext ?_ ?_⟩
  · funext i
    fin_cases i
    exact hbValue
  · calc
      (D.point b.val).2=Fin.append (fun _ : Fin 1 => branchTag (M := M) true) a.2 := by
        simp only [point,hbCore,hTags]
      _=(D.point a).2 := by simp only [point,hcore]
      _=z.2 := hRV

theorem coreImage_subset (D : UnaryRelativeApertureData A) :
    D.coreImage.carrier ⊆ D.map.image.carrier := fun _ h => h.1

theorem coreImage_doublyBounded (D : UnaryRelativeApertureData A)
    (hc : CanonicalStructure.IsCanonical (M := M)) {κ : Cardinal} (hs : Saturated M κ)
    (hsmall : Cardinal.mk S < κ) : VFDoublyBounded D.coreImage.carrier := by
  obtain ⟨γ,hγ⟩ := D.image_vfDoublyBounded hc hs hsmall
  exact ⟨γ,fun p hp => hγ p (D.coreImage_subset hp)⟩

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem coreImage_properInvariant (D : UnaryRelativeApertureData A)
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (hsmall : Cardinal.mk S < κ) : ProperInvariant S D.coreImage.carrier :=
  rvTagSlice_properInvariant _ _ _ (D.image_properInvariant h00 hc hκ hs hv hsmall)

end DiamondIntegral.Section6.UnaryRelativeApertureData
