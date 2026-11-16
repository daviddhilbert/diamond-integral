import «section 6».PairedDiscImageGraphs

/-! Exact interpretation of the paired-disc formula in the actual VF
sort. Its four parameters specify the two centers and nonzero radius
representatives; no full-disc equality is replaced by pointwise data. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem rawOpenBall_iff_centeredGammaDisc (a r x : VF M) (hr : r ≠ 0) :
    x.val ∈ rawOpenBall a.val r.val ↔ x ∈ centeredGammaDisc a (finiteValue r hr) := by
  have h : x.val ∈ rawOpenBall a.val r.val ↔
      Values.vfValueHom r < Values.vfValueHom (x-a) :=
    (mem_rawOpenBall_iff Values.presentationValuation Values.presentation_compatible a r x hr).trans
      (lt_iff_not_ge.trans ((not_congr ((Values.presentation_compatible r (x-a)).symm.trans
        (Values.vf_pred_iff_gamma_le r (x-a)))).trans lt_iff_not_ge.symm))
  rw [mem_centeredGammaDisc]
  change x.val ∈ rawOpenBall a.val r.val ↔ vfValue r < vfValue (x-a)
  simpa only [valueHom_eq_value] using h

theorem pairedDiscImageCodes_at (A : Set (VF M)) (f : VF M → VF M)
    (a b r s : VF M) (hr : r ≠ 0) (hs : s ≠ 0) :
    ![a.val,b.val,r.val,s.val] ∈ pairedDiscImageCodes A f ↔
      a ∈ A ∧ f a = b ∧ centeredGammaDisc a (finiteValue r hr) ⊆ A ∧
        f '' centeredGammaDisc a (finiteValue r hr) = centeredGammaDisc b (finiteValue s hs) := by
  constructor
  · rintro ⟨hAnchor,hSelfA,hSelfB,hDom,hImage⟩
    obtain ⟨p,hp,hpa,hpb⟩ := hAnchor
    have hpa' : p = a := Subtype.ext hpa
    have hpb' : f a = b := by
      rw [hpa'] at hpb
      exact Subtype.ext hpb
    have hSource : centeredGammaDisc a (finiteValue r hr) ⊆ A := by
      intro x hx
      obtain ⟨y,hy,he⟩ := hDom (fun _ => x.val) ((rawOpenBall_iff_centeredGammaDisc a r x hr).mpr hx)
      exact (Subtype.ext he : y = x) ▸ hy
    refine ⟨hpa' ▸ hp,hpb',hSource,?_⟩
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      apply (rawOpenBall_iff_centeredGammaDisc b s (f x) hs).mp
      apply (hImage (fun _ => (f x).val)).mpr
      exact ⟨(fun _ => x.val),(rawOpenBall_iff_centeredGammaDisc a r x hr).mpr hx,
        x,hSource hx,rfl,rfl⟩
    · intro hy
      obtain ⟨x,hx,⟨p,hp,hpx,hpy⟩⟩ := (hImage (fun _ => y.val)).mp
        ((rawOpenBall_iff_centeredGammaDisc b s y hs).mpr hy)
      change p.val = x 0 at hpx
      change (f p).val = y.val at hpy
      change x 0 ∈ rawOpenBall a.val r.val at hx
      have hpDisc : p ∈ centeredGammaDisc a (finiteValue r hr) := by
        apply (rawOpenBall_iff_centeredGammaDisc a r p hr).mp
        simpa only [hpx] using hx
      exact ⟨p,hpDisc,Subtype.ext hpy⟩
  · rintro ⟨ha,hfa,hDom,hImage⟩
    refine ⟨⟨a,ha,rfl,congrArg Subtype.val hfa⟩,?_,?_,?_,?_⟩
    · exact (rawOpenBall_iff_centeredGammaDisc a r a hr).mpr (Set.mem_insert a _)
    · exact (rawOpenBall_iff_centeredGammaDisc b s b hs).mpr (Set.mem_insert b _)
    · intro x hx
      let p : VF M := ⟨x 0,hx.2.1⟩
      exact ⟨p,hDom ((rawOpenBall_iff_centeredGammaDisc a r p hr).mp hx),rfl⟩
    · intro y
      constructor
      · intro hy
        let q : VF M := ⟨y 0,hy.2.1⟩
        have hq := (rawOpenBall_iff_centeredGammaDisc b s q hs).mp hy
        obtain ⟨p,hp,he⟩ := hImage.symm ▸ hq
        refine ⟨(fun _ => p.val),(rawOpenBall_iff_centeredGammaDisc a r p hr).mpr hp,
          p,hDom hp,rfl,?_⟩
        exact congrArg Subtype.val he
      · rintro ⟨x,hx,⟨p,hp,hpx,hpy⟩⟩
        change p.val = x 0 at hpx
        change (f p).val = y 0 at hpy
        change x 0 ∈ rawOpenBall a.val r.val at hx
        have hpDisc : p ∈ centeredGammaDisc a (finiteValue r hr) := by
          apply (rawOpenBall_iff_centeredGammaDisc a r p hr).mp
          simpa only [hpx] using hx
        have hTarget : f p ∈ centeredGammaDisc b (finiteValue s hs) := hImage ▸ Set.mem_image_of_mem f hpDisc
        have hRaw := (rawOpenBall_iff_centeredGammaDisc b s (f p) hs).mpr hTarget
        change y 0 ∈ rawOpenBall b.val s.val
        exact hpy ▸ hRaw

end DiamondIntegral.Section6
