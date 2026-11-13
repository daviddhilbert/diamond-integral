import «section 3».IntegrationCoordinatePartition
import «section 3».IntegrationOrdinaryFibres
import «section 3».IntegrationZeroRefinement
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer SpecialTransformations.Section3
open IntegrationInACVF.Section3 IntegrationInACVF.Section3ACVF
noncomputable section
namespace DiamondIntegral.Section3
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]

/-- Native mixed-coordinate partition, with every original RV label and
Gamma parameter retained. The four zero cells make both directions ordinary. -/
theorem integrationDiscToDiscPartition {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (hs : Saturated M κ) (B : GammaParameters.Base (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    (hΓ : Section2.NontrivialDefinableGamma B) {r s : ℕ}
    (A : Set (Section2.Mixed M 1 r)) (f : Section2.Mixed M 1 r → Section2.Mixed M 1 s)
    (hf : Section2.MixedMapDefinable B A f) (hinj : Set.InjOn f A) :
    Section2.DiscToDiscPartition B A f := by
  obtain ⟨δ,hδ,hδ1⟩ := integrationPositiveGamma_of_nontrivial B hΓ
  let Araw := Section2.mixedTuple '' A
  let F := integrationMixedRawMap A f
  let i := integrationMixedVFIndex r
  let j := integrationMixedVFIndex s
  have hF := integrationMixedRawGraph_definable B A f hf
  have hinjF := integrationMixedRawMap_injOn A f hinj
  have hsrc : ∀ a ∈ ({i} : Set (Fin (1+r))), ∀ x ∈ Araw, iVF (x a) := by
    intro a ha x hx
    have ha' : a = i := Set.mem_singleton_iff.mp ha
    subst a
    obtain ⟨p,hp,rfl⟩ := hx
    rw [integrationMixedVFCoordinate]
    exact (p.1 0).property
  have htar : ∀ b ∈ ({j} : Set (Fin (1+s))), ∀ x ∈ Araw, iVF (F x b) := by
    intro b hb x hx
    have hb' : b = j := Set.mem_singleton_iff.mp hb
    subst b
    obtain ⟨p,hp,rfl⟩ := hx
    dsimp only [F]
    rw [integrationMixedRawMap_on A f p hp,integrationMixedVFCoordinate]
    exact ((f p).1 0).property
  obtain ⟨P,hP,hDis,hCov⟩ := integrationFullCoordinatePartition hκ hs (integrationGammaBase B)
    h00 δ hδ hδ1 Araw F hF hinjF {i} {j} hsrc htar
  let θ := {W // W ∈ P} × Bool × Bool
  let e : Fin (Fintype.card θ) ≃ θ := (Fintype.equivFin θ).symm
  let R (a : θ) : Set (Fin (1+r) → M) := integrationRawZeroPiece Araw F i j a.1.val a.2.1 a.2.2
  let Q (a : θ) : Set (Section2.Mixed M 1 r) := Section2.mixedTuple ⁻¹' R a
  have hRW (a : θ) : R a ⊆ a.1.val := fun _ hx => hx.1.1
  have hRA (a : θ) : R a ⊆ Araw := (hRW a).trans (hP a.1.val a.1.property).2.1
  have hQA (a : θ) : Q a ⊆ A := by
    intro x hx
    obtain ⟨y,hy,he⟩ := hRA a hx
    exact integrationMixedTuple_injective he ▸ hy
  have hImage (a : θ) : Section2.mixedTuple '' Q a = R a := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hx
    · intro z hz
      obtain ⟨x,hx,rfl⟩ := hRA a hz
      exact ⟨x,hz,rfl⟩
  refine ⟨Fintype.card θ,fun n => Q (e n),?_,?_,?_⟩
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hx
      exact hQA (e n) hn
    · intro x hx
      have hxraw : Section2.mixedTuple x ∈ Araw := ⟨x,hx,rfl⟩
      obtain ⟨W,hWP,hxW⟩ := (Set.ext_iff.mp hCov (Section2.mixedTuple x)).mp hxraw
      have hbex : ∃ b, Section2.mixedTuple x ∈ integrationTruthCell {z | z i = iVFZero} b :=
        ⟨_,integrationTruthCell_mem _ _⟩
      have hcex : ∃ c, Section2.mixedTuple x ∈ integrationTruthCell {z | z ∈ Araw ∧ F z j = iVFZero} c :=
        ⟨_,integrationTruthCell_mem _ _⟩
      obtain ⟨b,hb⟩ := hbex
      obtain ⟨c,hc⟩ := hcex
      let a : θ := (⟨W,hWP⟩,b,c)
      apply Set.mem_iUnion.mpr
      refine ⟨e.symm a,?_⟩
      rw [Equiv.apply_symm_apply]
      exact ⟨⟨hxW,hb⟩,hc⟩
  · intro m n hmn
    apply Set.disjoint_left.mpr
    intro x hxm hxn
    have hW : (e m).1 = (e n).1 := by
      apply Subtype.ext
      by_contra hne
      exact (Set.disjoint_left.mp (hDis (e m).1.property (e n).1.property hne)
        (hRW (e m) hxm) (hRW (e n) hxn)).elim
    have hb : (e m).2.1 = (e n).2.1 := integrationTruthCell_unique hxm.1.2 hxn.1.2
    have hc : (e m).2.2 = (e n).2.2 := integrationTruthCell_unique hxm.2 hxn.2
    exact hmn (e.injective (Prod.ext hW (Prod.ext hb hc)))
  · intro n
    let a := e n
    have hRDef := integrationRawZeroPiece_definable (integrationGammaBase B) Araw F hF i j
      a.1.val (hP a.1.val a.1.property).2.2.1 a.2.1 a.2.2
    have hproper : ∀ z ∈ R a, ∀ k, sortEval (Section2.mixedSort 1 r k) (z k) := by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := hRA a hz
      exact integrationMixedTuple_sorted x
    have hQDef : Section2.MixedDefinable B (Q a) := by
      change GammaParameters.DefinableOverBase B _ (Section2.mixedTuple '' Q a)
      rw [hImage a]
      exact (integrationGammaDefinable_iff hproper).mpr hRDef
    refine ⟨hQDef,?_⟩
    have hPaper := integrationMixedPaperFibres_of_coordinate A f (hRA a)
      (CoordinateOpenToOpen.at_mono (hRW a) F i j ((hP a.1.val a.1.property).2.2.2 i rfl j rfl))
    apply integrationHasDiscToDisc_of_paper h00 δ hδ1 (Q a) f (hinj.mono (hQA a)) hPaper
    · cases hb : a.2.1 with
      | false =>
        apply Or.inr
        intro x hx he
        have hn : Section2.mixedTuple x i ≠ iVFZero := by
          simpa only [integrationTruthCell,hb,Bool.false_eq_true,↓reduceIte,Set.mem_compl_iff,Set.mem_ofPred_eq] using hx.1.2
        apply hn
        rw [integrationMixedVFCoordinate,he]
        rfl
      | true =>
        apply Or.inl
        intro x hx
        have he : Section2.mixedTuple x i = iVFZero := by
          simpa only [integrationTruthCell,hb,↓reduceIte,Set.mem_ofPred_eq] using hx.1.2
        exact Subtype.ext he
    · cases hc : a.2.2 with
      | false =>
        apply Or.inr
        intro x hx he
        have hn : ¬ (Section2.mixedTuple x ∈ Araw ∧ F (Section2.mixedTuple x) j = iVFZero) := by
          simpa only [integrationTruthCell,hc,Bool.false_eq_true,↓reduceIte,Set.mem_compl_iff,Set.mem_ofPred_eq] using hx.2
        apply hn
        refine ⟨hRA a hx,?_⟩
        dsimp only [F]
        rw [integrationMixedRawMap_on A f x (hQA a hx),integrationMixedVFCoordinate,he]
        rfl
      | true =>
        apply Or.inl
        intro x hx
        have he : Section2.mixedTuple x ∈ Araw ∧ F (Section2.mixedTuple x) j = iVFZero := by
          simpa only [integrationTruthCell,hc,↓reduceIte,Set.mem_ofPred_eq] using hx.2
        have hz := he.2
        dsimp only [F] at hz
        rw [integrationMixedRawMap_on A f x (hQA a hx),integrationMixedVFCoordinate] at hz
        exact Subtype.ext hz
end DiamondIntegral.Section3
