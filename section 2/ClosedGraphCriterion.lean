import «section 2».ProjectiveGraphClosure
import «section 2».CorrespondenceImages
import «section 2».SmallVFGeneratedBase
import «section 2».AffineCurveSelection

/-! The geometric closed-graph criterion. Discontinuous maps produce a
finite-valued approaching curve and a different projective graph limit.
Temporary VF-generation is constructed from the actual defining data. -/

set_option backward.isDefEq.respectTransparency false
open FirstOrder FirstOrder.Language Filter Topology
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4
open SpecialTransformations.Section8 SpecialTransformations.Section9

namespace DiamondIntegral.Section2
variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {n m : ℕ}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem continuousWithinAt_iff_vfBalls
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (f : (Fin n → VF M) → Fin m → VF M) (A : Set (Fin n → VF M)) (a : Fin n → VF M) :
    ContinuousWithinAt f A a ↔
      ∀ ε : Gamma M, ∃ δ : Gamma M, ∀ x ∈ A, x ∈ vfBall a δ → f x ∈ vfBall (f a) ε := by
  constructor
  · exact fun h ε => continuousWithinAt_ball_estimate hv f A a h ε
  · intro h
    apply Filter.tendsto_def.mpr
    intro V hV
    obtain ⟨ε,hε⟩ := exists_vfBall_subset_nhds hv (f a) hV
    obtain ⟨δ,hδ⟩ := h ε
    apply Filter.mem_of_superset
      (Filter.inter_mem (mem_nhdsWithin_of_mem_nhds (vfBall_mem_nhds hv a δ)) self_mem_nhdsWithin)
    exact fun x hx => hε (hδ x hx.2 hx.1)

theorem ContinuousOn.projectiveGraphCluster_eq
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {A : Set (Fin n → VF M)} {f : (Fin n → VF M) → Fin m → VF M}
    (hf : ContinuousOn f A) {a : Fin n → VF M} (ha : a ∈ A)
    {b : Fin m → LimitPoint M} (hb : ProjectiveGraphCluster A f a b) :
    b = finiteLimitPoint (f a) := by
  by_contra hne
  obtain ⟨ε,hε⟩ := exists_disjoint_limitBall hne
  obtain ⟨δ,hδ⟩ := continuousWithinAt_ball_estimate hv f A a (hf a ha) ε
  obtain ⟨x,hx,hxa,hxb⟩ := hb ε δ
  exact Set.disjoint_left.mp hε hxb
    (by simpa only [limitBall_finite] using hδ x hx hxa)

theorem exists_projectiveGraphCluster_of_not_continuousWithinAt
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (A : Set (Fin n → VF M))
    (f : (Fin n → VF M) → Fin m → VF M)
    (hf : S.Definable LRV (vfCorrespondenceGraph A (fun x => {f x})))
    (a : Fin n → VF M) (hnot : ¬ ContinuousWithinAt f A a) :
    ∃ b : Fin m → LimitPoint M, b ≠ finiteLimitPoint (f a) ∧ ProjectiveGraphCluster A f a b := by
  classical
  rw [continuousWithinAt_iff_vfBalls hv f A a] at hnot
  push Not at hnot
  obtain ⟨ε,hε⟩ := hnot
  let D : Set (Fin n → VF M) := {x ∈ A | f x ∉ vfBall (f a) ε}
  have haD : a ∈ closure D := by
    apply mem_closure_iff_nhds.mpr
    intro U hU
    obtain ⟨δ,hδ⟩ := exists_vfBall_subset_nhds hv a hU
    obtain ⟨x,hx,hxa,hbad⟩ := hε δ
    exact ⟨x,hδ hxa,hx,hbad⟩
  have hD : (Set.univ : Set M).Definable LRV (vfValues '' D) := by
    simpa only [Set.mem_sdiff,Set.mem_univ,true_and] using
      vf_map_preimage_definable A f (hf.mono (Set.subset_univ _))
        (Set.univ \ vfBall (f a) ε)
        (vf_sdiff_definable Set.univ (vfBall (f a) ε) (vf_univ_definable Set.univ)
          (vfBall_definable_univ hc (f a) ε))
  obtain ⟨E,hsmall,hDE,hfE,B,x,hx0,hxv⟩ :=
    exists_small_vf_generated_base_for_two_definable hv hκ (vfValues '' D) hD
      (vfCorrespondenceGraph A (fun x => {f x})) (hf.mono (Set.subset_univ _))
  obtain ⟨C,hC,hCfin,hCvalues,hCcont,hClim⟩ := lemma_2_46_affine h00 hc hκ.le hs hv
    E.toSubstructure B ⟨x,hx0,ne_of_lt hxv⟩ hsmall D hDE a haD
  let T : Set M := (E : Set M) ∪ Set.range (vfValues a)
  have hT : Cardinal.mk T < κ := small_union_range hκ.le (E : Set M) hsmall (vfValues a)
  have hF : T.Definable LRV (vfCorrespondenceGraph curveSource (fun c => f '' C c)) :=
    vfCorrespondenceGraph_image_definable curveSource C hC A
      (fun c hcU y hy => ((hCvalues c hcU).2 hy).1) f (hfE.mono Set.subset_union_left)
  obtain ⟨L,hLf,hL,hLdef⟩ := SpecialTransformations.Section9.lemma_9_5 hc hs hT curveSource
    (fun c => f '' C c) hF (fun c _ => (hCfin c).image f)
  have hLne : L.Nonempty := by
    obtain ⟨δ,hδ⟩ := (isLimitSet_iff curveSource 0 (fun c => f '' C c) L).mp hL.1 1
    obtain ⟨c,hcU,hnear⟩ := curveSource_accumulates (M := M) δ
    obtain ⟨y,hy⟩ := (hCvalues c hcU.1).1
    obtain ⟨b,hb,_⟩ := hδ c hcU hnear (f y) ⟨y,hy,rfl⟩
    exact ⟨b,hb⟩
  obtain ⟨b,hb⟩ := hLne
  refine ⟨b,?_,?_⟩
  · intro he
    obtain ⟨c,hcU,hnear,z,⟨y,hy,rfl⟩,hzb⟩ := hL.frequently_hits hb ε 1
    have hybad := ((hCvalues c hcU.1).2 hy).2
    apply hybad
    simpa only [he,limitBall_finite] using hzb
  · intro η δ
    obtain ⟨ζ,hζ⟩ := hClim.1 δ
    obtain ⟨c,hcU,hnear,z,⟨y,hy,rfl⟩,hzb⟩ := hL.frequently_hits hb η ζ
    obtain ⟨q,hq,hyq⟩ := hζ c hcU hnear y hy
    have hqa : q = a := Set.mem_singleton_iff.mp hq
    exact ⟨y,((hCvalues c hcU.1).2 hy).1,hqa ▸ hyq,hzb⟩

theorem continuousOn_iff_relativeProjectiveGraph_isClosed
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {S : Set M} (A : Set (Fin n → VF M))
    (f : (Fin n → VF M) → Fin m → VF M)
    (hf : S.Definable LRV (vfCorrespondenceGraph A (fun x => {f x}))) :
    ContinuousOn f A ↔ IsClosed (relativeProjectiveGraph A f) := by
  rw [relativeProjectiveGraph_isClosed_iff hv A f]
  constructor
  · exact fun h a ha b hb => ContinuousOn.projectiveGraphCluster_eq hv h ha hb
  · intro h a ha
    by_contra hnot
    obtain ⟨b,hne,hb⟩ := exists_projectiveGraphCluster_of_not_continuousWithinAt
      h00 hc hκ hs hv A f hf a hnot
    exact hne (h a ha b hb)

end DiamondIntegral.Section2
