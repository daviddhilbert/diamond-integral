import «section 6».RVLabelCovariance

/-! The actual coordinate-forgetting map used after an RV contraction.
All old RV tags and the original parameter base are retained. Projection
preserves proper invariance and proper covariance directly, without an
additional compactness or uniform-radius hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

theorem Congruent.init {α : Fin (n+1) → Gamma M} {a b : Fin (n+1) → VF M}
    (h : Congruent α a b) : Congruent (Fin.init α) (Fin.init a) (Fin.init b) :=
  fun i => h i.castSucc

theorem Congruent.snoc {α : Fin (n+1) → Gamma M} {a b : Fin n → VF M}
    (h : Congruent (Fin.init α) a b) (c : VF M) :
    Congruent α (Fin.snoc a c) (Fin.snoc b c) := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using (Congruent.refl α (Fin.snoc a c) (Fin.last n))
  · simpa only [Fin.snoc_castSucc,Fin.init] using h j

theorem AlphaInvariant.image_init {α : Fin (n+1) → Gamma M}
    {H : Set (Fin (n+1) → VF M)} (h : AlphaInvariant α H) :
    AlphaInvariant (Fin.init α) (Fin.init '' H) := by
  intro a b hab
  constructor
  · rintro ⟨x,hx,hxa⟩
    refine ⟨Fin.snoc b (x (Fin.last n)),?_,by simp⟩
    have hxb : Congruent α x (Fin.snoc b (x (Fin.last n))) := by
      conv_lhs => rw [← Fin.snoc_init_self x]
      exact (hxa ▸ hab).snoc _
    exact (h x _ hxb).mp hx
  · rintro ⟨y,hy,hyb⟩
    refine ⟨Fin.snoc a (y (Fin.last n)),?_,by simp⟩
    have hya : Congruent α y (Fin.snoc a (y (Fin.last n))) := by
      conv_lhs => rw [← Fin.snoc_init_self y]
      exact (hyb ▸ hab.symm).snoc _
    exact (h y _ hya).mp hy

def vfDropLast (A : DefSet (rawMixedSpace (M := M) (n+1) r) S) :
    Map A (DefSet.univ (rawMixedSpace (M := M) n r) S) := by
  let P := rawMixedSpace (M := M) (n+1) r
  let Q := rawMixedSpace (M := M) n r
  let F (p : Mixed M (n+1) r) : Mixed M n r := (Fin.init p.1,p.2)
  let codes (z : Fin (n+1) ⊕ Fin r → M) : Fin n ⊕ Fin r → M :=
    Sum.elim (fun i => z (.inl i.castSucc)) (z ∘ Sum.inr)
  have hd : S.DefinableMap LRV codes := by
    rintro (i | i) <;> exact Set.DefinableFun.proj LRV
  have hdom (c : P.domain) : codes c.val ∈ Q.domain := by
    obtain ⟨a,ha⟩ := c.property.1
    refine ⟨⟨Fin.init a,?_⟩,c.property.2⟩
    funext i
    exact congrFun ha i.castSucc
  refine Map.ofCodes A F codes hd hdom ?_
  intro c
  apply mixedValues_injective
  have h := mixedValues_decode ⟨codes c.val,hdom c⟩
  refine h.trans ?_
  funext i
  cases i with
  | inl i => exact (congrFun (mixedValues_decode c) (.inl i.castSucc)).symm
  | inr i => exact (congrFun (mixedValues_decode c) (.inr i)).symm

variable {A : DefSet (rawMixedSpace (M := M) (n+1) r) S}

theorem vfDropLast_apply (p : A) : (vfDropLast A p).val = (Fin.init p.val.1,p.val.2) := rfl

theorem vfDropLast_image_fibre (u : Fin r → RVInfinity M) :
    vfFibre (vfDropLast A).image.carrier u = Fin.init '' vfFibre A.carrier u := by
  ext b
  constructor
  · rintro ⟨p,hp⟩
    have hu : p.val.2 = u := congrArg Prod.snd hp
    exact ⟨p.val.1,hu ▸ p.property,congrArg Prod.fst hp⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨⟨(a,u),ha⟩,rfl⟩

theorem vfDropLast_image_vfBounded (hA : VFBounded A.carrier) :
    VFBounded (vfDropLast A).image.carrier := by
  obtain ⟨γ,hγ⟩ := hA
  refine ⟨γ,?_⟩
  rintro _ ⟨p,rfl⟩ i
  exact hγ p.val p.property i.castSucc

theorem vfDropLast_image_rvBounded (hA : RVSupportDoublyBounded A.carrier) :
    RVSupportDoublyBounded (vfDropLast A).image.carrier := by
  obtain ⟨γ,hγ⟩ := hA
  refine ⟨γ,?_⟩
  rintro _ ⟨p,rfl⟩ i
  exact hγ p.val p.property i

theorem vfDropLast_image_properInvariant (hA : ProperInvariant S A.carrier) :
    ProperInvariant S (vfDropLast A).image.carrier := by
  refine ⟨(vfDropLast A).image.definable,vfDropLast_image_vfBounded hA.vfBounded,
    vfDropLast_image_rvBounded hA.rvBounded,fun u => ?_⟩
  obtain ⟨α,hα,hInv⟩ := hA.radii u
  refine ⟨Fin.init α,fun i => hα i.castSucc,?_⟩
  rw [vfDropLast_image_fibre]
  exact hInv.image_init

theorem vfDropLast_graph_iff (u v : Fin r → RVInfinity M)
    (a : Fin (n+1) → VF M) (b : Fin n → VF M) :
    graphFibre (vfDropLast A).toImage u v a b ↔
      (a,u) ∈ A.carrier ∧ Fin.init a = b ∧ u = v := by
  constructor
  · rintro ⟨p,hp,hfp⟩
    refine ⟨hp ▸ p.property,?_,?_⟩
    · exact (congrArg (fun z : Mixed M (n+1) r => Fin.init z.1) hp).symm.trans
        (congrArg Prod.fst hfp)
    · exact (congrArg Prod.snd hp).symm.trans (congrArg Prod.snd hfp)
  · rintro ⟨ha,hab,huv⟩
    exact ⟨⟨(a,u),ha⟩,rfl,Prod.ext hab huv⟩

theorem vfDropLast_graphSource (u v : Fin r → RVInfinity M) :
    graphFibreSource (vfDropLast A).toImage u v =
      {a | a ∈ vfFibre A.carrier u ∧ u = v} := by
  ext a
  simp only [graphFibreSource,Set.mem_ofPred_eq,vfDropLast_graph_iff]
  exact ⟨fun ⟨_,ha,_,huv⟩ => ⟨ha,huv⟩,fun ⟨ha,huv⟩ => ⟨Fin.init a,ha,rfl,huv⟩⟩

theorem vfDropLast_graphRange (u v : Fin r → RVInfinity M) :
    graphFibreRange (vfDropLast A).toImage u v =
      {b | b ∈ Fin.init '' vfFibre A.carrier u ∧ u = v} := by
  ext b
  simp only [graphFibreRange,Set.mem_ofPred_eq,vfDropLast_graph_iff]
  exact ⟨fun ⟨a,ha,hab,huv⟩ => ⟨⟨a,ha,hab⟩,huv⟩,
    fun ⟨⟨a,ha,hab⟩,huv⟩ => ⟨a,ha,hab,huv⟩⟩

theorem vfDropLast_graphMap (u v : Fin r → RVInfinity M) :
    Set.EqOn (graphFibreMap (vfDropLast A).toImage u v) Fin.init
      (graphFibreSource (vfDropLast A).toImage u v) := by
  intro a ha
  exact ((vfDropLast_graph_iff u v a _).mp
    (graphFibreMap_graph (vfDropLast A).toImage u v ha)).2.1.symm

theorem vfDropLast_properCovariant (hA : ProperInvariant S A.carrier) :
    ProperCovariant (vfDropLast A).toImage := by
  refine ⟨hA.vfBounded,vfDropLast_image_vfBounded hA.vfBounded,
    hA.rvBounded,vfDropLast_image_rvBounded hA.rvBounded,fun u v => ?_⟩
  obtain ⟨α,hα,hInv⟩ := hA.radii u
  have hn : NamedGammaTuple (graphFibreBase S u v) α :=
    fun i => (hα i).mono Set.subset_union_left
  refine ⟨α,Fin.init α,hn,fun i => hn i.castSucc,?_,?_,?_⟩
  · rw [vfDropLast_graphSource]
    intro a b hab
    exact and_congr (hInv a b hab) Iff.rfl
  · rw [vfDropLast_graphRange]
    intro a b hab
    exact and_congr (hInv.image_init a b hab) Iff.rfl
  · intro a ha b hb hab
    rw [vfDropLast_graphMap u v ha,vfDropLast_graphMap u v hb]
    exact hab.init

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem vfDropLast_continuous : ContinuousOnGraphFibres (vfDropLast A).toImage := by
  intro u v
  exact (show Continuous (Fin.init : (Fin (n+1) → VF M) → Fin n → VF M) from
    continuous_pi (fun i => continuous_apply i.castSucc)).continuousOn.congr (vfDropLast_graphMap u v)

end DiamondIntegral.Section6
