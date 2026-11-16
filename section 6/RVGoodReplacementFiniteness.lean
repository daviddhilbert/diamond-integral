import «section 6».FiniteVolumeImageCriterion

/-! Replacing the last volume coordinate by a target coordinate has
finite fibres outside the constructed inverse obstacles. The proof
uses finitely many actual old volume values and the given old volume
fibres; no new finite-fibre condition is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem rvGoodReplacementMap_finite {U V : RVObject (M := M) S (n+1)}
    (F : RVHom U V) (j : Fin (n+1)) (E : RawClosure.Tuple.GoodRelation (n := n) S)
    (hUF : U.volume.FiniteFibres)
    (hObs : ∀ (t : Fin n → M) (y : M), (t,y) ∉ E.val →
      {x | (Fin.snoc t x,y) ∈ rvCoordinateRelation F j}.Finite) :
    ((rvLastReplacementMap F j).restrict (rvGoodReplacementDomain_subset F j E)).FiniteFibres := by
  let D := rvGoodReplacementDomain F j E
  let hD := rvGoodReplacementDomain_subset F j E
  let ι (u : D) : U.domain := ⟨u.val,hD u.property⟩
  let f := U.volume.restrict hD
  let g := (rvLastReplacementMap F j).restrict hD
  apply finite_fibres_of_finite_volume_images f g (hUF.restrict hD)
  intro v
  let B : Set D := {u | g u = v}
  by_cases hne : B.Nonempty
  · obtain ⟨u₀,hu₀⟩ := hne
    have hPoint (u : D) (hu : u ∈ B) :
        Fin.init (U.value (ι u)) = Fin.init v.val ∧ V.value (F.map (ι u)) j = v.val (Fin.last n) := by
      have h := congrArg Subtype.val hu
      change (rvLastReplacementMap F j (ι u)).val = v.val at h
      rw [rvLastReplacementMap_value] at h
      exact ⟨by simpa only [Fin.init_snoc] using congrArg Fin.init h,
        by simpa only [Fin.snoc_last] using congrFun h (Fin.last n)⟩
    let t := rvValues (Fin.init v.val)
    let y := (v.val (Fin.last n)).val
    have hNot : (t,y) ∉ E.val := by
      have h := (rvGoodReplacementDomain_mem F j E (ι u₀)).mp u₀.property
      have hpre : Fin.init (rvValues (U.value (ι u₀))) = t :=
        congrArg (fun z : Fin n → RVInfinity M => rvValues z) (hPoint u₀ hu₀).1
      rw [hpre,(hPoint u₀ hu₀).2] at h
      exact h
    have hX := hObs t y hNot
    let T := (fun u : D => U.value (ι u)) '' B
    have hT : T.Finite := by
      apply finite_rv_tuples_of_fixed_prefix T (Fin.init v.val)
      · rintro s ⟨u,hu,rfl⟩
        exact (hPoint u hu).1
      · apply hX.subset
        rintro x ⟨s,⟨u,hu,hs⟩,hx⟩
        subst s
        refine ⟨ι u,?_,?_⟩
        · funext i
          refine Fin.lastCases ?_ (fun k => ?_) i
          · simpa only [rvValues,Fin.snoc_last] using hx
          · simpa only [t,rvValues,Fin.snoc_castSucc,Fin.init] using congrArg Subtype.val (congrFun (hPoint u hu).1 k)
        · exact congrArg Subtype.val (hPoint u hu).2
    apply Set.Finite.of_finite_image (f :=
      (Subtype.val : DefSet.univ (rawRVSpace (M := M) (n+1)) S → Fin (n+1) → RVInfinity M)) ?_
      Subtype.val_injective.injOn
    rw [Set.image_image]
    exact hT
  · have he : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    change (f '' B).Finite
    rw [he,Set.image_empty]
    exact Set.finite_empty

end DiamondIntegral.Section6
