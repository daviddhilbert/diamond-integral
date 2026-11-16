import «section 6».PreparedCoreComplements

/-! Globally prepared cores occupy whole final RV-label branches.
Within those branches the boundary step preserves exactly the old-label
equivalence, and the complement is a literal complementary branch. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n r s : ℕ}

theorem restricted_image_mem_iff
    {A C : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (hf : Function.Injective f) (hCA : C.carrier ⊆ A.carrier) (a : A) :
    (f a).val ∈ (f.restrict hCA).image.carrier ↔ a.val ∈ C.carrier := by
  constructor
  · rintro ⟨c,hc⟩
    have hEq : (⟨c.val,hCA c.property⟩ : A)=a := hf (Subtype.ext hc)
    exact (congrArg Subtype.val hEq) ▸ c.property
  · intro hC
    exact ⟨⟨a.val,hC⟩,rfl⟩

theorem prepared_subset_source_labels_iff
    {A C : DefSet (rawMixedSpace (M := M) n r) S} {B : DefSet (rawMixedSpace (M := M) n s) S}
    (f : Map A B) (hf : Function.Injective f) (hCA : C.carrier ⊆ A.carrier)
    (hCore : IsRVPullback (f.restrict hCA).image.carrier)
    (hTag : ∀ p ∈ B.carrier,∀ q ∈ B.carrier,p.2=q.2 → tupleRV M p.1=tupleRV M q.1) (a : A) :
    a.val ∈ C.carrier ↔ (f a).val.2 ∈ (locusTags B (f.restrict hCA).image).carrier :=
  (restricted_image_mem_iff f hf hCA a).symm.trans
    (locus_iff_tags B (f.restrict hCA).image hCore hTag (f a).property)

variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable {A : DefSet (rawMixedSpace (M := M) 1 r) S}
variable (F : UnaryFocusData A) (d : (Fin r → RVInfinity M) → VF M)
variable (dMap : Map (focusActive A F.activeTags) (DefSet.univ (rawVFSpace (M := M) 1) S))
variable (hdMap : ∀ p : focusActive A F.activeTags,(dMap p).val 0=d p.val.2)
variable (E : CentripetalData (G := G) A)
variable (hCoord : E.coordinate=0) (hActive : E.activeTags=F.activeTags)
variable (hFocus : ∀ x u,E.focus x u=F.focus u-d u)
variable (hCore : ∀ p ∈ (F.offsetCoreDomain dMap).carrier,E.core p=false)
variable (hRV : IsRVPullback A.carrier)
variable (hCenters : ∀ u ∈ F.activeTags.carrier,((fun _ : Fin 1 => F.focus u),u) ∈ A.carrier)
variable (hd : ∀ u ∈ F.activeTags.carrier,d u ≠ 0)
variable (hSmall : ∀ u ∈ F.activeTags.carrier,vfValue (F.focus u) < vfValue (d u))

include hdMap hCoord hActive hFocus hCore hRV hCenters hd hSmall in
theorem ambient_boundary_core_image_tagged :
    ∀ p ∈ (E.bijection.restrict (F.offsetCoreDomain_subset dMap)).image.carrier,
      ∀ q ∈ (E.bijection.restrict (F.offsetCoreDomain_subset dMap)).image.carrier,
        p.2=q.2 → tupleRV M p.1=tupleRV M q.1 := by
  have hImage := F.ambient_boundary_core_image d dMap hdMap E hCoord hActive hFocus hCore hRV hCenters hd hSmall
  intro p hp q hq hTags
  rw [hImage] at hp hq
  obtain ⟨u,hu,hpu,hpRV⟩ := hp
  obtain ⟨v,hv,hqv,hqRV⟩ := hq
  have huv : u=v := by
    funext i
    have hh := congrFun (hpu.symm.trans (hTags.trans hqv)) (Fin.natAdd 1 i)
    simpa only [Fin.append_right] using hh
  funext i
  fin_cases i
  exact hpRV.trans ((congrArg (fun t => rv M (d t)) huv).trans hqRV.symm)

include hdMap hCoord hActive hFocus hCore hRV hCenters hd hSmall in
theorem ambient_boundary_core_labels_iff (h00 : M ⊨ Axioms.ACVF00)
    (p q : F.offsetCoreDomain dMap) :
    ((centripetalStepMap E) ⟨p.val,F.offsetCoreDomain_subset dMap p.property⟩).val.2=
      ((centripetalStepMap E) ⟨q.val,F.offsetCoreDomain_subset dMap q.property⟩).val.2 ↔ p.val.2=q.val.2 := by
  constructor
  · exact fun h => (E.coordinate_step_same_labels h00 _ _ h).1
  · intro hTags
    let p' : A := ⟨p.val,F.offsetCoreDomain_subset dMap p.property⟩
    let q' : A := ⟨q.val,F.offsetCoreDomain_subset dMap q.property⟩
    have hComponentTags : (E.bijection p').val.2=(E.bijection q').val.2 := by
      change (E.point p.val).2=(E.point q.val).2
      simp only [CentripetalData.point,hCore p.val p.property,hCore q.val q.property,hTags]
    have hVF := ambient_boundary_core_image_tagged F d dMap hdMap E hCoord hActive hFocus hCore hRV hCenters hd hSmall
      (E.bijection p').val ⟨p,rfl⟩ (E.bijection q').val ⟨q,rfl⟩ hComponentTags
    change Fin.append (tupleRV M (E.point p.val).1) (E.point p.val).2=
      Fin.append (tupleRV M (E.point q.val).1) (E.point q.val).2
    change tupleRV M (E.point p.val).1=tupleRV M (E.point q.val).1 at hVF
    change (E.point p.val).2=(E.point q.val).2 at hComponentTags
    rw [hVF,hComponentTags]

end DiamondIntegral.Section6
