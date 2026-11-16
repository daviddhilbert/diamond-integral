import «section 6».RelativeAffineTailData

/-! An affine tail with equal inactive centres is literally relatively
unary when its head VF coordinates are fixed. Full measured derivatives
hold off a whole-label set smaller than the positive head degree. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section7 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M G : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF]
variable [LinearOrderedCommGroupWithZero G] [Valued (VF M) G] {S : Set M} {k m : ℕ}

theorem affineTailSlopesForHead_eq_one_of_inactive
    (a b : Fin m → VF M) (j l : Fin m) (hl : l ≠ j) (ha : a l ≠ 0) (hb : b l=a l) (D c : VF M) :
    affineTailSlopesForHead Valued.v a b j D c l=1 := by
  unfold affineTailSlopesForHead
  split_ifs
  · rw [affineTailSlopes_eq_of_ne a b j _ hl,hb,div_self ha]
  · change b l / a l=1
    rw [hb,div_self ha]

theorem exists_relative_affine_lift_small_head_exception
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ) (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S,∅⟩ : ParameterBase M))
    (hv : ∀ x y : VF M,VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    {U V : MeasuredRVObject (M := M) S ((k+1)+m)} (e : MeasuredRVIso U V)
    (hU : (rvHeadVolume U.object (productLeft (k+1) m)).FiniteFibres)
    (hV : (rvHeadVolume V.object (productLeft (k+1) m)).FiniteFibres)
    (F : EverywhereMeasuredRVLift (measuredRVHeadIso hc e
      (productLeft (k+1) m) (productLeft (k+1) m) hU hV))
    (hFixed : ∀ p,(F.map p).val.1=p.val.1)
    (T : FullAffineTailData (G := G) hc e hU hV F) (j : Fin m)
    (hInactive : ∀ p l,l ≠ j → (T.b p).val l=(T.a p).val l) :
    ∃ f : Map (rvLift U.object) (rvLift V.object),Function.Bijective f ∧
      VFUnaryRelativeAt f (productRight (k+1) m j) ∧
      (∀ p,e.iso.hom.map.graph p.val.2 (f p).val.2) ∧
      ∃ E : DefSet (rawRVSpace (M := M) U.object.arity) S,
        E.carrier ⊆ U.object.domain.carrier ∧ rvDim E < k+1 ∧
          ∀ p : rvLift U.object,p.val.2 ∉ E.carrier →
            ∃ L,HasMixedVFDerivativeAt f p L ∧ vfValue (LinearMap.toMatrix' L).det=
              (gammaMapValue U.form (liftLabelMap _ p) / gammaMapValue V.form (liftLabelMap _ (f p))).val := by
  obtain ⟨f,hf,heq,E,hE,hDim,hGood⟩ := exists_affineLift_small_head_exception h00 hc hκ hs hsmall hΓ hv
    U V hU hV F.map F.bijective (fun p => ⟨(F.measure p).choose,(F.measure p).choose_spec.1⟩)
    T.a T.b T.D T.c j T.a_nonzero T.b_nonzero T.a_rv T.b_rv
  let H := rvLiftHeadSelect ⟨U.object,U.finiteVolume⟩ (productLeft (k+1) m) hU
  let s (p) := affineTailSlopesForHead Valued.v (T.a p).val (T.b p).val j ((T.D p).val 0) ((T.c p).val 0)
  have hUnary : VFUnaryRelativeAt f (productRight (k+1) m j) := by
    intro p l hl
    have he := congrArg (fun z : (rawMixedSpace (M := M) ((k+1)+m) V.object.arity).Carrier => z.1 l) (heq p)
    rw [he]
    obtain ⟨q,rfl⟩ := (finSumFinEquiv : Fin (k+1) ⊕ Fin m ≃ Fin ((k+1)+m)).surjective l
    cases q with
    | inl q =>
      change productTuple (F.map (H p)).val.1
        (affineTail (T.a (H p)).val (T.b (H p)).val (s (H p))
          (p.val.1 ∘ productRight (k+1) m)) (productLeft (k+1) m q)=_
      rw [productTuple_left,hFixed]
      rfl
    | inr q =>
      have hq : q ≠ j := fun he => hl (congrArg (productRight (k+1) m) he)
      change productTuple (F.map (H p)).val.1
        (affineTail (T.a (H p)).val (T.b (H p)).val (s (H p))
          (p.val.1 ∘ productRight (k+1) m)) (productRight (k+1) m q)=_
      rw [productTuple_right]
      change (T.b (H p)).val q+s (H p) q*(p.val.1 (productRight (k+1) m q)-(T.a (H p)).val q)=_
      have hs : s (H p) q=1 := affineTailSlopesForHead_eq_one_of_inactive _ _ j q hq
        (T.a_nonzero (H p) q) (hInactive (H p) q hq) _ _
      rw [hs,hInactive (H p) q hq,one_mul,add_sub_cancel]
      rfl
  have hLabels (p) : e.iso.hom.map.graph p.val.2 (f p).val.2 := by
    obtain ⟨u,hu,hv⟩ := F.labels (H p)
    exact ⟨u,hu,hv.trans (congrArg Prod.snd (heq p)).symm⟩
  refine ⟨f,hf,hUnary,hLabels,E,hE,hDim,fun p hp => ?_⟩
  obtain ⟨L,hL⟩ := hGood p hp
  obtain ⟨D,hD,_⟩ := F.measure (H p)
  have hDet := det_affineLift_of_mixed_derivatives
    ⟨U.object,U.finiteVolume⟩ ⟨V.object,V.finiteVolume⟩ hU hV F.map f
    (fun x => (T.a x).val) (fun x => (T.b x).val) s
    (fun q => congrArg Prod.fst (heq q)) p D L hD hL
  have hC : (LinearMap.toMatrix' L).det=(T.c (H p)).val 0 := by
    rw [hDet,← T.head_det (H p) D hD]
    exact (affineTailSlopesForHead_spec Valued.v (T.a (H p)).val (T.b (H p)).val j
      ((T.D (H p)).val 0) ((T.c (H p)).val 0) (T.a_nonzero (H p)) (T.b_nonzero (H p))).2 (T.correction (H p))
  refine ⟨L,hL,?_⟩
  rw [hC,T.c_value,liftLabelMap_target_of_graph e.iso.hom.map f hLabels p]
  rfl

end DiamondIntegral.Section6
