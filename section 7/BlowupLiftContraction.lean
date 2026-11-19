import «section 7».BlowupLiftImage
import «section 6».DiamondSpecialIsomorphisms
import «section 6».BoundedVariableUnaryMatching
import «section 6».PreparedRVObjects
import «section 6».UnaryPullbackPreservation
import «section 6».DiamondLiftHomomorphism
import «section 7».LiftClasses

/-! The contraction of the regularized image (Lemma 7.12, `blowup:same:RV:coa`).

The regularized image `V` of the lift of an elementary blowup is tagged (its
labels record the leading terms), an RV pullback, finite over each VF point,
and doubly bounded. The source form, transported along the centripetal
transformation and the regularization, depends only on the labels. Section 6's
contraction therefore gives a doubly bounded measured RV object `W` whose lift
is `V`. Remark 6.15 turns the chain (relative aperture data, then
regularization) into an isomorphism of `μVF^◇[1+k]` from the lift of the
source chart onto the lift of `W`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3
open SpecialTransformations.Section3.GammaParameters
open SpecialTransformations.Section4 DiamondIntegral.Section2 SpecialTransformations.DefinableGeometry
open SpecialTransformations.Section9 (liftLabelMap)

namespace DiamondIntegral.Section7.BlowupLiftContraction
open DiamondIntegral.Section4
open DiamondIntegral.Section4.RVMeasuredCharts DiamondIntegral.Section4.FiniteTupleBlocks
open AnnularBlowup BlowupChart RelativeAnnularGenerators
open DiamondIntegral.Section7.BoundedClasses DiamondIntegral.Section7.RVMaps
open DiamondIntegral.Section7.StrictCharts DiamondIntegral.Section7.MeasuredRVBridge
open DiamondIntegral.Section7.BlowupLiftData DiamondIntegral.Section7.BlowupLiftImage
open DiamondIntegral.Section6 DiamondIntegral.Section6.DiamondLift DiamondIntegral.Section6.DiamondCategory

variable {M : Type} [LRV.Structure M] [hM : M ⊨ Axioms.ACVF] {S : Set M} {k : ℕ}

section Contraction
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]
variable (hc : CanonicalStructure.IsCanonical (M := M))
variable (D : AnnularDatum (⟨S, ∅⟩ : Base (M := M)) k)
variable (L : TupleFinitaryLift (centreRelation D))
variable (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
variable (hU : (toMeasured hc D.chart).doublyBounded)
variable (hP : ProperInvariant S (liftSet hc D).carrier)
variable (Δ : Values.Gamma (M := M))
variable (hΔ : S.Definable LRV {z : Fin 1 → M | z 0 ∈ Values.gammaPullback {Δ}})
variable (hΔ1 : 1 ≤ Δ) (hΔb : ∀ u ∈ D.chart.domain, codeValue (D.aperture.aperture u) ≤ Δ)

local notation "𝓡" => apertureData (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb
local notation "𝓥" => Vreg (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb

theorem vreg_tagged :
    ∀ p ∈ (𝓥).carrier, ∀ q ∈ (𝓥).carrier, p.2 = q.2 → tupleRV M p.1 = tupleRV M q.1 := by
  intro p hp q hq he
  apply rvValues_injective
  rw [((mem_Vreg_iff hc D L hv hU hP Δ hΔ hΔ1 hΔb p).mp hp).2,
    ((mem_Vreg_iff hc D L hv hU hP Δ hΔ hΔ1 hΔb q).mp hq).2, he]

theorem vreg_pullback : IsRVPullback (𝓥).carrier := by
  show rvHull _ = _
  apply Set.Subset.antisymm
  · intro q hq
    obtain ⟨p, hp, h1, h2⟩ := (mem_rvHull_iff _ q).mp hq
    have h := (mem_Vreg_iff hc D L hv hU hP Δ hΔ hΔ1 hΔb p).mp hp
    apply (mem_Vreg_iff hc D L hv hU hP Δ hΔ hΔ1 hΔb q).mpr
    rw [← h1, ← h2]
    exact h
  · intro q hq
    exact (mem_rvHull_iff _ q).mpr ⟨q, hq, rfl, rfl⟩

theorem hd_off {w : Fin (labN D) → M} (hw : w ∈ Icore D ∪ Ishell D) :
    ∀ l ≠ D.coordinate, hd D w l = D.chart.coordinate (lb D w) l := by
  intro l hl
  rcases hw with h | h
  · rw [((mem_Icore_iff D w).mp h).2.2, blownCoordinate, Function.update_of_ne hl]
  · exact ((mem_Ishell_iff_lead D w).mp h).2.2.1 l hl

theorem vreg_finite (a : Fin (1 + k) → VF M) :
    {t : Fin (labN D) → RVInfinity M | (a, t) ∈ (𝓥).carrier}.Finite := by
  let h0 := rvValues (tupleRV M a)
  let F : Set (Fin D.chart.arity → M) := {v | v ∈ D.chart.domain ∧
    AnnularBlowup.inactive D.chart D.coordinate v = Function.update h0 D.coordinate iRVOne}
  have hF : F.Finite := D.finite _
  have hT : ((F ×ˢ ({minusOne, iRVOne} : Set M)).image (fun z => mk D h0 z.2 z.1)).Finite :=
    (hF.prod (Set.toFinite _)).image _
  refine (hT.preimage rvValues_injective.injOn).subset ?_
  intro t ht
  obtain ⟨hw, hhd⟩ := (mem_Vreg_iff hc D L hv hU hP Δ hΔ hΔ1 hΔb (a, t)).mp ht
  have hl : lb D (rvValues t) ∈ D.chart.domain := by
    rcases hw with h | h
    · exact ((mem_Icore_iff D _).mp h).1
    · exact ((mem_Ishell_iff D _).mp h).1
  refine ⟨(lb D (rvValues t), tg D (rvValues t)), ⟨⟨hl, ?_⟩, ?_⟩, ?_⟩
  · funext l
    by_cases hl' : l = D.coordinate
    · subst hl'
      simp only [AnnularBlowup.inactive, Function.update_self]
    · simp only [AnnularBlowup.inactive, Function.update_of_ne hl']
      rw [← hd_off D hw l hl']
      exact (congrFun hhd l).symm
  · rcases hw with h | h
    · exact Or.inl ((mem_Icore_iff D _).mp h).2.1
    · exact Or.inr ((mem_Ishell_iff D _).mp h).2.1
  · change mk D h0 (tg D (rvValues t)) (lb D (rvValues t)) = rvValues t
    have hh : h0 = hd D (rvValues t) := hhd
    rw [hh, mk_recon]

theorem vreg_vfDoublyBounded : VFDoublyBounded (𝓥).carrier := by
  obtain ⟨γ, hγ⟩ := (𝓡).image_vfDoublyBounded
  refine ⟨γ, fun p hp i => ?_⟩
  rw [regularization_carrier] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  exact hγ q hq i

theorem vreg_rvDoublyBounded : RVSupportDoublyBounded (𝓥).carrier := by
  obtain ⟨γ, hγ⟩ := (𝓡).image_vfDoublyBounded
  obtain ⟨δ, hδ⟩ := (𝓡).image_rvDoublyBounded
  have h1 : ((max γ δ)⁻¹).val ≤ (γ⁻¹).val := show (max γ δ)⁻¹ ≤ γ⁻¹ from inv_le_inv' (le_max_left _ _)
  have h2 : ((max γ δ)⁻¹).val ≤ (δ⁻¹).val := show (max γ δ)⁻¹ ≤ δ⁻¹ from inv_le_inv' (le_max_right _ _)
  have h3 : γ.val ≤ (max γ δ).val := show γ ≤ max γ δ from le_max_left _ _
  have h4 : δ.val ≤ (max γ δ).val := show δ ≤ max γ δ from le_max_right _ _
  refine ⟨max γ δ, fun p hp i => ?_⟩
  rw [regularization_carrier] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · change ((max γ δ)⁻¹).val ≤ Values.vrv (Fin.append (tupleRV M q.1) q.2 (Fin.castAdd _ i)) ∧
      Values.vrv (Fin.append (tupleRV M q.1) q.2 (Fin.castAdd _ i)) ≤ (max γ δ).val
    rw [Fin.append_left]
    obtain ⟨hl, hu⟩ := hγ q hq i
    exact ⟨h1.trans hl, hu.trans h3⟩
  · change ((max γ δ)⁻¹).val ≤ Values.vrv (Fin.append (tupleRV M q.1) q.2 (Fin.natAdd _ i)) ∧
      Values.vrv (Fin.append (tupleRV M q.1) q.2 (Fin.natAdd _ i)) ≤ (max γ δ).val
    rw [Fin.append_right]
    obtain ⟨hl, hu⟩ := hδ q hq i
    exact ⟨h2.trans hl, hu.trans h4⟩

/-- The centripetal transformation followed by the regularization. -/
def Fmap : Map (liftSet hc D) (𝓥) := (regularization (𝓡).map.image).comp (𝓡).bijection

theorem Fmap_bijective (h00 : M ⊨ Axioms.ACVF00) :
    Function.Bijective (Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb) :=
  (regularization_bijective _).comp ((𝓡).bijective h00)

theorem Fmap_val (a : liftSet hc D) :
    (Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb a).val = regularize ((𝓡).point a.val) := rfl

theorem Fmap_labels (a : liftSet hc D) (i : Fin D.chart.arity) :
    (Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb a).val.2 (Fin.natAdd (1 + k) (Fin.natAdd 1 i)) = a.val.2 i := by
  rw [Fmap_val]
  simp only [regularize, RelativeApertureData.point, Fin.append_right]

/-- The source form transported to the regularized image. -/
def form (h00 : M ⊨ Axioms.ACVF00) : Map (𝓥) (DefSet.univ (rawGammaPresentation (M := M)) S) :=
  (liftForm (toMeasured hc D.chart)).comp
    ((Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).inverse (Fmap_bijective hc D L hv hU hP Δ hΔ hΔ1 hΔb h00))

theorem form_labels (h00 : M ⊨ Axioms.ACVF00) (p q : 𝓥) (he : p.val.2 = q.val.2) :
    form hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 p = form hc D L hv hU hP Δ hΔ hΔ1 hΔb h00 q := by
  have hF := Fmap_bijective hc D L hv hU hP Δ hΔ hΔ1 hΔb h00
  have hp := Map.apply_inverse (Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb) hF p
  have hq := Map.apply_inverse (Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb) hF q
  have hl : ((Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).inverse hF p).val.2 =
      ((Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).inverse hF q).val.2 := by
    funext i
    rw [← Fmap_labels hc D L hv hU hP Δ hΔ hΔ1 hΔb _ i, ← Fmap_labels hc D L hv hU hP Δ hΔ hΔ1 hΔb _ i, hp, hq, he]
  change (toMeasured hc D.chart).form (liftLabelMap _ ((Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).inverse hF p)) =
    (toMeasured hc D.chart).form (liftLabelMap _ ((Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).inverse hF q))
  congr 1
  exact Subtype.ext hl

/-- The contraction `W` of the regularized image. -/
def W (h00 : M ⊨ Axioms.ACVF00) : MeasuredRVObject (M := M) S (1 + k) :=
  contractedMeasuredRVObject (𝓥) (vreg_tagged hc D L hv hU hP Δ hΔ hΔ1 hΔb)
    (vreg_pullback hc D L hv hU hP Δ hΔ hΔ1 hΔb) (vreg_finite hc D L hv hU hP Δ hΔ hΔ1 hΔb)
    (vreg_vfDoublyBounded hc D L hv hU hP Δ hΔ hΔ1 hΔb) (form hc D L hv hU hP Δ hΔ hΔ1 hΔb h00)
    (form_labels hc D L hv hU hP Δ hΔ hΔ1 hΔb h00)

theorem W_doublyBounded (h00 : M ⊨ Axioms.ACVF00) : (W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).doublyBounded :=
  contractedMeasuredRVObject_doublyBounded _ _ _ _ _ (vreg_rvDoublyBounded hc D L hv hU hP Δ hΔ hΔ1 hΔb) _ _

theorem W_lift_carrier (h00 : M ⊨ Axioms.ACVF00) :
    (rvLift (W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).object).carrier = (𝓥).carrier :=
  preparedRVObject_lift_carrier _ (vreg_pullback hc D L hv hU hP Δ hΔ hΔ1 hΔb)
    (vreg_tagged hc D L hv hU hP Δ hΔ hΔ1 hΔb)

/-- The lift of the source chart is isomorphic in `μVF^◇[1+k]` to the lift of
the contraction `W`. -/
theorem lift_isomorphic (h00 : M ⊨ Axioms.ACVF00) {κ : Cardinal} (hκ : Cardinal.aleph0 < κ)
    (hs : Saturated M κ) (hsmall : Cardinal.mk S < κ)
    (hΓ : NontrivialDefinableGamma (⟨S, ∅⟩ : ParameterBase M)) :
    Isomorphic G (liftObject (toMeasured hc D.chart) hP)
      (liftObject (W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00)
        (measuredRVLift_properInvariant h00 hc hκ hs hv _ (W_doublyBounded hc D L hv hU hP Δ hΔ hΔ1 hΔb h00))) := by
  have hsub : (𝓥).carrier ⊆ (rvLift (W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).object).carrier :=
    fun p hp => (W_lift_carrier hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).symm ▸ hp
  let F' : Map (liftSet hc D) (rvLift (W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).object) :=
    (Map.inclusion hsub).comp (Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb)
  have hchain : RelativeApertureChain (G := G) (liftSet hc D) (𝓥) (Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb) :=
    RelativeApertureChain.comp (RelativeApertureChain.relative _ (𝓡))
      (RelativeApertureChain.original (SpecialCovariantChain.regularize _
        ((𝓡).image_properInvariant h00 hc hκ hs hv) (𝓡).image_vfDoublyBounded))
  have H : RelativeApertureChain (G := G) (liftSet hc D) (rvLift (W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).object) F' :=
    RelativeApertureChain.changeTarget (DefSet.eq_of_carrier_eq (W_lift_carrier hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).symm)
      (fun _ => rfl) hchain
  refine DiamondSpecialIsomorphisms.remark_6_15 h00 hc DiamondIntegral.Section7.LiftClasses.lin hκ hs hv hsmall hΓ
    (A := liftObject (toMeasured hc D.chart) hP) F' H (DefSet.empty _ S) (Or.inr rfl) (fun p _ => ?_)
  have hl : liftLabelMap (W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).object (F' p) =
      pureRVTagQuotient (𝓥) (Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb p) := Subtype.ext rfl
  change gammaMapValue (liftForm (toMeasured hc D.chart)) p =
    gammaMapValue (W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).form (liftLabelMap _ (F' p))
  rw [hl, show gammaMapValue (W hc D L hv hU hP Δ hΔ hΔ1 hΔb h00).form
      (pureRVTagQuotient (𝓥) (Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb p)) =
      gammaMapValue (form hc D L hv hU hP Δ hΔ hΔ1 hΔb h00) (Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb p) from
    contractedMeasuredRVObject_form _ _ _ _ _ _ _ _]
  change _ = gammaMapValue (liftForm (toMeasured hc D.chart))
    ((Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb).inverse _ (Fmap (G := G) hc D L hv hU hP Δ hΔ hΔ1 hΔb p))
  rw [Map.inverse_apply]

end Contraction

end DiamondIntegral.Section7.BlowupLiftContraction
