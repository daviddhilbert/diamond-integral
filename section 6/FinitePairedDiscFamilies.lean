import «section 6».PairedDiscImageGeometry

/-! Finite original-base families of genuine paired-disc radii over a
finite algebraic center graph. Choice is made over the full VF center
pair and retains the complete graph; individual centers are not named. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Milestone0.Transfer
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section8 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

def pairedRadiusFamily (A : Set (VF M)) (f : VF M → VF M) (q : Fin 2 → VF M) :
    Set (Fin 2 → VF M) := {r | ![(q 0).val,(q 1).val,(r 0).val,(r 1).val] ∈ pairedDiscImageCodes A f}

theorem pairedRadiusFamily_graph_definable
    (A : Set (VF M)) (f : VF M → VF M) (hGraph : S.Definable LRV (scalarPartialGraph A f))
    (C : Set (Fin 2 → VF M)) (hC : S.Definable LRV (vfValues '' C)) :
    S.Definable LRV (vfCorrespondenceGraph C (pairedRadiusFamily A f)) := by
  let idx : Fin 4 → Fin 2 ⊕ Fin 2 := ![.inl 0,.inl 1,.inr 0,.inr 1]
  have hPair := (pairedDiscImageCodes_definable A f hGraph).preimage_comp idx
  have hSource := hC.preimage_comp (Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2)
  have hOut := (vfRawUniverse_definable S 2).preimage_comp (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2)
  convert (hSource.inter hOut).inter hPair using 1
  ext z
  constructor
  · rintro ⟨q,hq,r,hr,he⟩
    have hQ : vfValues q = z ∘ Sum.inl := funext (fun i => congrFun he (.inl i))
    have hR : vfValues r = z ∘ Sum.inr := funext (fun i => congrFun he (.inr i))
    refine ⟨⟨⟨q,hq,hQ⟩,fun i => ?_⟩,?_⟩
    · change iVF (z (.inr i))
      have hi : (r i).val = z (.inr i) := congrFun hR i
      rw [← hi]
      exact (r i).property
    · have hp : ![(q 0).val,(q 1).val,(r 0).val,(r 1).val] = z ∘ idx := by
        funext i
        fin_cases i
        · exact congrFun hQ 0
        · exact congrFun hQ 1
        · exact congrFun hR 0
        · exact congrFun hR 1
      change z ∘ idx ∈ pairedDiscImageCodes A f
      rw [← hp]
      exact hr
  · rintro ⟨⟨⟨q,hq,hQ⟩,hSort⟩,hPair⟩
    let r : Fin 2 → VF M := fun i => ⟨z (.inr i),hSort i⟩
    have hp : ![(q 0).val,(q 1).val,(r 0).val,(r 1).val] = z ∘ idx := by
      funext i
      fin_cases i
      · exact congrFun hQ 0
      · exact congrFun hQ 1
      · rfl
      · rfl
    refine ⟨q,hq,r,?_,?_⟩
    · change ![(q 0).val,(q 1).val,(r 0).val,(r 1).val] ∈ pairedDiscImageCodes A f
      rw [hp]
      exact hPair
    · funext i
      cases i with
      | inl i => exact congrFun hQ i
      | inr i => rfl

theorem exists_finite_paired_disc_families
    (h00 : M ⊨ Axioms.ACVF00) (hc : CanonicalStructure.IsCanonical (M := M))
    {κ : Cardinal} (hκ : Cardinal.aleph0 < κ) (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V : Set M) (hsmall : Cardinal.mk S < κ)
    (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (A B : Set (VF M)) (hA : IsOpen A) (f : VF M → VF M) (hbij : Set.BijOn f A B)
    (hGraph : S.Definable LRV (scalarPartialGraph A f)) (hCont : ContinuousOn f A)
    (hBound : ∃ η : Gamma M, ∀ y ∈ B, η.val ≤ vfValue y)
    (C : Set (Fin 2 → VF M)) (hC : S.Definable LRV (vfValues '' C)) (hCFin : C.Finite)
    (hCenters : ∀ q ∈ C, q 0 ∈ A ∧ f (q 0) = q 1) :
    ∃ F : (Fin 2 → VF M) → Set (Fin 2 → VF M),
      S.Definable LRV (vfCorrespondenceGraph C F) ∧
      (⋃ q ∈ C, F q).Finite ∧
      (∀ q, (F q).Nonempty ↔ q ∈ C) ∧
      ∀ q ∈ C, ∀ r ∈ F q, ∃ hr : r 0 ≠ 0, ∃ hs : r 1 ≠ 0,
        centeredGammaDisc (q 0) (finiteValue (r 0) hr) ⊆ A ∧
        f '' centeredGammaDisc (q 0) (finiteValue (r 0) hr) =
          centeredGammaDisc (q 1) (finiteValue (r 1) hs) := by
  have hNonempty (q) (hq : q ∈ C) : (pairedRadiusFamily A f q).Nonempty := by
    obtain ⟨ρ,γ,hDisc⟩ := continuous_bijection_paired_centered_discs hc hκ.le hs hsmall hv
      A B hA f hbij hGraph hCont hBound (q 0) (hCenters q hq).1
    obtain ⟨r,hr,hR⟩ := gamma_has_vf_representative γ
    obtain ⟨s,hs₀,hS⟩ := gamma_has_vf_representative (ρ γ)
    have hR' : finiteValue r hr = γ := Subtype.ext hR
    have hS' : finiteValue s hs₀ = ρ γ := Subtype.ext hS
    refine ⟨![r,s],(pairedDiscImageCodes_at A f (q 0) (q 1) r s hr hs₀).mpr ?_⟩
    rw [hR',hS',← (hCenters q hq).2]
    exact ⟨(hCenters q hq).1,rfl,(hDisc γ le_rfl).1,(hDisc γ le_rfl).2.2⟩
  obtain ⟨F,hF,hFin,hSub,hNe⟩ := finite_vf_choice_vf_core Valued.v hv hc h00 hs V S hV hVS hSV hnt hsmall
    C hC (pairedRadiusFamily A f) (pairedRadiusFamily_graph_definable A f hGraph C hC) hNonempty
  refine ⟨F,hF,hCFin.biUnion (fun q _ => hFin q),hNe,fun q hq r hrF => ?_⟩
  have hCode := hSub q hrF
  have hSelfA : (q 0).val ∈ rawOpenBall (q 0).val (r 0).val := hCode.2.1
  have hSelfB : (q 1).val ∈ rawOpenBall (q 1).val (r 1).val := hCode.2.2.1
  have hr : r 0 ≠ 0 := fun he => hSelfA.1.2 (congrArg Subtype.val he)
  have hs₀ : r 1 ≠ 0 := fun he => hSelfB.1.2 (congrArg Subtype.val he)
  have h := (pairedDiscImageCodes_at A f (q 0) (q 1) (r 0) (r 1) hr hs₀).mp hCode
  exact ⟨hr,hs₀,h.2.2⟩

end DiamondIntegral.Section6
