import «section 6».RawFiniteFibres

/-! Single-valued centers in every prescribed RV disc over the full VF
input. The complete definable finite family is averaged within each RV
fiber, including the singleton zero fiber. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n : ℕ} {S : Set M}
variable {G : Type} [LinearOrderedCommGroupWithZero G] [Valued (VF M) G]

theorem exists_parametric_rv_centers
    (hc : CanonicalStructure.IsCanonical (M := M)) (h00 : M ⊨ Axioms.ACVF00)
    {κ : Cardinal} (hs : Saturated M κ)
    (hv : ∀ x y : VF M, VFValued.predV x y ↔ Valued.v x ≤ Valued.v y)
    (V S : Set M) (hV : ∀ a ∈ V, iVF a) (hVS : V ⊆ S) (hSV : S ⊆ algebraicClosureSet V)
    (hnt : ∃ x : vfAlgebraicClosureField V, x ≠ 0 ∧ Valued.v x.val ≠ 1)
    (hsmall : Cardinal.mk S < κ)
    (A : Set (Fin n → VF M)) (hA : S.Definable LRV (vfValues '' A))
    (C : (Fin n → M) → Set M)
    (hC : S.Definable LRV {z : Fin n ⊕ Fin 1 → M | z (.inr 0) ∈ C (z ∘ Sum.inl)})
    (hFin : ∀ a, (C a).Finite) (hRV : ∀ a, ∀ v ∈ C a, iRV v) :
    ∃ f : (Fin (n+1) → M) → VF M, S.DefinableFun LRV (fun z => (f z).val) ∧
      ∀ a ∈ A, ∀ v ∈ C (vfValues a), iRv (f (Fin.snoc (vfValues a) v)).val = v := by
  obtain ⟨E,hE,hEf,hHit⟩ := exists_finite_rv_hitting_sets hc h00 hs hv V S hV hVS hSV hnt hsmall A hA C hC hFin hRV
  let F := rawFiniteFibre A E hEf
  let H := rvFilteredFibre F
  have hHdef : RawClosure.Tuple.RelationDefinable S (Barycentre.finiteFibreRelation H) :=
    rvFilteredFibre_definable F (rawFiniteFibre_definable A E hEf hE)
  let f (z : Fin (n+1) → M) := Barycentre.mean (H z)
  refine ⟨f,finiteMean_definable h00 hs hsmall H hHdef,?_⟩
  intro a ha v hvC
  obtain ⟨x,hx,hxv⟩ := hHit a ha v hvC
  have he : H (Fin.snoc (vfValues a) v) = (hEf a).toFinset.filter (fun y => iRv y.val = v) := by
    simp only [H,F,rvFilteredFibre,Fin.init_snoc,Fin.snoc_last,rawFiniteFibre_at A E hEf a ha]
  have hne : (H (Fin.snoc (vfValues a) v)).Nonempty := by
    rw [he]
    exact ⟨x,Finset.mem_filter.mpr ⟨(hEf a).mem_toFinset.mpr hx,hxv⟩⟩
  have hall (y : VF M) (hy : y ∈ H (Fin.snoc (vfValues a) v)) :
      rv M y = (⟨v,hRV (vfValues a) v hvC⟩ : RVInfinity M) := by
    rw [he] at hy
    exact Subtype.ext (Finset.mem_filter.mp hy).2
  exact congrArg Subtype.val (finiteMean_sameRV h00 hv _ hne _ hall)

end DiamondIntegral.Section6
