import «section 6».RVResidualDomains

/-! The residual domain has an actual finite-to-one map to the old
prefix volume. Its target volumes lie in a finite product of the finite
obstacle rows. This proves the strict RV dimension drop. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 6000000
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2
namespace DiamondIntegral.Section6
variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {S : Set M} {n : ℕ}

theorem rvResidualPrefixMap_finite {U V : RVObject (M := M) S (n+1)} (F : RVHom U V)
    (E : Fin (n+1) → RawClosure.Tuple.GoodRelation (n := n) S)
    (hF : Function.Injective F.map) (hVF : V.volume.FiniteFibres) : (rvResidualPrefixMap F E).FiniteFibres := by
  let D := rvResidualDomain F E
  let hD := rvResidualDomain_subset F E
  let ι (u : D) : U.domain := ⟨u.val,hD u.property⟩
  let f := (V.volume.comp F.map).restrict hD
  have hf : f.FiniteFibres := (hVF.comp (Map.finiteFibres_of_injective hF)).restrict hD
  apply finite_fibres_of_finite_volume_images f (rvResidualPrefixMap F E) hf
  intro a
  let T : Set (Fin (n+1) → RVInfinity M) :=
    {t | ∀ j, (rvValues a.val,(t j).val) ∈ (E j).val}
  have hT : T.Finite := by
    exact (Set.Finite.pi' (fun j => (E j).property.2 (rvValues a.val))).preimage rvValues_injective.injOn
  apply Set.Finite.of_finite_image (f :=
    (Subtype.val : DefSet.univ (rawRVSpace (M := M) (n+1)) S → Fin (n+1) → RVInfinity M)) ?_
    Subtype.val_injective.injOn
  rw [Set.image_image]
  apply hT.subset
  rintro t ⟨u,hu,rfl⟩ j
  have h := (rvResidualDomain_mem F E (ι u)).mp u.property j
  have hPre : Fin.init (U.value (ι u)) = a.val := by
    have h := congrArg Subtype.val hu
    rw [rvResidualPrefixMap_value] at h
    exact h
  have hRawPre : Fin.init (rvValues (U.value (ι u))) = rvValues a.val :=
    congrArg (fun z : Fin n → RVInfinity M => rvValues z) hPre
  rw [hRawPre] at h
  exact h

theorem rvResidualDomain_dimension_drop {U V : RVObject (M := M) S (n+1)} (F : RVHom U V)
    (E : Fin (n+1) → RawClosure.Tuple.GoodRelation (n := n) S)
    (hF : Function.Injective F.map) (hVF : V.volume.FiniteFibres) : rvDim (rvResidualDomain F E) < n+1 := by
  exact Nat.lt_succ_of_le ((rvDim_le_iff (rvResidualDomain F E) n).mpr
    ⟨n,le_rfl,rvResidualPrefixMap F E,rvResidualPrefixMap_finite F E hF hVF⟩)

end DiamondIntegral.Section6
