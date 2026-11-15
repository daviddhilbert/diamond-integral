import IntegrationSection5.RVUnaryProfiles

/-! An actual varying-profile RV[2] isomorphism criterion. Pointwise absorbing status and finite first-coordinate images are explicit obligations; this criterion alone is not the uniform comparison producer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [LRV.Structure M] {S : Set M}

def rvVariableUnaryProfileHom {U V : RVObject (M := M) S 1}
    (F : RVHom U V)
    (u : Map U.domain (DefSet.univ (rawRVSpace 2) S))
    (v : Map V.domain (DefSet.univ (rawRVSpace 2) S))
    (hu : ∀ a, (u a).val 1 = U.value a 0) (hv : ∀ b, (v b).val 1 = V.value b 0)
    (hz : ∀ a, ((u a).val 0).val = iRVZero ↔ ((v (F.map a)).val 0).val = iRVZero)
    (hFirst : ∀ z : Fin 2 → CanonicalRV.RVSort M,
      {t : CanonicalRV.RVSort M | ∃ a : U.domain, (u a).val = z ∧ (v (F.map a)).val 0 = t}.Finite) :
    RVHom (rvUnaryProfileObject U u) (rvUnaryProfileObject V v) where
  map := F.map
  volumetric a := by
    change rvWeight (u a).val ≤ rvWeight (v (F.map a)).val
    have huEta : (u a).val = ![(u a).val 0,(u a).val 1] := by funext j; fin_cases j <;> rfl
    have hvEta : (v (F.map a)).val = ![(v (F.map a)).val 0,(v (F.map a)).val 1] := by funext j; fin_cases j <;> rfl
    rw [huEta,hvEta,rvWeight_pair,rvWeight_pair]
    have hFirst : (if ((u a).val 0).val ≠ iRVZero then 1 else 0) =
        (if ((v (F.map a)).val 0).val ≠ iRVZero then 1 else 0) := by simp only [not_congr (hz a)]
    have hF := F.volumetric a
    simp only [rvWeight,Fin.sum_univ_one] at hF
    rw [hFirst,hu,hv]
    exact Nat.add_le_add_left hF _
  finite_volume_images z := by
    have hSecond := (F.finite_volume_images (fun _ => z 1)).image (fun w => w 0)
    have hFinite := ((hFirst z).prod hSecond).image
      (fun p : CanonicalRV.RVSort M × CanonicalRV.RVSort M => (![p.1,p.2] : Fin 2 → CanonicalRV.RVSort M))
    apply hFinite.subset
    rintro w ⟨a,ha,hw⟩
    have hIn : U.value a = fun _ => z 1 := by
      funext j
      fin_cases j
      exact (hu a).symm.trans (congrFun ha 1)
    refine ⟨(w 0,w 1),⟨?_,?_⟩,?_⟩
    · exact ⟨a,ha,congrFun hw 0⟩
    · exact ⟨V.value (F.map a),⟨a,hIn,rfl⟩,(hv (F.map a)).symm.trans (congrFun hw 1)⟩
    · funext j; fin_cases j <;> rfl

def rvVariableUnaryProfileIso {U V : RVObject (M := M) S 1}
    (e : U ≅ V)
    (u : Map U.domain (DefSet.univ (rawRVSpace 2) S))
    (v : Map V.domain (DefSet.univ (rawRVSpace 2) S))
    (hu : ∀ a, (u a).val 1 = U.value a 0) (hv : ∀ b, (v b).val 1 = V.value b 0)
    (hz : ∀ a, ((u a).val 0).val = iRVZero ↔ ((v (e.hom.map a)).val 0).val = iRVZero)
    (hzInv : ∀ b, ((v b).val 0).val = iRVZero ↔ ((u (e.inv.map b)).val 0).val = iRVZero)
    (hFirst : ∀ z : Fin 2 → CanonicalRV.RVSort M,
      {t : CanonicalRV.RVSort M | ∃ a : U.domain, (u a).val = z ∧ (v (e.hom.map a)).val 0 = t}.Finite)
    (hFirstInv : ∀ z : Fin 2 → CanonicalRV.RVSort M,
      {t : CanonicalRV.RVSort M | ∃ b : V.domain, (v b).val = z ∧ (u (e.inv.map b)).val 0 = t}.Finite) :
    rvUnaryProfileObject U u ≅ rvUnaryProfileObject V v where
  hom := rvVariableUnaryProfileHom e.hom u v hu hv hz hFirst
  inv := rvVariableUnaryProfileHom e.inv v u hv hu hzInv hFirstInv
  hom_inv_id := by
    apply RVHom.ext
    exact congrArg (fun F : RVHom U U => F.map) e.hom_inv_id
  inv_hom_id := by
    apply RVHom.ext
    exact congrArg (fun F : RVHom V V => F.map) e.inv_hom_id

end IntegrationInACVF.Section5
