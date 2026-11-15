import Section4.RVReindexing

/-! Adjoining a constant RV volume coordinate preserves an actual unary
RV isomorphism whenever the two constants have the same absorbing status.
Both morphism obligations are proved for the unchanged RV category. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language CategoryTheory
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.DefinableGeometry SpecialTransformations.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [LRV.Structure M] {S : Set M}

def rvUnaryProfileObject (U : RVObject (M := M) S 1)
    (v : Map U.domain (DefSet.univ (rawRVSpace 2) S)) : RVObject (M := M) S 2 :=
  ⟨U.arity,U.domain,v⟩

theorem rvWeight_pair (x y : CanonicalRV.RVSort M) :
    rvWeight (![x,y] : Fin 2 → CanonicalRV.RVSort M) =
      (if x.val ≠ iRVZero then 1 else 0) + (if y.val ≠ iRVZero then 1 else 0) := by
  simp [rvWeight,Fin.sum_univ_two]

def rvUnaryProfileHom {U V : RVObject (M := M) S 1}
    (F : RVHom U V)
    (u : Map U.domain (DefSet.univ (rawRVSpace 2) S))
    (v : Map V.domain (DefSet.univ (rawRVSpace 2) S))
    (r t : CanonicalRV.RVSort M) (hrt : r.val = iRVZero ↔ t.val = iRVZero)
    (hu : ∀ a, (u a).val = ![r,U.value a 0])
    (hv : ∀ b, (v b).val = ![t,V.value b 0]) :
    RVHom (rvUnaryProfileObject U u) (rvUnaryProfileObject V v) where
  map := F.map
  volumetric a := by
    change rvWeight (u a).val ≤ rvWeight (v (F.map a)).val
    rw [hu,hv,rvWeight_pair,rvWeight_pair]
    have hc : (if r.val ≠ iRVZero then 1 else 0) = (if t.val ≠ iRVZero then 1 else 0) := by
      simp only [not_congr hrt]
    have hF := F.volumetric a
    simp only [rvWeight,Fin.sum_univ_one] at hF
    rw [hc]
    exact Nat.add_le_add_left hF _
  finite_volume_images z := by
    have hfin := (F.finite_volume_images (fun _ => z 1)).image
      (fun w : Fin 1 → CanonicalRV.RVSort M => (![t,w 0] : Fin 2 → CanonicalRV.RVSort M))
    apply hfin.subset
    rintro w ⟨a,ha,hw⟩
    have ha1 : U.value a 0 = z 1 := by
      have h := congrFun ha 1
      change (u a).val 1 = z 1 at h
      rw [hu] at h
      exact h
    refine ⟨V.value (F.map a),⟨a,?_,rfl⟩,?_⟩
    · funext i
      fin_cases i
      exact ha1
    · exact (hv (F.map a)).symm.trans hw

def rvUnaryProfileIso {U V : RVObject (M := M) S 1} (e : U ≅ V)
    (u : Map U.domain (DefSet.univ (rawRVSpace 2) S))
    (v : Map V.domain (DefSet.univ (rawRVSpace 2) S))
    (r t : CanonicalRV.RVSort M) (hrt : r.val = iRVZero ↔ t.val = iRVZero)
    (hu : ∀ a, (u a).val = ![r,U.value a 0])
    (hv : ∀ b, (v b).val = ![t,V.value b 0]) :
    rvUnaryProfileObject U u ≅ rvUnaryProfileObject V v where
  hom := rvUnaryProfileHom e.hom u v r t hrt hu hv
  inv := rvUnaryProfileHom e.inv v u t r hrt.symm hv hu
  hom_inv_id := by
    apply RVHom.ext
    have h := congrArg (fun F : RVHom U U => F.map) e.hom_inv_id
    exact h
  inv_hom_id := by
    apply RVHom.ext
    have h := congrArg (fun F : RVHom V V => F.map) e.inv_hom_id
    exact h

end IntegrationInACVF.Section5
