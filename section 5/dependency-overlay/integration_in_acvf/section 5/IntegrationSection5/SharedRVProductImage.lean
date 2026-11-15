import IntegrationSection5.LiftedUnaryProductGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n a b l r : ℕ}
theorem coordinate_lift_product_image_sharedRV
    {A : DefSet (M := M) S 1 a} {B : DefSet (M := M) S 1 b}
    (u : SpecialBijection A B)
    {H : DefSet (M := M) S n l} {K : DefSet (M := M) S n r}
    (f : Map H K) (i : Fin n) (hf : SpecialRelative f i) (hle : l ≤ r)
    (ρ : Fin a → Fin l) (σ : Fin b → Fin r) (Q : Point (M := M) n l → Prop)
    (hQ : ∀ p x, Q (replace i p x) ↔ Q p)
    (hH : carrier H = {p | activeUnaryProjection i ρ p ∈ carrier A ∧ Q p})
    (hcomm : ∀ p : H, activeUnaryProjection i σ (f p).val =
      (u.toMap ⟨activeUnaryProjection i ρ p.val,((Set.ext_iff.mp hH p.val).mp p.property).1⟩).val)
    (hcompat : ∀ j : Fin a, σ (suffixIndex (special_chain_rvArity_le u.chain) j) = suffixIndex hle (ρ j))
    (hcover : ∀ j : Fin r, (∃ k, σ k = j) ∨ ∃ k, suffixIndex hle k = j) :
    carrier K = {q | activeUnaryProjection i σ q ∈ carrier B ∧ Q (retainedPoint hle q)} := by
  ext q
  constructor
  · intro hq
    obtain ⟨p,hp⟩ := (specialRelative_bijective hf).2 ⟨q,hq⟩
    have hpq : (f p).val = q := congrArg (fun q : K => q.val) hp
    have hsource := (Set.ext_iff.mp hH p.val).mp p.property
    refine ⟨?_,?_⟩
    · rw [← hpq,hcomm]
      exact (u.toMap ⟨activeUnaryProjection i ρ p.val,hsource.1⟩).property
    · rw [← hpq,retainedPoint_map f i hf hle p]
      exact (hQ p.val _).mpr hsource.2
  · rintro ⟨hB,hqQ⟩
    let z : B := ⟨activeUnaryProjection i σ q,hB⟩
    let a := u.inverseMap z
    let p0 := retainedPoint hle q
    let p := replace i p0 (vfAt a.val 0)
    have hpa : activeUnaryProjection i ρ p = a.val := by
      refine Prod.ext ?_ ?_
      · funext j
        fin_cases j
        simp [p,activeUnaryProjection,replace,vfAt]
      · funext j
        change q.2 (suffixIndex hle (ρ j)) = a.val.2 j
        rw [← hcompat j]
        exact (congrArg (fun v : B => v.val.2 (suffixIndex (special_chain_rvArity_le u.chain) j))
          (u.apply_inverse z)).symm.trans (special_oldLabels u a j)
    have hpH : p ∈ carrier H := (Set.ext_iff.mp hH p).mpr
      ⟨hpa.symm ▸ a.property,(hQ p0 _).mpr hqQ⟩
    let pH : H := ⟨p,hpH⟩
    have hinput : (⟨activeUnaryProjection i ρ pH.val,
        ((Set.ext_iff.mp hH pH.val).mp pH.property).1⟩ : A) = a := Subtype.ext hpa
    have hProj : activeUnaryProjection i σ (f pH).val = activeUnaryProjection i σ q := by
      rw [hcomm,hinput]
      exact congrArg (fun z : B => z.val) (u.apply_inverse z)
    have hpq : (f pH).val = q := by
      refine Prod.ext ?_ ?_
      · funext j
        by_cases hj : j = i
        · subst j
          exact congrArg (fun p : Point (M := M) 1 b => vfAt p 0) hProj
        · have h := specialRelative_unaryRelative hf pH j hj
          simpa only [pH,p,p0,retainedPoint,replace,Function.update_of_ne hj,vfAt] using h
      · funext j
        rcases hcover j with ⟨k,rfl⟩ | ⟨k,rfl⟩
        · exact congrArg (fun p : Point (M := M) 1 b => p.2 k) hProj
        · exact specialRelative_oldLabels hf pH k
    exact hpq ▸ (f pH).property

end IntegrationInACVF.Section5
