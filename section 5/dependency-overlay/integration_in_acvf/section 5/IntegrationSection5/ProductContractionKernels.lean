import IntegrationSection5.LiftedUnaryProductGeometry

/-! Exact kernel identities for product contractions. The retained labels
and the unary projection jointly determine every output RV label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n b l r : ℕ}

theorem activeProjection_sameRV_iff (i : Fin n) (σ : Fin b → Fin r) (hσ : Function.Surjective σ)
    (p q : Point (M := M) n r) :
    SameRV (activeUnaryProjection i σ p) (activeUnaryProjection i σ q) ↔
      rv (vfAt p i) = rv (vfAt q i) ∧ p.2 = q.2 := by
  constructor
  · intro h
    obtain ⟨hv,hr⟩ := (sameRV_iff _ _).mp h
    refine ⟨hv 0,?_⟩
    funext j
    obtain ⟨k,rfl⟩ := hσ j
    exact congrFun hr k
  · rintro ⟨hv,hr⟩
    apply (sameRV_iff _ _).mpr
    exact ⟨fun _ => hv,congrArg (fun z => z ∘ σ) hr⟩

theorem lifted_unary_sameRV_iff {H : DefSet (M := M) S 1 l} {K : DefSet (M := M) S 1 r}
    (f : Map H K) (hf : SpecialRelative f 0) (hle : l ≤ r) (σ : Fin b → Fin r)
    (hcover : ∀ j : Fin r, (∃ k, σ k = j) ∨ ∃ k, suffixIndex hle k = j) (p q : H) :
    SameRV (f p).val (f q).val ↔
      SameRV (activeUnaryProjection 0 σ (f p).val) (activeUnaryProjection 0 σ (f q).val) ∧ p.val.2 = q.val.2 := by
  constructor
  · intro h
    refine ⟨activeUnaryProjection_sameRV 0 σ h,?_⟩
    have hr := ((sameRV_iff _ _).mp h).2
    funext j
    exact (specialRelative_oldLabels hf p j).symm.trans
      ((congrFun hr (suffixIndex hle j)).trans (specialRelative_oldLabels hf q j))
  · rintro ⟨h,hold⟩
    obtain ⟨hv,hr⟩ := (sameRV_iff _ _).mp h
    apply (sameRV_iff _ _).mpr
    constructor
    · intro j
      fin_cases j
      exact hv 0
    · funext j
      rcases hcover j with ⟨k,rfl⟩ | ⟨k,rfl⟩
      · exact congrFun hr k
      · exact (specialRelative_oldLabels hf p k).trans
          ((congrFun hold k).trans (specialRelative_oldLabels hf q k).symm)

theorem headKey_labels_eq_iff (p q : Point (M := M) (n+1) r) :
    (headKey p).2 = (headKey q).2 ↔ rv (vfAt p 0) = rv (vfAt q 0) ∧ p.2 = q.2 := by
  constructor
  · intro h
    refine ⟨congrFun h 0,?_⟩
    funext j
    have hj := congrFun h (Fin.natAdd 1 j)
    simpa only [headKey,Fin.append_right] using hj
  · rintro ⟨hv,hr⟩
    change Fin.append (fun _ : Fin 1 => rv (vfAt p 0)) p.2 =
      Fin.append (fun _ : Fin 1 => rv (vfAt q 0)) q.2
    rw [hv,hr]

theorem headKey_labels_projection_iff (σ : Fin b → Fin r) (hσ : Function.Surjective σ)
    (p q : Point (M := M) (n+1) r) :
    (headKey p).2 = (headKey q).2 ↔
      SameRV (activeUnaryProjection 0 σ p) (activeUnaryProjection 0 σ q) :=
  (headKey_labels_eq_iff p q).trans (activeProjection_sameRV_iff 0 σ hσ p q).symm

end IntegrationInACVF.Section5
