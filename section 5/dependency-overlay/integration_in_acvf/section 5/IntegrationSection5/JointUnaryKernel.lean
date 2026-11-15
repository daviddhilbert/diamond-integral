import IntegrationSection5.ProductContractionKernels
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {S : Set M} {n m l r b c : ℕ}
variable {X : DefSet (M := M) S n m} {H : DefSet (M := M) S 1 l} {K : DefSet (M := M) S 1 r}
variable {BD : DefSet (M := M) S 1 b} {BE : DefSet (M := M) S 1 c}

theorem unary_headKey_eq_iff_sameRV (p q : Point (M := M) 1 r) :
    headKey p = headKey q ↔ SameRV p q := by
  rw [headKey_eq_iff]
  exact ⟨And.right,fun h => ⟨fun j => Fin.elim0 j,h⟩⟩

theorem lifted_unary_joint_kernel (f : Map H K) (hf : SpecialRelative f 0)
    (hle : l ≤ r) (σ : Fin c → Fin r)
    (hCover : ∀ j : Fin r, (∃ k, σ k = j) ∨ ∃ k, suffixIndex hle k = j)
    (pre : Map X H) (d : Map X BD) (e : Map X BE) (φ : X → VF (M := M))
    (hPreVF : ∀ p : X, vfAt (pre p).val 0 = φ p)
    (hPre : ∀ p q : X, SameRV (pre p).val (pre q).val ↔ rv (φ p) = rv (φ q) ∧ SameRV (d p).val (d q).val)
    (hFactor : ∀ p : X, activeUnaryProjection 0 σ (f (pre p)).val = (e p).val)
    (hInv : ∀ p q : X, SameRV (e p).val (e q).val → rv (φ p) = rv (φ q)) (p q : X) :
    headKey (f (pre p)).val = headKey (f (pre q)).val ↔ SameRV (d p).val (d q).val ∧ SameRV (e p).val (e q).val := by
  rw [unary_headKey_eq_iff_sameRV,lifted_unary_sameRV_iff f hf hle σ hCover,hFactor,hFactor]
  constructor
  · rintro ⟨he,hl⟩
    have hφ := hInv p q he
    have hSame : SameRV (pre p).val (pre q).val := by
      apply (sameRV_iff _ _).mpr
      refine ⟨?_,hl⟩
      intro i
      fin_cases i
      change rv (vfAt (pre p).val 0) = rv (vfAt (pre q).val 0)
      rw [hPreVF,hPreVF]
      exact hφ
    exact ⟨((hPre p q).mp hSame).2,he⟩
  · rintro ⟨hd,he⟩
    exact ⟨he,((sameRV_iff _ _).mp ((hPre p q).mpr ⟨hInv p q he,hd⟩)).2⟩

theorem sameRV_pair_of_fixedVF {a b : ℕ} (p q : Point (M := M) 1 a) (p' q' : Point (M := M) 1 b)
    (σ : Fin a → Fin b) (hp : vfAt p' 0 = vfAt p 0) (hq : vfAt q' 0 = vfAt q 0)
    (hlp : p'.2 ∘ σ = p.2) (hlq : q'.2 ∘ σ = q.2) (hForward : SameRV p q → SameRV p' q') :
    SameRV p' q' ↔ SameRV p q := by
  refine ⟨?_,hForward⟩
  intro he
  obtain ⟨hv,hl⟩ := (sameRV_iff _ _).mp he
  apply (sameRV_iff _ _).mpr
  refine ⟨?_,?_⟩
  · intro i
    fin_cases i
    change rv (vfAt p 0) = rv (vfAt q 0)
    rw [← hp,← hq]
    exact hv 0
  · exact hlp.symm.trans ((congrArg (fun s => s ∘ σ) hl).trans hlq)

end IntegrationInACVF.Section5
