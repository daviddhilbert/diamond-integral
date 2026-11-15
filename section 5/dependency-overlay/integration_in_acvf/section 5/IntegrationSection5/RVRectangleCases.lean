import IntegrationSection5.GammaRectangleFamilyComparison
import IntegrationSection5.CellLabelInjection

/-! An actual original-Gamma definable partition by whether an RV fibre is a rectangle. A four-VF witness detects failure, uniformly in every old RV label. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true in
attribute [local reducible] SpecialTransformations.DefinableGeometry.Space.prod
  SpecialTransformations.Section4.realSpace SpecialTransformations.Milestone0.sortEval
  SpecialTransformations.Section4.vfSpace SpecialTransformations.Section4.rvSpace
  SpecialTransformations.Section5.pointSpace
open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section5 SpecialTransformations.Section3
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {m : ℕ}

def mixedVFSelect {n u : ℕ} (ρ : Fin u → Fin n) (p : Point (M := M) n m) : Point (M := M) u m :=
  (p.1 ∘ ρ,p.2)

def mixedVFSelectMap (S : Set M) {n u : ℕ} (ρ : Fin u → Fin n) :
    Map (PresentedSet.univ (pointSpace (M := M) n m) S)
      (PresentedSet.univ (pointSpace u m) S) :=
  Map.ofCodes _ (mixedVFSelect ρ)
    (fun z => Sum.elim (fun j => z (.inl (ρ j))) (fun j => z (.inr j)))
    (by intro j; cases j with
        | inl j => exact rawProj S (.inl (ρ j) : Fin n ⊕ Fin m)
        | inr j => exact rawProj S (.inr j : Fin n ⊕ Fin m))
    (by intro c; exact ⟨fun j => c.property.1 (ρ j),c.property.2⟩)
    (by intro c; rfl)

theorem gamma_mixedVFSelect_preimage {n u : ℕ} (ρ : Fin u → Fin n)
    (A : Set (Point (M := M) u m)) (hA : GammaSetDefinable G A) :
    GammaSetDefinable G {p : Point (M := M) n m | mixedVFSelect ρ p ∈ A} := by
  have h := (gammaLogicInput G).preimage_real (mixedVFSelectMap G.real ρ) hA
  convert h using 1
  ext p
  constructor
  · intro hp
    exact ⟨⟨p,Set.mem_univ _⟩,rfl,hp⟩
  · rintro ⟨a,rfl,ha⟩
    exact ha

def rectangleFailureWitnesses (A : Set (Point (M := M) 2 m)) : Set (Point (M := M) 4 m) :=
  {p | mixedVFSelect (![0,1] : Fin 2 → Fin 4) p ∈ A ∧
    mixedVFSelect (![2,3] : Fin 2 → Fin 4) p ∈ A ∧
    mixedVFSelect (![0,3] : Fin 2 → Fin 4) p ∉ A}

theorem rectangleFailureWitnesses_gamma (A : Set (Point (M := M) 2 m))
    (hA : GammaSetDefinable G A) : GammaSetDefinable G (rectangleFailureWitnesses A) := by
  have h := (gammaLogicInput G).sdiff
    ((gammaLogicInput G).inter
      (gamma_mixedVFSelect_preimage (![0,1] : Fin 2 → Fin 4) A hA)
      (gamma_mixedVFSelect_preimage (![2,3] : Fin 2 → Fin 4) A hA))
    (gamma_mixedVFSelect_preimage (![0,3] : Fin 2 → Fin 4) A hA)
  convert h using 1
  ext p
  change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ _)
  tauto

def rectangleFailureCodes (A : Set (Point (M := M) 2 m)) : Set (Point (M := M) 0 m) :=
  {s | ∃ p ∈ rectangleFailureWitnesses A, p.2 = s.2}

theorem rectangleFailureCodes_gamma (A : Set (Point (M := M) 2 m))
    (hA : GammaSetDefinable G A) : GammaSetDefinable G (rectangleFailureCodes A) := by
  have h := (gammaLogicInput G).image_real (pointLabels G.real 4 m) (rectangleFailureWitnesses_gamma A hA)
  convert h using 1
  ext s
  constructor
  · rintro ⟨p,hp,he⟩
    refine ⟨⟨p,Set.mem_univ _⟩,hp,Prod.ext (Subsingleton.elim _ _) ?_⟩
    simpa only [pointLabels_snd] using he
  · rintro ⟨p,hp,he⟩
    exact ⟨p.val,hp,(pointLabels_snd _ _ _ p).symm.trans (congrArg Prod.snd he)⟩

def rectangleFailureDomain (A : Set (Point (M := M) 2 m)) : Set (Point (M := M) 2 m) :=
  {p | (Fin.elim0,p.2) ∈ rectangleFailureCodes A}

theorem rectangleFailureDomain_gamma (A : Set (Point (M := M) 2 m))
    (hA : GammaSetDefinable G A) : GammaSetDefinable G (rectangleFailureDomain A) := by
  have h := (gammaLogicInput G).preimage_real (pointLabels G.real 2 m) (rectangleFailureCodes_gamma A hA)
  convert h using 1
  ext p
  constructor
  · intro hp
    refine ⟨⟨p,Set.mem_univ _⟩,rfl,?_⟩
    change ∃ q ∈ rectangleFailureWitnesses A, q.2 = (pointLabels G.real 2 m ⟨p,Set.mem_univ _⟩).val.2
    rwa [pointLabels_snd]
  · rintro ⟨a,rfl,ha⟩
    change ∃ q ∈ rectangleFailureWitnesses A, q.2 = (pointLabels G.real 2 m a).val.2 at ha
    rwa [pointLabels_snd] at ha

def rectangleFamilyBranch (A : Set (Point (M := M) 2 m)) : Set (Point (M := M) 2 m) :=
  A \ rectangleFailureDomain A

def nonrectangleFamilyBranch (A : Set (Point (M := M) 2 m)) : Set (Point (M := M) 2 m) :=
  A ∩ rectangleFailureDomain A

theorem rectangleFamilyBranch_gamma (A : Set (Point (M := M) 2 m)) (hA : GammaSetDefinable G A) :
    GammaSetDefinable G (rectangleFamilyBranch A) :=
  (gammaLogicInput G).sdiff hA (rectangleFailureDomain_gamma A hA)

theorem nonrectangleFamilyBranch_gamma (A : Set (Point (M := M) 2 m)) (hA : GammaSetDefinable G A) :
    GammaSetDefinable G (nonrectangleFamilyBranch A) :=
  (gammaLogicInput G).inter hA (rectangleFailureDomain_gamma A hA)

theorem rectangleFamilyBranches_cover (A : Set (Point (M := M) 2 m)) :
    rectangleFamilyBranch A ∪ nonrectangleFamilyBranch A = A := by
  ext p
  simp only [rectangleFamilyBranch,nonrectangleFamilyBranch,Set.mem_union,Set.mem_sdiff,Set.mem_inter_iff]
  tauto

theorem rectangleFamilyBranches_disjoint (A : Set (Point (M := M) 2 m)) :
    Disjoint (rectangleFamilyBranch A) (nonrectangleFamilyBranch A) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  exact hp.2 hq.2

end IntegrationInACVF.Section5

namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {m : ℕ}

theorem rectangleFailureDomain_iff (A : Set (Point (M := M) 2 m)) (p : Point (M := M) 2 m) :
    p ∈ rectangleFailureDomain A ↔
      ∃ x ∈ A, ∃ y ∈ A, x.2 = p.2 ∧ y.2 = p.2 ∧ (![vfAt x 0,vfAt y 1],p.2) ∉ A := by
  constructor
  · rintro ⟨z,hz,hl⟩
    let x := mixedVFSelect (![0,1] : Fin 2 → Fin 4) z
    let y := mixedVFSelect (![2,3] : Fin 2 → Fin 4) z
    refine ⟨x,hz.1,y,hz.2.1,hl,hl,?_⟩
    have he : (![vfAt x 0,vfAt y 1],p.2) = mixedVFSelect (![0,3] : Fin 2 → Fin 4) z := by
      apply Prod.ext
      · funext i; fin_cases i <;> rfl
      · exact hl.symm
    exact he ▸ hz.2.2
  · rintro ⟨x,hx,y,hy,hlx,hly,hmix⟩
    let z : Point (M := M) 4 m := (![vfAt x 0,vfAt x 1,vfAt y 0,vfAt y 1],p.2)
    have hzx : mixedVFSelect (![0,1] : Fin 2 → Fin 4) z = x := by
      apply Prod.ext
      · funext i; fin_cases i <;> rfl
      · exact hlx.symm
    have hzy : mixedVFSelect (![2,3] : Fin 2 → Fin 4) z = y := by
      apply Prod.ext
      · funext i; fin_cases i <;> rfl
      · exact hly.symm
    refine ⟨z,⟨hzx.symm ▸ hx,hzy.symm ▸ hy,?_⟩,rfl⟩
    have hm : mixedVFSelect (![0,3] : Fin 2 → Fin 4) z = (![vfAt x 0,vfAt y 1],p.2) := by
      apply Prod.ext
      · funext i; fin_cases i <;> rfl
      · rfl
    exact hm.symm ▸ hmix

theorem rectangleFamilyBranch_rectangles (A : Set (Point (M := M) 2 m)) :
    RVFibreRectangles (rectangleFamilyBranch A) := by
  intro p hp q hq hl
  have hmix : (![vfAt p 0,vfAt q 1],p.2) ∈ A := by
    by_contra hn
    exact hp.2 ((rectangleFailureDomain_iff A p).mpr ⟨p,hp.1,q,hq.1,rfl,hl.symm,hn⟩)
  exact ⟨hmix,hp.2⟩

theorem nonrectangleFamilyBranch_fibre (A : Set (Point (M := M) 2 m))
    (p : Point (M := M) 2 m) (hp : p ∈ nonrectangleFamilyBranch A) :
    ¬ RVFibreRectangles {q | q ∈ A ∧ q.2 = p.2} := by
  obtain ⟨x,hx,y,hy,hlx,hly,hn⟩ := (rectangleFailureDomain_iff A p).mp hp.2
  intro hRect
  have h := hRect x ⟨hx,hlx⟩ y ⟨hy,hly⟩ (hlx.trans hly.symm)
  have hm : (![vfAt x 0,vfAt y 1],p.2) ∈ A := by
    simpa only [hlx] using h.1
  exact hn hm

end IntegrationInACVF.Section5

namespace IntegrationInACVF.Section5
open IntegrationInACVF.Section4.Cells
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {m : ℕ}

theorem rectangleFailureCodes_native_iff (A : Set (Point (M := M) 2 m)) (s : Fin m → RV (M := M)) :
    (Fin.elim0,s) ∈ rectangleFailureCodes A ↔
      nativeTwoFibre A s ≠ first (nativeTwoFibre A s) ×ˢ second (nativeTwoFibre A s) := by
  constructor
  · intro hs hRect
    obtain ⟨x,hx,y,hy,hlx,hly,hn⟩ :=
      (rectangleFailureDomain_iff A (fun _ : Fin 2 => 0,s)).mp hs
    have hxR : (vfAt x 0,vfAt x 1) ∈ nativeTwoFibre A s := by
      change (![vfAt x 0,vfAt x 1],s) ∈ A
      have he : (![vfAt x 0,vfAt x 1],s) = x := by
        apply Prod.ext
        · funext i; fin_cases i <;> rfl
        · exact hlx.symm
      exact he.symm ▸ hx
    have hyR : (vfAt y 0,vfAt y 1) ∈ nativeTwoFibre A s := by
      change (![vfAt y 0,vfAt y 1],s) ∈ A
      have he : (![vfAt y 0,vfAt y 1],s) = y := by
        apply Prod.ext
        · funext i; fin_cases i <;> rfl
        · exact hly.symm
      exact he.symm ▸ hy
    exact hn ((Set.ext_iff.mp hRect (vfAt x 0,vfAt y 1)).mpr
      ⟨⟨(vfAt x 0,vfAt x 1),hxR,rfl⟩,⟨(vfAt y 0,vfAt y 1),hyR,rfl⟩⟩)
  · intro hRect
    by_contra hs
    apply hRect
    ext p
    constructor
    · intro hp
      exact ⟨⟨p,hp,rfl⟩,⟨p,hp,rfl⟩⟩
    · rintro ⟨⟨x,hx,hxp⟩,⟨y,hy,hyp⟩⟩
      by_contra hn
      apply hs
      apply (rectangleFailureDomain_iff A (fun _ : Fin 2 => 0,s)).mpr
      refine ⟨(![x.1,x.2],s),hx,(![y.1,y.2],s),hy,rfl,rfl,?_⟩
      change (![p.1,p.2],s) ∉ A at hn
      simpa only [vfAt,Matrix.cons_val_zero,Matrix.cons_val_one,hxp,hyp] using hn

theorem nonrectangleFamilyBranch_native_fibre (A : Set (Point (M := M) 2 m))
    (s : Fin m → RV (M := M)) (hs : (nativeTwoFibre (nonrectangleFamilyBranch A) s).Nonempty) :
    nativeTwoFibre (nonrectangleFamilyBranch A) s = nativeTwoFibre A s ∧
      nativeTwoFibre A s ≠ first (nativeTwoFibre A s) ×ˢ second (nativeTwoFibre A s) := by
  obtain ⟨p,hp⟩ := hs
  have hCode : (Fin.elim0,s) ∈ rectangleFailureCodes A := hp.2
  refine ⟨?_,(rectangleFailureCodes_native_iff A s).mp hCode⟩
  ext q
  exact ⟨And.left,fun h => ⟨h,hCode⟩⟩

end IntegrationInACVF.Section5
