import «section 6».RefinedLabelCentripetalMaps

/-! Exact fiber transport when the whole carried-coordinate bundle is
regularized. The new leading-term tag of the carried coordinate must
agree with its retained old tag; after that check the projected fiber
is exactly the lower-dimensional regularized fiber. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

open Classical FirstOrder FirstOrder.Language
open SpecialTransformations.Milestone0 SpecialTransformations.Milestone0.LRV
open SpecialTransformations.Section3 SpecialTransformations.Section4 SpecialTransformations.Section9
open SpecialTransformations.DefinableGeometry DiamondIntegral.Section2

namespace DiamondIntegral.Section6

variable {M : Type} [LRV.Structure M] [M ⊨ Axioms.ACVF] {n r : ℕ} {S : Set M}

def regularizedBundleLabels (n r : ℕ) : Fin (n+r) → Fin ((n+1)+r) :=
  Fin.addCases (fun i => Fin.castAdd r i.castSucc) (Fin.natAdd (n+1))

def regularizedBundleBase (A : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r) :
    DefSet (rawMixedSpace (M := M) n ((n+1)+r)) S :=
  (vfDropLast (regularizeMap (rvCoordinateBundle A k)).image).image

theorem regularizedBundleLabels_old (u : Fin ((n+1)+r) → RVInfinity M) :
    (u ∘ regularizedBundleLabels n r) ∘ Fin.natAdd n = u ∘ Fin.natAdd (n+1) := by
  funext i
  simp only [Function.comp_apply,regularizedBundleLabels,Fin.addCases_right]

theorem regularizedBundleLabels_new (u : Fin ((n+1)+r) → RVInfinity M) :
    (u ∘ regularizedBundleLabels n r) ∘ Fin.castAdd r =
      (fun i : Fin n => u (Fin.castAdd r i.castSucc)) := by
  funext i
  simp only [Function.comp_apply,regularizedBundleLabels,Fin.addCases_left]

theorem regularizedBundleBase_fibre
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r)
    (u : Fin ((n+1)+r) → RVInfinity M) :
    vfFibre (regularizedBundleBase A k).carrier u =
      if u (Fin.castAdd r (Fin.last n)) = u (Fin.natAdd (n+1) k) then
        vfFibre (regularizeMap A).image.carrier (u ∘ regularizedBundleLabels n r) else ∅ := by
  rw [regularizedBundleBase,vfDropLast_image_fibre,regularization_carrier,regularized_fibre]
  have hOld : vfFibre (regularizeMap A).image.carrier (u ∘ regularizedBundleLabels n r) =
      vfFibre A.carrier (u ∘ Fin.natAdd (n+1)) ∩
        {a | tupleRV M a = fun i : Fin n => u (Fin.castAdd r i.castSucc)} := by
    rw [regularization_carrier,regularized_fibre,regularizedBundleLabels_old,regularizedBundleLabels_new]
  rw [hOld]
  ext a
  by_cases hTag : u (Fin.castAdd r (Fin.last n)) = u (Fin.natAdd (n+1) k)
  · rw [if_pos hTag]
    constructor
    · rintro ⟨x,⟨hx,hRV⟩,hxa⟩
      refine ⟨?_,?_⟩
      · exact hxa ▸ hx.1
      · funext i
        have hi := congrFun hRV i.castSucc
        change rv M (x i.castSucc) = u (Fin.castAdd r i.castSucc) at hi
        change rv M (a i) = u (Fin.castAdd r i.castSucc)
        rw [← hxa]
        exact hi
    · rintro ⟨ha,hRV⟩
      obtain ⟨x,hx⟩ := rv_surjective (u (Fin.castAdd r (Fin.last n)))
      let b : Fin (n+1) → VF M := Fin.snoc a x
      have hba : Fin.init b = a := by simp only [b,Fin.init_snoc]
      refine ⟨b,⟨⟨?_,?_⟩,?_⟩,hba⟩
      · exact hba.symm ▸ ha
      · simpa only [b,Fin.snoc_last,Function.comp_apply] using hx.trans hTag
      · funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · change rv M (b (Fin.last n)) = u (Fin.castAdd r (Fin.last n))
          simpa only [b,Fin.snoc_last] using hx
        · change rv M (b j.castSucc) = u (Fin.castAdd r j.castSucc)
          have hj := congrFun hRV j
          change rv M (a j) = u (Fin.castAdd r j.castSucc) at hj
          simpa only [b,Fin.snoc_castSucc] using hj
  · rw [if_neg hTag]
    constructor
    · rintro ⟨x,⟨hx,hRV⟩,hxa⟩
      apply False.elim
      apply hTag
      have hlast := congrFun hRV (Fin.last n)
      exact hlast.symm.trans hx.2
    · exact fun h => h.elim

theorem regularizedBundleBase_old_or_empty
    (A : DefSet (rawMixedSpace (M := M) n r) S) (k : Fin r)
    (u : Fin ((n+1)+r) → RVInfinity M) :
    vfFibre (regularizedBundleBase A k).carrier u = ∅ ∨
      vfFibre (regularizedBundleBase A k).carrier u =
        vfFibre (regularizeMap A).image.carrier (u ∘ regularizedBundleLabels n r) := by
  rw [regularizedBundleBase_fibre]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

end DiamondIntegral.Section6
