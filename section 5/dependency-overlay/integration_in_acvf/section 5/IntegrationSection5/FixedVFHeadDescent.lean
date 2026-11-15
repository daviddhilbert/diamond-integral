import IntegrationSection5.GammaOrderedContraction
import IntegrationSection5.RelativeLabelPreservation
import IntegrationSection5.GammaUnaryChain
noncomputable section
set_option backward.isDefEq.respectTransparency false
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
variable {G : SpecialTransformations.Section3.GammaParameters.Base (M := M)}
variable {S : Set M} {n m l : ℕ}
variable {A : DefSet (M := M) S (n+1) m} {B : DefSet (M := M) S (n+1) l}

theorem fixedVF_headKey_kernel (f : Map A B)
    (hVF : ∀ a : A, ∀ i, vfAt (f a).val i = vfAt a.val i)
    (ρ : Fin m → Fin l) (hLabels : ∀ a : A, (f a).val.2 ∘ ρ = a.val.2)
    (hRV : ∀ a b : A, SameRV a.val b.val → SameRV (f a).val (f b).val)
    (a b : A) : headKey (f a).val = headKey (f b).val ↔ headKey a.val = headKey b.val := by
  constructor
  · intro he
    obtain ⟨ht,hSame⟩ := (headKey_eq_iff _ _).mp he
    obtain ⟨hv,hl⟩ := (sameRV_iff _ _).mp hSame
    apply (headKey_eq_iff _ _).mpr
    refine ⟨fun j => (hVF a j.succ).symm.trans ((ht j).trans (hVF b j.succ)),?_⟩
    apply (sameRV_iff _ _).mpr
    refine ⟨fun i => ?_,?_⟩
    · exact (congrArg rv (hVF a i)).symm.trans ((hv i).trans (congrArg rv (hVF b i)))
    · exact (hLabels a).symm.trans ((congrArg (fun s => s ∘ ρ) hl).trans (hLabels b))
  · intro he
    obtain ⟨ht,hSame⟩ := (headKey_eq_iff _ _).mp he
    exact (headKey_eq_iff _ _).mpr ⟨fun j => (hVF a j.succ).trans ((ht j).trans (hVF b j.succ).symm),hRV a b hSame⟩

def headDescent (f : Map A B)
    (hConst : ∀ a b : A, headKey a.val = headKey b.val → headKey (f a).val = headKey (f b).val) :
    Map (headImage A) (headImage B) :=
  Map.descend (headKeyMap A) (Map.comp (Map.toImage (headKeyMap B)) f) (by
    intro a b he
    apply Subtype.ext
    change (headKeyMap B (f a)).val = (headKeyMap B (f b)).val
    have he' : headKey a.val = headKey b.val := (headKeyMap_apply A a).symm.trans (he.trans (headKeyMap_apply A b))
    exact (headKeyMap_apply B (f a)).trans ((hConst a b he').trans (headKeyMap_apply B (f b)).symm))

theorem headDescent_square (f : Map A B)
    (hConst : ∀ a b : A, headKey a.val = headKey b.val → headKey (f a).val = headKey (f b).val)
    (a : A) : headDescent f hConst (Map.toImage (headKeyMap A) a) =
      Map.toImage (headKeyMap B) (f a) := Map.descend_apply _ _ _ a

theorem headKeyImage_surjective (A : DefSet (M := M) S (n+1) m) :
    Function.Surjective (Map.toImage (headKeyMap A)) := by
  intro q
  exact ⟨Map.imageRepresentative (headKeyMap A) q,Subtype.ext (Map.imageRepresentative_spec _ q)⟩

theorem headDescent_bijective (f : Map A B) (hf : Function.Surjective f)
    (hKernel : ∀ a b : A, headKey (f a).val = headKey (f b).val ↔ headKey a.val = headKey b.val) :
    Function.Bijective (headDescent f (fun a b h => (hKernel a b).mpr h)) := by
  constructor
  · intro p q he
    obtain ⟨a,rfl⟩ := headKeyImage_surjective A p
    obtain ⟨b,rfl⟩ := headKeyImage_surjective A q
    rw [headDescent_square,headDescent_square] at he
    have hv := congrArg (fun z : headImage B => z.val) he
    have hv' : headKey (f a).val = headKey (f b).val :=
      (headKeyMap_apply B (f a)).symm.trans (hv.trans (headKeyMap_apply B (f b)))
    apply Subtype.ext
    change (headKeyMap A a).val = (headKeyMap A b).val
    exact (headKeyMap_apply A a).trans (((hKernel a b).mp hv').trans (headKeyMap_apply A b).symm)
  · intro q
    obtain ⟨b,rfl⟩ := headKeyImage_surjective B q
    obtain ⟨a,rfl⟩ := hf b
    exact ⟨Map.toImage (headKeyMap A) a,headDescent_square f _ a⟩

theorem gamma_headDescent (f : Map A B) (hA : GammaSetDefinable G (carrier A))
    (hB : GammaSetDefinable G (carrier B)) (hf : GammaGraphDefinable G (pointMapGraph f))
    (hConst : ∀ a b : A, headKey a.val = headKey b.val → headKey (f a).val = headKey (f b).val) :
    GammaGraphDefinable G (pointMapGraph (headDescent f hConst)) := by
  have hKeyA := gamma_headKey_graph A hA
  have hKeyB := gamma_headKey_graph B hB
  have hComp := gamma_composition_graph f (Map.toImage (headKeyMap B)) hf hKeyB
  apply GammaGraphDefinable.congr ((gammaLogicInput G).comp_graph ((gammaLogicInput G).swap_graph hKeyA) hComp)
  intro p q
  constructor
  · rintro ⟨z,⟨a,rfl,ha⟩,⟨b,hb,hq⟩⟩
    have hab : a = b := Subtype.ext hb.symm
    subst b
    let u : headImage A := Map.toImage (headKeyMap A) a
    refine ⟨u,ha,?_⟩
    exact (congrArg Subtype.val (headDescent_square f hConst a)).trans hq
  · rintro ⟨u,rfl,hq⟩
    obtain ⟨a,rfl⟩ := headKeyImage_surjective A u
    refine ⟨a.val,⟨a,rfl,rfl⟩,a,rfl,?_⟩
    exact (congrArg Subtype.val (headDescent_square f hConst a)).symm.trans hq

def fixedVFHeadIso (f : Map A B) (hf : Function.Surjective f)
    (hA : GammaSetDefinable G (carrier A)) (hB : GammaSetDefinable G (carrier B))
    (hfG : GammaGraphDefinable G (pointMapGraph f))
    (hVF : ∀ a : A, ∀ i, vfAt (f a).val i = vfAt a.val i)
    (ρ : Fin m → Fin l) (hLabels : ∀ a : A, (f a).val.2 ∘ ρ = a.val.2)
    (hRV : ∀ a b : A, SameRV a.val b.val → SameRV (f a).val (f b).val) :
    GammaIso G (carrier (headImage A)) (carrier (headImage B)) where
  equiv := Equiv.ofBijective (headDescent f (fun a b h => (fixedVF_headKey_kernel f hVF ρ hLabels hRV a b).mpr h))
    (headDescent_bijective f hf (fixedVF_headKey_kernel f hVF ρ hLabels hRV))
  graph := gamma_headDescent f hA hB hfG (fun a b h => (fixedVF_headKey_kernel f hVF ρ hLabels hRV a b).mpr h)

theorem fixedVFHeadIso_square (f : Map A B) (hf : Function.Surjective f)
    (hA : GammaSetDefinable G (carrier A)) (hB : GammaSetDefinable G (carrier B))
    (hfG : GammaGraphDefinable G (pointMapGraph f))
    (hVF : ∀ a : A, ∀ i, vfAt (f a).val i = vfAt a.val i)
    (ρ : Fin m → Fin l) (hLabels : ∀ a : A, (f a).val.2 ∘ ρ = a.val.2)
    (hRV : ∀ a b : A, SameRV a.val b.val → SameRV (f a).val (f b).val) (a : A) :
    (fixedVFHeadIso f hf hA hB hfG hVF ρ hLabels hRV).equiv (Map.toImage (headKeyMap A) a) =
      Map.toImage (headKeyMap B) (f a) := headDescent_square f (fun x y h => (fixedVF_headKey_kernel f hVF ρ hLabels hRV x y).mpr h) a

end IntegrationInACVF.Section5
