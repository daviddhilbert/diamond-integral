import IntegrationSection5.RVAttachment
import IntegrationSection5.MixedFibreDefinability
import IntegrationSection5.VFPermutation

/-! RV recoding preserves the full VF tuple. If the code determines the
old RV tuple, the recoding is an actual original-base definable injection. -/
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
open IntegrationInACVF.Section4
namespace IntegrationInACVF.Section5
variable {M : Type} [sM : LRV.Structure M] [hM : M ⊨ Axioms.ACVF]
variable {G : GammaParameters.Base (M := M)} {n m d : ℕ} {A : Set (Point (M := M) n m)}

def rvRecodePoint (P : GammaRVMap G A d) (a : A) : Point (M := M) n d := (a.val.1,P.toFun a)

def rvRecodeTarget (P : GammaRVMap G A d) : Set (Point (M := M) n d) := Set.range (rvRecodePoint P)

theorem rvRecode_graph (P : GammaRVMap G A d) :
    GammaGraphDefinable G (fun p q => ∃ a : A, a.val = p ∧ rvRecodePoint P a = q) := by
  let L := gammaLogicInput G
  let X := PresentedSet.univ (pointSpace (M := M) n m) G.real
  let Y := PresentedSet.univ (pointSpace (M := M) n d) G.real
  let F := MixedFibreDefinability.vfCoordinateMap (n := n) (m := m) G.real (id : Fin n → Fin n)
  let H := MixedFibreDefinability.vfCoordinateMap (n := n) (m := d) G.real (id : Fin n → Fin n)
  have hVF := L.comp_graph (L.real_map_graph F) (L.swap_graph (L.real_map_graph H))
  have hCode := P.graph.preimage_maps (Map.id X) (pointLabels G.real n d)
  apply GammaGraphDefinable.congr (GammaGraphOperations.inter G hVF hCode)
  intro p q
  constructor
  · rintro ⟨⟨z,⟨a,ha,haz⟩,⟨b,hb,hbz⟩⟩,c,hc,hcode⟩
    have hF : p.1 = q.1 := by
      have he := congrArg Prod.fst (haz.trans hbz.symm)
      change a.val.1 = b.val.1 at he
      rwa [ha,hb] at he
    refine ⟨c,hc,Prod.ext ?_ ?_⟩
    · exact (congrArg Prod.fst hc).trans hF
    · change P.toFun c = q.2
      simpa only [pointLabels_snd] using hcode
  · rintro ⟨a,rfl,he⟩
    have hv : a.val.1 = q.1 := congrArg Prod.fst he
    have hc : P.toFun a = q.2 := congrArg Prod.snd he
    refine ⟨⟨(a.val.1,Fin.elim0),⟨⟨a.val,Set.mem_univ _⟩,rfl,rfl⟩,
      ⟨q,Set.mem_univ _⟩,rfl,?_⟩,a,rfl,?_⟩
    · exact Prod.ext hv.symm rfl
    · simpa only [pointLabels_snd] using hc

theorem rvRecode_injective (P : GammaRVMap G A d)
    (hP : ∀ a b, P.toFun a = P.toFun b → a.val.2 = b.val.2) :
    Function.Injective (rvRecodePoint P) := by
  intro a b he
  have hv : a.val.1 = b.val.1 := congrArg (fun p : Point (M := M) n d => p.1) he
  have hc : P.toFun a = P.toFun b := congrArg (fun p : Point (M := M) n d => p.2) he
  exact Subtype.ext (Prod.ext hv (hP a b hc))

def rvRecodeIso (P : GammaRVMap G A d)
    (hP : ∀ a b, P.toFun a = P.toFun b → a.val.2 = b.val.2) :
    GammaIso G A (rvRecodeTarget P) where
  equiv := Equiv.ofBijective (fun a => ⟨rvRecodePoint P a,⟨a,rfl⟩⟩)
    ⟨fun a b he => rvRecode_injective P hP (congrArg Subtype.val he),
      by rintro ⟨q,a,ha⟩; exact ⟨a,Subtype.ext ha⟩⟩
  graph := rvRecode_graph P

def nativeTwoFibre (B : Set (Point (M := M) 2 d)) (s : Fin d → RV (M := M)) :
    Set (VF (M := M) × VF (M := M)) := {p | (![p.1,p.2],s) ∈ B}

end IntegrationInACVF.Section5
