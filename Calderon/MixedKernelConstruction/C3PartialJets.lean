import Calderon.MixedKernelConstruction.C3CoefficientAgreement
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Set Metric
open scoped ContDiff Topology Pointwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

def partialSecondJet (n : ℕ) (F : R3 × R3 → ℝ) (p : R3 × R3) : R3 [×n]→L[ℝ] ℝ :=
  iteratedFDeriv ℝ n (fun y => F (p.1,y)) p.2

/-- Local affine restriction of the joint jet; global smoothness is not required. -/
theorem partialSecondJet_eq (n : ℕ) (F : R3 × R3 → ℝ)
    (Ω : Set (R3 × R3)) (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ ∞ F Ω)
    (x y : R3) (hxy : (x,y) ∈ Ω) :
    partialSecondJet n F (x,y) = (iteratedFDeriv ℝ n F (x,y)).compContinuousLinearMap
      (fun _ => (LinearIsometry.inr ℝ R3 R3).toContinuousLinearMap) := by
  let a : R3 × R3 := (x,0)
  let I : R3 →L[ℝ] R3 × R3 := (LinearIsometry.inr ℝ R3 R3).toContinuousLinearMap
  let T : Set (R3 × R3) := (fun p => a+p) ⁻¹' Ω
  let W : Set R3 := I ⁻¹' T
  have hT : IsOpen T := hΩ.preimage (continuous_const.add continuous_id)
  have hW : IsOpen W := hT.preimage I.continuous
  have hshift : ContDiffOn ℝ ∞ (fun p => F (a+p)) T :=
    hF.comp ((contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : R3 × R3 => a) T).add
      contDiffOn_id) (fun _ hp => hp)
  have hpair (z : R3) : a + I z = (x,z) := by
    apply Prod.ext <;> simp [a,I]
  have hxT : I y ∈ T := by
    change a + I y ∈ Ω
    simpa only [hpair] using hxy
  have hxW : y ∈ W := hxT
  have htranslate : a +ᵥ T = Ω := by
    ext p
    constructor
    · rintro ⟨q,hq,hqp⟩
      change a + q = p at hqp
      rw [← hqp]
      exact hq
    · intro hp
      have hc : a+(p-a)=p := by abel
      refine ⟨p-a, ?_, ?_⟩
      · change a+(p-a) ∈ Ω
        rwa [hc]
      · exact hc
  have hcomp := I.iteratedFDerivWithin_comp_right hshift hT.uniqueDiffOn hW.uniqueDiffOn
    hxT (i := n) (by simp)
  have hfun : (fun p => F (a+p)) ∘ I = (fun z => F (x,z)) := by
    funext z
    simp only [Function.comp_apply,hpair]
  have hjoint : iteratedFDerivWithin ℝ n (fun p => F (a+p)) T (I y) =
      iteratedFDeriv ℝ n F (x,y) := by
    rw [iteratedFDerivWithin_comp_add_left,htranslate,hpair,
      iteratedFDerivWithin_of_isOpen n hΩ hxy]
  rw [hfun,iteratedFDerivWithin_of_isOpen n hW hxW,hjoint] at hcomp
  exact hcomp

theorem norm_partialSecondJet_le_joint (n : ℕ) (F : R3 × R3 → ℝ)
    (Ω : Set (R3 × R3)) (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ ∞ F Ω)
    (x y : R3) (hxy : (x,y) ∈ Ω) :
    ‖partialSecondJet n F (x,y)‖ ≤ ‖iteratedFDeriv ℝ n F (x,y)‖ := by
  rw [partialSecondJet_eq n F Ω hΩ hF x y hxy]
  exact (iteratedFDeriv ℝ n F (x,y)).norm_compContinuous_linearIsometry_le
    (fun _ => LinearIsometry.inr ℝ R3 R3)

theorem continuousOn_partialSecondJet (n : ℕ) (F : R3 × R3 → ℝ)
    (Ω : Set (R3 × R3)) (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ ∞ F Ω) :
    ContinuousOn (partialSecondJet n F) Ω := by
  have hj : ContinuousOn (iteratedFDeriv ℝ n F) Ω :=
    ContinuousOn.continuousOn_iteratedFDeriv hF hΩ (by simp)
  have hc := (ContinuousMultilinearMap.continuous_precomp
    (fun _ : Fin n => (LinearIsometry.inr ℝ R3 R3).toContinuousLinearMap)).comp_continuousOn hj
  apply hc.congr
  intro p hp
  exact partialSecondJet_eq n F Ω hΩ hF p.1 p.2 hp

/-- One bound is chosen before both points on the compact product room. -/
theorem exists_bound_partialSecondJet (n : ℕ) (F : R3 × R3 → ℝ)
    (Ω : Set (R3 × R3)) (hΩ : IsOpen Ω) (hF : ContDiffOn ℝ ∞ F Ω)
    (K J : Set R3) (hK : IsCompact K) (hJ : IsCompact J) (hKJ : K ×ˢ J ⊆ Ω) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K, ∀ y ∈ J, ‖partialSecondJet n F (x,y)‖ ≤ B := by
  obtain ⟨B,hB⟩ := (hK.prod hJ).exists_bound_of_continuousOn
    ((continuousOn_partialSecondJet n F Ω hΩ hF).mono hKJ)
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro x hx y hy
  exact (hB (x,y) ⟨hx,hy⟩).trans (le_max_left _ _)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
