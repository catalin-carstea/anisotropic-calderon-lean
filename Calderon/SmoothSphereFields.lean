import Calderon.CompactParameterSmoothness
import Calderon.SphereHarmonicBridge
import Mathlib.Analysis.Calculus.FDeriv.Const

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.SmoothSphereFields
open SphereHarmonic CompactParameterSmoothness

def unitSphereInclusion : C(UnitSphere,R3) := ⟨Subtype.val,continuous_subtype_val⟩

def ambientSphereSection (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    R3 → C(UnitSphere,ℝ) := compactPullback G hG.continuous unitSphereInclusion

def ambientSphereL2 (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) : R3 → SphereL2 :=
  fun x => ContinuousMap.toLp 2 sphereProbability ℝ (ambientSphereSection G hG x)

lemma contDiff_ambientSphereSection (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientSphereSection G hG) :=
  contDiff_infty_compactPullback G hG unitSphereInclusion

lemma contDiff_ambientSphereL2 (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (ambientSphereL2 G hG) := by
  change ContDiff ℝ ∞
    ((ContinuousMap.toLp 2 sphereProbability ℝ : C(UnitSphere,ℝ) →L[ℝ] SphereL2) ∘
      ambientSphereSection G hG)
  exact (ContinuousMap.toLp 2 sphereProbability ℝ : C(UnitSphere,ℝ) →L[ℝ] SphereL2).contDiff.comp
    (contDiff_ambientSphereSection G hG)

lemma ambientSphereL2_ae (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    ambientSphereL2 G hG x =ᵐ[sphereProbability] (fun theta : UnitSphere => G (x,theta.val)) :=
  ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) sphereProbability
    (ambientSphereSection G hG x)

def ambientBasePartialSphere (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    C(UnitSphere,R3 →L[ℝ] ℝ) :=
  compactPullback (basePartial G)
    (contDiff_basePartial 0 G (hG.of_le (by simp))).continuous unitSphereInclusion x

lemma hasFDerivAt_ambientSphereSection (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    HasFDerivAt (ambientSphereSection G hG)
      (transposeContinuousFamily (ambientBasePartialSphere G hG x)) x := by
  apply hasFDerivAt_of_uniform_slice_derivative
    (ambientSphereSection G hG) (ambientBasePartialSphere G hG) x
  · exact (continuous_compactPullback (basePartial G)
      (contDiff_basePartial 0 G (hG.of_le (by simp))).continuous unitSphereInclusion).continuousAt
  · intro y theta
    exact hasFDerivAt_base_slice G (hG.differentiable (by simp)) y theta.val

lemma fderiv_ambientSphereL2 (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3) :
    fderiv ℝ (ambientSphereL2 G hG) x =
      (ContinuousMap.toLp 2 sphereProbability ℝ).comp
        (transposeContinuousFamily (ambientBasePartialSphere G hG x)) := by
  change fderiv ℝ
    ((ContinuousMap.toLp 2 sphereProbability ℝ : C(UnitSphere,ℝ) →L[ℝ] SphereL2) ∘
      ambientSphereSection G hG) x = _
  exact ((ContinuousMap.toLp 2 sphereProbability ℝ : C(UnitSphere,ℝ) →L[ℝ] SphereL2).hasFDerivAt.comp x
    (hasFDerivAt_ambientSphereSection G hG x)).fderiv

lemma fderiv_ambientSphereL2_ae (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x X : R3) :
    fderiv ℝ (ambientSphereL2 G hG) x X =ᵐ[sphereProbability]
      (fun theta : UnitSphere => fderiv ℝ G (x,theta.val) (X,0)) := by
  rw [fderiv_ambientSphereL2,ContinuousLinearMap.comp_apply]
  exact ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) sphereProbability
    (transposeContinuousFamily (ambientBasePartialSphere G hG x) X)

lemma ambientSphereSection_eq_zero (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3)
    (hz : ∀ theta : UnitSphere, G (x,theta.val)=0) : ambientSphereSection G hG x = 0 := by
  ext theta
  exact hz theta

lemma ambientSphereL2_eq_zero (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G) (x : R3)
    (hz : ∀ theta : UnitSphere, G (x,theta.val)=0) : ambientSphereL2 G hG x = 0 := by
  change ContinuousMap.toLp 2 sphereProbability ℝ (ambientSphereSection G hG x)=0
  rw [ambientSphereSection_eq_zero G hG x hz,map_zero]

lemma hasCompactSupport_ambientSphereSection (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (ambientSphereSection G hG) :=
  HasCompactSupport.intro hK (fun x hx => ambientSphereSection_eq_zero G hG x (hz x hx))

lemma hasCompactSupport_ambientSphereL2 (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) :
    HasCompactSupport (ambientSphereL2 G hG) :=
  HasCompactSupport.intro hK (fun x hx => ambientSphereL2_eq_zero G hG x (hz x hx))

lemma hasCompactSupport_fderiv_ambientSphereL2 (G : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ G)
    (K : Set R3) (hK : IsCompact K)
    (hz : ∀ x ∉ K, ∀ theta : UnitSphere, G (x,theta.val)=0) (X : R3) :
    HasCompactSupport (fun x => fderiv ℝ (ambientSphereL2 G hG) x X) :=
  (hasCompactSupport_ambientSphereL2 G hG K hK hz).fderiv_apply ℝ X

end OAI.AnisotropicCalderon.SmoothSphereFields
