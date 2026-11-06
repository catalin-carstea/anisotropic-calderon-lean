import Calderon.NativeBoundaryCoefficientFamilies
import Calderon.NativeBoundaryNormalMultiplierInverse
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ContDiff Gradient ENNReal Matrix.Norms.Elementwise Topology
namespace OAI.AnisotropicCalderon.NativeNormalCoefficientInverseFamily
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
  NativeCoefficientBoundaryMultiplier NativeBoundaryCoefficientFamilies NativeBoundaryNormalMultiplierInverse
variable {H : Type} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

/-! Expanded before source in EXPANSION-native-parameterized-boundary-multiplier-topology-v001.json. -/

theorem exists_compact_contDiffOn_norm_bound
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : E → V) (Q : Set E) (hQ : IsCompact Q) (hf : ContDiffOn ℝ ∞ f Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Q, ‖f p‖ ≤ C := by
  obtain ⟨C,hC⟩ := hQ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨max 0 C,le_max_left _ _,fun p hp => (hC p hp).trans (le_max_right _ _)⟩

lemma nativeNegativeHalf_normalCoefficientFamily_isInvertible
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → a (p,x) = 0)
    (p : H) (lam Lam : ℝ)
    (hUE : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun x => a (p,x)) lam Lam) :
    (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
      (normalCoefficientJetsFamily a ha K hK hz p)).IsInvertible := by
  let F : SmoothCoefficientMatrix 2 := commonSupportMatrixFamily 2 a ha K hK hz p
  have hfield : coefficientMatrixField 2 F = (fun x => a (p,x)) :=
    coefficientMatrixField_commonSupportMatrixFamily 2 a ha K hK hz p
  have hUEF : TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (coefficientMatrixField 2 F) lam Lam := by
    rw [hfield]
    exact hUE
  obtain ⟨M,hM,hm,hgm⟩ := exists_smooth_ball_multiplier_bound (boundaryNormalCoefficientData F)
  have hData : coefficientSmoothData (normalCoefficientJetsFamily a ha K hK hz p) =
      boundaryNormalCoefficientData F := coefficientSmoothData_normalCoefficientJetsFamily a ha K hK hz p
  have hmData : ∀ x ∈ (ballOpens : Set R3),
      |(coefficientSmoothData (normalCoefficientJetsFamily a ha K hK hz p)).1 x| ≤ M := by
    rw [hData]
    exact hm
  have hgData : ∀ x ∈ (ballOpens : Set R3),
      ‖gradient (coefficientSmoothData (normalCoefficientJetsFamily a ha K hK hz p)).1 x‖ ≤ M := by
    rw [hData]
    exact hgm
  have hEq := nativeNegativeHalfCoefficientMulL_eq_smoothMulL hcalc hF hO hD τ0
    (normalCoefficientJetsFamily a ha K hK hz p) hM hmData hgData
  simp only [hData] at hEq
  rw [hEq]
  exact nativeNegativeHalfNormalCoefficientMulL_isInvertible hF hO hD τ0 F lam Lam hUEF hM hm hgm

lemma contDiffOn_nativeNegativeHalf_normalCoefficientFamily_inverse
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → a (p,x) = 0)
    (Q : Set H) (lam Lam : ℝ)
    (hUE : ∀ p ∈ Q, TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun x => a (p,x)) lam Lam) :
    ContDiffOn ℝ ∞ (fun p : H =>
      (nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
        (normalCoefficientJetsFamily a ha K hK hz p)).inverse) Q := by
  intro p hp
  have hInv := nativeNegativeHalf_normalCoefficientFamily_isInvertible hcalc hF hO hD τ0
    a ha K hK hz p lam Lam (hUE p hp)
  exact hInv.contDiffAt_map_inverse.comp_contDiffWithinAt p
    (contDiff_negativeHalf_normalCoefficientFamily hcalc hF hO hD τ0 a ha K hK hz).contDiffWithinAt

lemma exists_uniform_nativeNormalCoefficientInverse_bound
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (a : H × R3 → Matrix (Fin 3) (Fin 3) ℝ) (ha : ContDiff ℝ ∞ a)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ p x, x ∉ K → a (p,x) = 0)
    (Q : Set H) (hQ : IsCompact Q) (lam Lam : ℝ)
    (hUE : ∀ p ∈ Q, TauCeti.PDE.UniformlyEllipticOn (ballOpens : Set R3) (fun x => a (p,x)) lam Lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Q,
      ‖(nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
        (normalCoefficientJetsFamily a ha K hK hz p)).inverse‖ ≤ C := by
  exact exists_compact_contDiffOn_norm_bound _ Q hQ
    (contDiffOn_nativeNegativeHalf_normalCoefficientFamily_inverse
      hcalc hF hO hD τ0 a ha K hK hz Q lam Lam hUE)

end OAI.AnisotropicCalderon.NativeNormalCoefficientInverseFamily

#print axioms OAI.AnisotropicCalderon.NativeNormalCoefficientInverseFamily.nativeNegativeHalf_normalCoefficientFamily_isInvertible
#print axioms OAI.AnisotropicCalderon.NativeNormalCoefficientInverseFamily.contDiffOn_nativeNegativeHalf_normalCoefficientFamily_inverse
#print axioms OAI.AnisotropicCalderon.NativeNormalCoefficientInverseFamily.exists_uniform_nativeNormalCoefficientInverse_bound
