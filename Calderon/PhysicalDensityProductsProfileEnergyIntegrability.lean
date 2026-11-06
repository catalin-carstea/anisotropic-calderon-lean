import Calderon.PhysicalDensityProductsConcreteSectionsModular
import Calderon.ActualFiniteHarmonicModelHorizontalProfileComparison
import Calderon.PhysicalDensityProductsFiniteCoreProjection
import Calderon.PhysicalDensityProductsConcreteWeightedSums
import Calderon.PhysicalDensityProductsPredicateTransport
import Calderon.PhysicalDensityProductsOperatorSmoothness
import Calderon.SupportedOperatorSection
import Calderon.PhysicalDensityProductsProfileOpenRoom
import Calderon.PhysicalDensityProductsFiniteCorePairing
import Calderon.PhysicalDensityProductsNegativeGraph
import Calderon.SphereSobolevHalfToL2
import Calderon.WeightedIntegralCongruence
import Calderon.SupportedOperatorSectionsOfPairing
import Calderon.PhysicalDensityProductsWeightedSumsSmoothness
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Exact original reference-radius regularity and complete physical profile-energy
integrability. No comparison-only energy or new premise is used. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff Topology BigOperators

namespace OAI.AnisotropicCalderon.PhysicalDensityProductsProfileEnergyIntegrability

open SphereHarmonic SpectralWeightedGraph ActualFiniteHarmonicCore
  ActualFiniteHarmonicModel ConformalDepth RadiusProfile
  ReferenceWeightedApproximation ReferenceDensityBounds WeightedBaseSpectral
  SectionFiveErrorForms

theorem contDiff_referenceRadius (δ A : ℝ) (p : ℕ) (L : ℝ) :
    ContDiff ℝ ∞ (referenceRadius δ A p L) := by
  have hlog : ContDiff ℝ ∞
      (fun y : R3 => Real.log (1 + Real.exp (referenceDepth L y / δ))) := by
    apply (contDiff_const.add ((contDiff_referenceDepth L).div_const δ).exp).log
    intro y
    exact ne_of_gt (by positivity)
  unfold referenceRadius softplus
  with_unfolding_all exact
    contDiff_const.mul ((contDiff_const.mul hlog).pow p)

theorem referenceRadius_smooth_pos (δ A : ℝ) (p : ℕ) (L : ℝ)
    (hδ : 0 < δ) (hA : 0 < A) :
    ContDiff ℝ ∞ (referenceRadius δ A p L) ∧
      ∀ y : R3, 0 < referenceRadius δ A p L y := by
  exact ⟨contDiff_referenceRadius δ A p L,
    fun y => referenceRadius_pos δ A p L y hδ hA⟩

variable (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)

private theorem continuous_core_norm_sq (U : smoothCompactFiniteSphereCore hO hD) :
    Continuous (fun y : R3 => ‖U.val y‖ ^ 2) :=
  U.property.1.continuous.norm.pow 2

private theorem hasCompactSupport_core_norm_sq
    (U : smoothCompactFiniteSphereCore hO hD) :
    HasCompactSupport (fun y : R3 => ‖U.val y‖ ^ 2) := by
  have hs := U.property.2.1.comp_left
    (g := fun v : SphereL2 => ‖v‖ ^ 2) (by simp)
  change HasCompactSupport (fun y : R3 => ‖U.val y‖ ^ 2) at hs
  exact hs

theorem continuous_hasCompactSupport_finiteCoreReferenceProfileEnergy
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L q : ℝ)
    (b : R3 → ℝ) (hb : Continuous b) (hb0 : ∀ y, b y ≠ 0)
    (F : smoothCompactFiniteSphereCore hO hD) :
    Continuous (fun y : R3 =>
      finiteCoreReferenceProfileEnergy hO hD g hg L q (b y) F y) ∧
    HasCompactSupport (fun y : R3 =>
      finiteCoreReferenceProfileEnergy hO hD g hg L q (b y) F y) := by
  let H : Fin 3 → smoothCompactFiniteSphereCore hO hD :=
    fun a => coreReferenceHorizontal hO hD g hg L q a F
  let W1 : smoothCompactFiniteSphereCore hO hD :=
    coreWeightOperator hO hD (besselWeight 1) F
  let WH : Fin 3 → smoothCompactFiniteSphereCore hO hD :=
    fun a => coreWeightOperator hO hD (besselWeight (1/2 : ℝ)) (H a)
  let W3 : smoothCompactFiniteSphereCore hO hD :=
    coreWeightOperator hO hD (besselWeight (3/2 : ℝ)) F
  have hcH : Continuous (fun y : R3 => ∑ a : Fin 3, ‖(H a).val y‖ ^ 2) :=
    continuous_finsetSum Finset.univ
      (fun a _ => continuous_core_norm_sq hO hD (H a))
  have hcWH : Continuous (fun y : R3 => ∑ a : Fin 3, ‖(WH a).val y‖ ^ 2) :=
    continuous_finsetSum Finset.univ
      (fun a _ => continuous_core_norm_sq hO hD (WH a))
  have hsH : HasCompactSupport (fun y : R3 => ∑ a : Fin 3, ‖(H a).val y‖ ^ 2) := by
    have hs := HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun a : Fin 3 => fun y : R3 => ‖(H a).val y‖ ^ 2)
      (fun a _ => hasCompactSupport_core_norm_sq hO hD (H a))
    have heq : (∑ a : Fin 3, fun y : R3 => ‖(H a).val y‖ ^ 2) =
        (fun y : R3 => ∑ a : Fin 3, ‖(H a).val y‖ ^ 2) := by
      funext y
      simp only [Finset.sum_apply]
    rw [heq] at hs
    exact hs
  have hsWH : HasCompactSupport (fun y : R3 => ∑ a : Fin 3, ‖(WH a).val y‖ ^ 2) := by
    have hs := HasCompactSupport.finset_sum (s := Finset.univ)
      (f := fun a : Fin 3 => fun y : R3 => ‖(WH a).val y‖ ^ 2)
      (fun a _ => hasCompactSupport_core_norm_sq hO hD (WH a))
    have heq : (∑ a : Fin 3, fun y : R3 => ‖(WH a).val y‖ ^ 2) =
        (fun y : R3 => ∑ a : Fin 3, ‖(WH a).val y‖ ^ 2) := by
      funext y
      simp only [Finset.sum_apply]
    rw [heq] at hs
    exact hs
  have hc1 : Continuous (fun y : R3 => b y ^ 2 * ‖W1.val y‖ ^ 2) :=
    (hb.pow 2).mul (continuous_core_norm_sq hO hD W1)
  have hcHalf : Continuous
      (fun y : R3 => (b y)⁻¹ * ∑ a : Fin 3, ‖(WH a).val y‖ ^ 2) :=
    (hb.inv₀ hb0).mul hcWH
  have hc3 : Continuous (fun y : R3 => b y * ‖W3.val y‖ ^ 2) :=
    hb.mul (continuous_core_norm_sq hO hD W3)
  have hs1 : HasCompactSupport (fun y : R3 => b y ^ 2 * ‖W1.val y‖ ^ 2) := by
    exact (hasCompactSupport_core_norm_sq hO hD W1).mul_left
  have hsHalf : HasCompactSupport
      (fun y : R3 => (b y)⁻¹ * ∑ a : Fin 3, ‖(WH a).val y‖ ^ 2) := by
    exact hsWH.mul_left
  have hs3 : HasCompactSupport (fun y : R3 => b y * ‖W3.val y‖ ^ 2) := by
    exact (hasCompactSupport_core_norm_sq hO hD W3).mul_left
  let E : R3 → ℝ :=
    (((fun y : R3 => ∑ a : Fin 3, ‖(H a).val y‖ ^ 2) +
      (fun y : R3 => b y ^ 2 * ‖W1.val y‖ ^ 2)) +
      (fun y : R3 => (b y)⁻¹ * ∑ a : Fin 3, ‖(WH a).val y‖ ^ 2)) +
      (fun y : R3 => b y * ‖W3.val y‖ ^ 2)
  have hcE : Continuous E := ((hcH.add hc1).add hcHalf).add hc3
  have hsE : HasCompactSupport E := ((hsH.add hs1).add hsHalf).add hs3
  have heq : E = (fun y : R3 =>
      finiteCoreReferenceProfileEnergy hO hD g hg L q (b y) F y) := by
    funext y
    rfl
  rw [heq] at hcE hsE
  exact ⟨hcE, hsE⟩

theorem continuous_hasCompactSupport_referenceProfileEnergyIntegrand
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q δ A : ℝ) (p : ℕ) (hL : 0 < L) (hδ : 0 < δ) (hA : 0 < A)
    (hp : 1 ≤ p) (F : smoothCompactFiniteSphereCore hO hD) :
    Continuous (fun y : R3 => referenceDensityFamily g L (q,y) *
      finiteCoreReferenceProfileEnergy hO hD g hg L q
        (actualReferenceBeta g L q δ A p y) F y) ∧
    HasCompactSupport (fun y : R3 => referenceDensityFamily g L (q,y) *
      finiteCoreReferenceProfileEnergy hO hD g hg L q
        (actualReferenceBeta g L q δ A p y) F y) := by
  have hb : Continuous (actualReferenceBeta g L q δ A p) :=
    continuous_actualReferenceBeta g hg L q δ A p hL hδ hA
  have hb0 : ∀ y : R3, actualReferenceBeta g L q δ A p y ≠ 0 :=
    fun y => ne_of_gt (actualReferenceBeta_pos g hg L q δ A p hL hδ hA hp y)
  obtain ⟨hcE, hsE⟩ :=
    continuous_hasCompactSupport_finiteCoreReferenceProfileEnergy hO hD
      g hg L q (actualReferenceBeta g L q δ A p) hb hb0 F
  exact ⟨(continuous_referenceBaseDensity g hg L q).mul hcE, hsE.mul_left⟩

theorem integrable_referenceProfileEnergyIntegrand
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q δ A : ℝ) (p : ℕ) (hL : 0 < L) (hδ : 0 < δ) (hA : 0 < A)
    (hp : 1 ≤ p) (F : smoothCompactFiniteSphereCore hO hD) :
    Integrable (fun y : R3 => referenceDensityFamily g L (q,y) *
      finiteCoreReferenceProfileEnergy hO hD g hg L q
        (actualReferenceBeta g L q δ A p y) F y) (volume : Measure R3) := by
  obtain ⟨hc, hs⟩ := continuous_hasCompactSupport_referenceProfileEnergyIntegrand
    hO hD g hg L q δ A p hL hδ hA hp F
  exact hc.integrable_of_hasCompactSupport hs

theorem integrable_const_mul_referenceProfileEnergyIntegrand
    (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L q δ A : ℝ) (p : ℕ) (hL : 0 < L) (hδ : 0 < δ) (hA : 0 < A)
    (hp : 1 ≤ p) (F : smoothCompactFiniteSphereCore hO hD) (c : ℝ) :
    Integrable (fun y : R3 => c * (referenceDensityFamily g L (q,y) *
      finiteCoreReferenceProfileEnergy hO hD g hg L q
        (actualReferenceBeta g L q δ A p y) F y)) (volume : Measure R3) := by
  obtain ⟨hc, hs⟩ := continuous_hasCompactSupport_referenceProfileEnergyIntegrand
    hO hD g hg L q δ A p hL hδ hA hp F
  exact (continuous_const.mul hc).integrable_of_hasCompactSupport hs.mul_left

end OAI.AnisotropicCalderon.PhysicalDensityProductsProfileEnergyIntegrability
