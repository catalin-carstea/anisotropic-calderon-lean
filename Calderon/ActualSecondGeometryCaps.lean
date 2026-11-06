import Calderon.ActualSAdjointSecondNegative
import Calderon.ReferenceFrameUniformComparison
import Calderon.ActualHigherSCoordinateWeightBounds

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSecondGeometryCaps
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualHigherSFormation ActualHigherSSecondAdjoint
  ReferenceDensityBounds ConformalDepth SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore ActualNormalizedSecondMetricDrift ActualHorizontalNormBridge
  ReferenceFrameUniformComparison

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def highSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
@[instance_reducible] private def lowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def lowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] highNormed highSpace lowNormed lowSpace

private lemma contDiff_frame_component (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (i k : Fin 3) :
    ContDiff ℝ ∞ (fun z : ℝ × R3 => referenceMetricGramFrame g L z i k) :=
  (EuclideanSpace.proj (𝕜 := ℝ) k).contDiff.comp
    (contDiff_referenceMetricGramFrame g hg L i)

private lemma contDiff_highAngular_joint (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun z : ℝ × R3 => referenceHighHorizontalAngularL g L z.1 z.2 i) := by
  change ContDiff ℝ ∞ (fun z : ℝ × R3 => (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
    referenceGramConnectionCoefficient g L i a b z • sphereSobolevRotationL (3/2 : ℝ) a b)
  apply ContDiff.const_smul
  exact ContDiff.sum (fun a _ => ContDiff.sum (fun b _ =>
    (contDiff_referenceGramConnectionCoefficient g hg L i a b).smul contDiff_const))

private lemma contDiff_lowAngular_joint (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun z : ℝ × R3 => referenceLowerHorizontalAngularL g L z.1 z.2 i) := by
  change ContDiff ℝ ∞ (fun z : ℝ × R3 => (1/2 : ℝ) • ∑ a : Fin 3, ∑ b : Fin 3,
    referenceGramConnectionCoefficient g L i a b z • sphereSobolevRotationL (1/2 : ℝ) a b)
  apply ContDiff.const_smul
  exact ContDiff.sum (fun a _ => ContDiff.sum (fun b _ =>
    (contDiff_referenceGramConnectionCoefficient g hg L i a b).smul contDiff_const))

private lemma contDiff_weightedDivergence_joint (g : MatrixField) (hg : IsAdmissibleMetric g)
    (L : ℝ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun z : ℝ × R3 => referenceWeightedFrameDivergence g L z.1 i z.2) := by
  change ContDiff ℝ ∞ (fun z : ℝ × R3 => ∑ k : Fin 3,
    familyDirectionalDeriv k (fun t : ℝ × R3 =>
      referenceDensityFamily g L t * referenceMetricGramFrame g L t i k) z)
  exact ContDiff.sum (fun k _ => contDiff_familyDirectionalDeriv k _
    ((contDiff_referenceDensityFamily g hg L).mul (contDiff_frame_component g hg L i k)))

private inductive GeometryIndex where
  | density | densityInv
  | frame (i : Fin 3)
  | frameEntry (i k : Fin 3)
  | connection (i j k : Fin 3)
  | highConnection (i : Fin 3)
  | lowConnection (i : Fin 3)
  | principal (i j : Fin 3)
  | principalDerivative (i j : Fin 3)
  | drift (i : Fin 3)
  | weightedDivergence (i : Fin 3)
  deriving Fintype, DecidableEq

private def geometryQuantity (g g2 : MatrixField) (L : ℝ) : GeometryIndex → (ℝ × R3) → ℝ
  | .density, z => |referenceDensityFamily g L z|
  | .densityInv, z => |(referenceDensityFamily g L z)⁻¹|
  | .frame i, z => ‖referenceMetricGramFrame g L z i‖
  | .frameEntry i k, z => |referenceMetricGramFrame g L z i k|
  | .connection i j k, z => |referenceGramConnectionCoefficient g L i k j z|
  | .highConnection i, z => ‖referenceHighHorizontalAngularL g L z.1 z.2 i‖
  | .lowConnection i, z => ‖referenceLowerHorizontalAngularL g L z.1 z.2 i‖
  | .principal i j, z => |referenceDensityPrincipalFrameCoefficient g g2 L z.1 z.2 i j|
  | .principalDerivative i j, z =>
      ‖fderiv ℝ (fun t : ℝ × R3 => referenceDensityPrincipalFrameCoefficient g g2 L t.1 t.2 i j) z‖
  | .drift i, z => |normalizedSecondDriftFrameJoint g g2 L i z|
  | .weightedDivergence i, z => |referenceWeightedFrameDivergence g L z.1 i z.2|

private lemma continuous_geometryQuantity (g g2 : MatrixField)
    (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2) (L : ℝ) (i : GeometryIndex) :
    Continuous (geometryQuantity g g2 L i) := by
  cases i with
  | density => exact (contDiff_referenceDensityFamily g hg L).continuous.abs
  | densityInv => exact (contDiff_referenceDensityFamily_inv g hg L).continuous.abs
  | frame i => exact (contDiff_referenceMetricGramFrame g hg L i).continuous.norm
  | frameEntry i k => exact (contDiff_frame_component g hg L i k).continuous.abs
  | connection i j k => exact (contDiff_referenceGramConnectionCoefficient g hg L i k j).continuous.abs
  | highConnection i => exact (contDiff_highAngular_joint g hg L i).continuous.norm
  | lowConnection i => exact (contDiff_lowAngular_joint g hg L i).continuous.norm
  | principal i j =>
      exact (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).continuous.abs
  | principalDerivative i j =>
      exact ((contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).fderiv_right
        (m := ∞) (by simp)).continuous.norm
  | drift i => exact (contDiff_normalizedSecondDriftFrameJoint g g2 hg hg2 L i).continuous.abs
  | weightedDivergence i => exact (contDiff_weightedDivergence_joint g hg L i).continuous.abs

/-- Actual geometry caps at one original dilation/base point. -/
structure GeometryCaps (g g2 : MatrixField) (L q : ℝ) (x : R3) (M : ℝ) : Prop where
  one_le : 1 ≤ M
  density : |referenceDensityFamily g L (q,x)| ≤ M
  density_inv : |(referenceDensityFamily g L (q,x))⁻¹| ≤ M
  frame : ∀ i : Fin 3, ‖referenceMetricGramFrame g L (q,x) i‖ ≤ M
  frame_entry : ∀ i k : Fin 3, |referenceMetricGramFrame g L (q,x) i k| ≤ M
  connection : ∀ i j k : Fin 3, |referenceFrameConnectionCoefficient g L q x
    (referenceMetricGramFrame g L (q,x) i) k j| ≤ M
  high_connection : ∀ i : Fin 3, ‖referenceHighHorizontalAngularL g L q x i‖ ≤ M
  low_connection : ∀ i : Fin 3, ‖referenceLowerHorizontalAngularL g L q x i‖ ≤ M
  principal : ∀ i j : Fin 3, |referenceDensityPrincipalFrameCoefficient g g2 L q x i j| ≤ M
  principal_derivative : ∀ i j : Fin 3,
    ‖fderiv ℝ (fun t : ℝ × R3 => referenceDensityPrincipalFrameCoefficient g g2 L t.1 t.2 i j) (q,x)‖ ≤ M
  drift : ∀ i : Fin 3, |normalizedSecondDriftFrameJoint g g2 L i (q,x)| ≤ M
  weighted_divergence : ∀ i : Fin 3, |referenceWeightedFrameDivergence g L q i x| ≤ M

/-- M is produced before q, x, every profile and every input, for fixed g2. -/
theorem exists_geometryCaps (g g2 : MatrixField) (hg : IsAdmissibleMetric g)
    (hg2 : IsAdmissibleMetric g2) (L : ℝ) (K : Set R3) (hK : IsCompact K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, GeometryCaps g g2 L q x M := by
  obtain ⟨M,hM,hcap⟩ := exists_uniform_bound_finite_family (geometryQuantity g g2 L)
    (continuous_geometryQuantity g g2 hg hg2 L) K hK
  have hc (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) (x : R3) (hx : x ∈ K) (i : GeometryIndex) :
      geometryQuantity g g2 L i (q,x) ≤ M :=
    (le_abs_self _).trans (hcap q hq x hx i)
  refine ⟨M,hM,?_⟩
  intro q hq x hx
  exact {
    one_le := hM
    density := hc q hq x hx .density
    density_inv := hc q hq x hx .densityInv
    frame := fun i => hc q hq x hx (.frame i)
    frame_entry := fun i k => hc q hq x hx (.frameEntry i k)
    connection := fun i j k => hc q hq x hx (.connection i j k)
    high_connection := fun i => hc q hq x hx (.highConnection i)
    low_connection := fun i => hc q hq x hx (.lowConnection i)
    principal := fun i j => hc q hq x hx (.principal i j)
    principal_derivative := fun i j => hc q hq x hx (.principalDerivative i j)
    drift := fun i => hc q hq x hx (.drift i)
    weighted_divergence := fun i => hc q hq x hx (.weightedDivergence i)
  }

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualSecondGeometryCaps
