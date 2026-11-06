import Calderon.ActualReferenceWeakEnergyConstruction
import Calderon.NativeSupportedAdjointH2Regularity
import Calderon.ClosedCoefficientJets

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError MetricVolume
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
include hData

def referenceWeightedDriftDivergence (q : (ℝ × (R3 × ℝ)) × R3) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun t => conformalReferenceWeightedFramedDrift g L Φ H w t i)
    q (0,coordinateVector i)

lemma contDiff_referenceWeightedDriftDivergence :
    ContDiff ℝ ∞ (referenceWeightedDriftDivergence g L Φ H w) := by
  apply ContDiff.sum
  intro i hi
  have hc := (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp
    (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1
  exact (hc.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

lemma referenceWeightedDriftDivergence_eq_native (p : ℝ × (R3 × ℝ)) (x : R3) :
    referenceWeightedDriftDivergence g L Φ H w (p,x) =
      nativeSupportedDriftDivergence (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x := by
  apply Finset.sum_congr rfl
  intro i hi
  have hc := (EuclideanSpace.proj i : R3 →L[ℝ] ℝ).contDiff.comp
    (jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).1
  have he := ((hc.differentiable (by simp) (p,x)).hasFDerivAt.comp x
    (hasFDerivAt_prodMk_right p x)).fderiv
  exact (congrArg (fun A : R3 →L[ℝ] ℝ => A (coordinateVector i)) he).symm

lemma referenceWeightedDriftDivergence_zero_outside
    (p : ℝ × (R3 × ℝ)) (x : R3) (hx : x ∉ closedBall (0 : R3) 3) :
    referenceWeightedDriftDivergence g L Φ H w (p,x) = 0 := by
  rw [referenceWeightedDriftDivergence_eq_native g L y0 Φ B ε C ρ H a w hData p x]
  apply Finset.sum_eq_zero
  intro i hi
  have hSupport : tsupport (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y) i) ⊆
      closedBall (0 : R3) 3 :=
    SpatialJetFields.tsupport_spatial_slice_subset
      (fun q => conformalReferenceWeightedFramedDrift g L Φ H w q i)
      (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
      (fun t y hy => by rw [(jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData).2 t y hy]; rfl) p
  have he := fderiv_of_notMem_tsupport ℝ (fun hy => hx (hSupport hy))
  exact congrArg (fun A : R3 →L[ℝ] ℝ => A (coordinateVector i)) he

def referenceAdjointMassFunction (q : (ℝ × (R3 × ℝ)) × R3) : ℝ :=
  -referenceWeightedDriftDivergence g L Φ H w q

lemma contDiff_referenceAdjointMassFunction :
    ContDiff ℝ ∞ (referenceAdjointMassFunction g L Φ H w) :=
  (contDiff_referenceWeightedDriftDivergence g L y0 Φ B ε C ρ H a w hData).neg

lemma referenceAdjointMassFunction_zero_outside
    (p : ℝ × (R3 × ℝ)) (x : R3) (hx : x ∉ closedBall (0 : R3) 3) :
    referenceAdjointMassFunction g L Φ H w (p,x) = 0 := by
  unfold referenceAdjointMassFunction
  rw [referenceWeightedDriftDivergence_zero_outside g L y0 Φ B ε C ρ H a w hData p x hx,neg_zero]

def referenceAdjointMassJetsFamily (p : ℝ × (R3 × ℝ)) : SmoothCoefficientJets 1 :=
  commonSupportCoefficientFamily 1 (referenceAdjointMassFunction g L Φ H w)
    (contDiff_referenceAdjointMassFunction g L y0 Φ B ε C ρ H a w hData)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData) p

lemma coefficientValue_referenceAdjointMassJetsFamily (p : ℝ × (R3 × ℝ)) (x : R3) :
    coefficientValue 1 (referenceAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData p) x =
      -nativeSupportedDriftDivergence (fun y => conformalReferenceWeightedFramedDrift g L Φ H w (p,y)) x := by
  have he := coefficientValue_commonSupportCoefficientFamily 1
    (referenceAdjointMassFunction g L Φ H w)
    (contDiff_referenceAdjointMassFunction g L y0 Φ B ε C ρ H a w hData)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData) p x
  exact he.trans (congrArg (fun t : ℝ => -t)
    (referenceWeightedDriftDivergence_eq_native g L y0 Φ B ε C ρ H a w hData p x))

lemma contDiff_referenceAdjointMassJetFields :
    ContDiff ℝ ∞ (fun p => (referenceAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData p).val) :=
  contDiff_commonSupportCoefficientFamily_val 1 (referenceAdjointMassFunction g L Φ H w)
    (contDiff_referenceAdjointMassFunction g L y0 Φ B ε C ρ H a w hData)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData)

lemma contDiff_referenceAdjointMassClosedJets :
    ContDiff ℝ ∞ (fun p => smoothCoefficientClosureInclusionL 1
      (referenceAdjointMassJetsFamily g L y0 Φ B ε C ρ H a w hData p)) :=
  contDiff_commonSupportClosedCoefficientFamily 1 (referenceAdjointMassFunction g L Φ H w)
    (contDiff_referenceAdjointMassFunction g L y0 Φ B ε C ρ H a w hData)
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (referenceAdjointMassFunction_zero_outside g L y0 Φ B ε C ρ H a w hData)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeightedDriftDivergence

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceWeightedDriftDivergence

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeightedDriftDivergence_eq_native

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceWeightedDriftDivergence_zero_outside

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointMassFunction

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceAdjointMassFunction

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointMassFunction_zero_outside

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.referenceAdjointMassJetsFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.coefficientValue_referenceAdjointMassJetsFamily

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceAdjointMassJetFields

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceAdjointMassClosedJets
