import Calderon.RadiusTwoSmoothSourceClassicalWeakEquation
import Calderon.LocalSmoothFluxInhomogeneousSource
import Calderon.MetricHessianDivergence
import Calderon.MetricSmooth

/-! Full EXPANSION.json precedes literal source-PDE coordinate assembly. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory Set Filter Metric TopologicalSpace Matrix
open scoped ENNReal ContDiff Gradient Distributions InnerProductSpace Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ExteriorSource
open EnergyBridge MetricVolume DirichletFamily DirichletFamily.DriftBootstrap
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local irreducible] radiusTwoSourceSolution

lemma principalFlux_gradient_pairing_eq_coordinate_sum
    (A : Matrix (Fin 3) (Fin 3) ℝ) (phi : SmoothData) (G : R3 → ℝ) (x : R3) :
    TauCeti.PDE.matrixBilinearForm A (gradient phi.1 x) (gradient G x) =
      ∑ i : Fin 3, lineDeriv ℝ phi.1 x (coordinateVector i) *
        (∑ j : Fin 3, A i j * fderiv ℝ G x (coordinateVector j)) := by
  rw [TauCeti.PDE.matrixBilinearForm_apply]
  change (∑ i : Fin 3, (gradient phi.1 x) i *
    (∑ j : Fin 3, A i j * (gradient G x) j)) = _
  simp_rw [lineDeriv_smoothData_coordinate_eq_gradient phi,gradient_coordinate]

lemma exists_radiusTwoSmoothSource_classical_divergence_innerBall
    (hreg : FixedDirichletRegularity) (hcalc : FixedSobolevCalculus)
    (g : MatrixField) (hg : IsAdmissibleMetric g) (H : SmoothData)
    (a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    ∃ G : R3 → ℝ, Continuous G ∧ ContDiffOn ℝ ∞ G (ball (0 : R3) (2*a)) ∧
      ((TauCeti.W1p.value (radiusTwoSourceSolution g hg (smoothRadiusTwoForcing H) : RadiusTwoH1) : R3 → ℝ)
        =ᵐ[(volume : Measure R3).restrict (ball (0 : R3) (2*a))] G) ∧
      ∀ x ∈ ball (0 : R3) (2*a),
        -(∑ i : Fin 3, fderiv ℝ
          (fun z : R3 => ∑ j : Fin 3, principalCoefficient g z i j *
            fderiv ℝ G z (coordinateVector j)) x (coordinateVector i)) = H.1 x := by
  obtain ⟨G,hG,hSmooth,hValue,hWeak⟩ :=
    exists_radiusTwoSmoothSource_classical_weakEquation_innerBall hreg hcalc g hg H a ha ha1
  let Omega : Opens R3 := ⟨ball (0 : R3) (2*a),isOpen_ball⟩
  let J : Fin 3 → R3 → ℝ := fun i z => ∑ j : Fin 3,
    principalCoefficient g z i j * fderiv ℝ G z (coordinateVector j)
  have hDG : ContDiffOn ℝ ∞ (fderiv ℝ G) (Omega : Set R3) :=
    hSmooth.fderiv_of_isOpen isOpen_ball (by simp)
  have hJ (i : Fin 3) : ContDiffOn ℝ ∞ (J i) (Omega : Set R3) :=
    ContDiffOn.sum (fun j _ => (contDiff_principalCoefficient_entry g hg i j).contDiffOn.mul
      (hDG.clm_apply contDiffOn_const))
  have hFluxWeak : ∀ phi : SmoothData, HasCompactSupport phi.1 →
      tsupport phi.1 ⊆ (Omega : Set R3) →
      (∫ x : R3, (∑ i : Fin 3, lineDeriv ℝ phi.1 x (coordinateVector i) * J i x)
        ∂(volume : Measure R3)) =
        ∫ x : R3, H.1 x * phi.1 x ∂(volume : Measure R3) := by
    intro phi hCompact hSupport
    have hPair :
        (∫ x : R3, (∑ i : Fin 3, lineDeriv ℝ phi.1 x (coordinateVector i) * J i x)
          ∂(volume : Measure R3)) =
        ∫ x : R3, TauCeti.PDE.matrixBilinearForm (principalCoefficient g x)
          (gradient phi.1 x) (gradient G x) ∂(volume : Measure R3) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x =>
        (principalFlux_gradient_pairing_eq_coordinate_sum (principalCoefficient g x) phi G x).symm)
    exact hPair.trans (hWeak phi hCompact hSupport)
  have hDiv := coordinateFluxRows_divergence_eq_neg_of_smooth_source_weakEquation
    Omega J hJ H.1 H.2.contDiffOn hFluxWeak
  refine ⟨G,hG,hSmooth,hValue,?_⟩
  intro x hx
  have hD : (∑ i : Fin 3, fderiv ℝ (J i) x (coordinateVector i)) = -H.1 x := hDiv x hx
  change -(∑ i : Fin 3, fderiv ℝ (J i) x (coordinateVector i)) = H.1 x
  linarith

end OAI.AnisotropicCalderon.ExteriorSource
#print axioms OAI.AnisotropicCalderon.ExteriorSource.principalFlux_gradient_pairing_eq_coordinate_sum
#print axioms OAI.AnisotropicCalderon.ExteriorSource.exists_radiusTwoSmoothSource_classical_divergence_innerBall
